import V185TrunkScan23Chunk0102

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_609667 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 1, 1, 3]
def baseStart_609667 : Nat := 118140960795 + 609667 * 2 ^ 59
def prefixEnd_609667 : Nat := 4983230072969 + 3 ^ 40 * 609667 * 2
def baseEnd_609667 : Nat := 313052210184771408758699

theorem tailTrace_609667 : CollatzResearch.WordTrace tailWord_609667 prefixEnd_609667 313052210184771408758699 := by
  unfold tailWord_609667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236382282288056679067255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14824254854858704452711503 22236382282288056679067255)
  ·
    refine ⟨33354573423432085018600883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22236382282288056679067255 33354573423432085018600883)
    ·
      refine ⟨50031860135148127527901325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33354573423432085018600883 50031860135148127527901325)
      ·
        refine ⟨18761947550680547822962997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50031860135148127527901325 18761947550680547822962997)
        ·
          refine ⟨1758932582876301358402781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18761947550680547822962997 1758932582876301358402781)
          ·
            refine ⟨659599718578613009401043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1758932582876301358402781 659599718578613009401043)
            ·
              refine ⟨989399577867919514101565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659599718578613009401043 989399577867919514101565)
              ·
                refine ⟨371024841700469817788087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989399577867919514101565 371024841700469817788087)
                ·
                  refine ⟨556537262550704726682131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371024841700469817788087 556537262550704726682131)
                  ·
                    refine ⟨834805893826057090023197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556537262550704726682131 834805893826057090023197)
                    ·
                      refine ⟨313052210184771408758699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834805893826057090023197 313052210184771408758699)
                      ·
                        rfl

theorem cell23_609667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_609667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609667 prefixEnd_609667 := by exact prefixLift 609667
  have htrace : WordTrace (prefixWord ++ tailWord_609667) baseStart_609667 baseEnd_609667 := by
    simpa [prefixWord, tailWord_609667, baseEnd_609667] using wordTrace_append hprefix tailTrace_609667
  have hstable : (prefixWord ++ tailWord_609667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609667).length < 2 ^ (prefixWord ++ tailWord_609667).sum := by decide
  have hdescent : baseEnd_609667 < baseStart_609667 := by decide
  rcases family_descends (prefixWord ++ tailWord_609667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609676 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_609676 : Nat := 118140960795 + 609676 * 2 ^ 59
def prefixEnd_609676 : Nat := 4983230072969 + 3 ^ 40 * 609676 * 2
def baseEnd_609676 : Nat := 313056831510661873546157

theorem tailTrace_609676 : CollatzResearch.WordTrace tailWord_609676 prefixEnd_609676 313056831510661873546157 := by
  unfold tailWord_609676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11118355269627725608072441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14824473692836967477429921 11118355269627725608072441)
  ·
    refine ⟨8338766452220794206054331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11118355269627725608072441 8338766452220794206054331)
    ·
      refine ⟨12508149678331191309081497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338766452220794206054331 12508149678331191309081497)
      ·
        refine ⟨9381112258748393481811123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12508149678331191309081497 9381112258748393481811123)
        ·
          refine ⟨14071668388122590222716685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9381112258748393481811123 14071668388122590222716685)
          ·
            refine ⟨5276875645545971333518757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14071668388122590222716685 5276875645545971333518757)
            ·
              refine ⟨989414183539869625034767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5276875645545971333518757 989414183539869625034767)
              ·
                refine ⟨1484121275309804437552151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989414183539869625034767 1484121275309804437552151)
                ·
                  refine ⟨2226181912964706656328227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484121275309804437552151 2226181912964706656328227)
                  ·
                    refine ⟨3339272869447059984492341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226181912964706656328227 3339272869447059984492341)
                    ·
                      refine ⟨313056831510661873546157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3339272869447059984492341 313056831510661873546157)
                      ·
                        rfl

theorem cell23_609676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_609676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609676 prefixEnd_609676 := by exact prefixLift 609676
  have htrace : WordTrace (prefixWord ++ tailWord_609676) baseStart_609676 baseEnd_609676 := by
    simpa [prefixWord, tailWord_609676, baseEnd_609676] using wordTrace_append hprefix tailTrace_609676
  have hstable : (prefixWord ++ tailWord_609676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609676).length < 2 ^ (prefixWord ++ tailWord_609676).sum := by decide
  have hdescent : baseEnd_609676 < baseStart_609676 := by decide
  rcases family_descends (prefixWord ++ tailWord_609676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609684 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_609684 : Nat := 118140960795 + 609684 * 2 ^ 59
def prefixEnd_609684 : Nat := 4983230072969 + 3 ^ 40 * 609684 * 2
def baseEnd_609684 : Nat := 313060939355897842246121

theorem tailTrace_609684 : CollatzResearch.WordTrace tailWord_609684 prefixEnd_609684 313060939355897842246121 := by
  unfold tailWord_609684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11118501161613234291218053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14824668215484312388290737 11118501161613234291218053)
  ·
    refine ⟨2084718967802481429603385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11118501161613234291218053 2084718967802481429603385)
    ·
      refine ⟨1563539225851861072202539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2084718967802481429603385 1563539225851861072202539)
      ·
        refine ⟨2345308838777791608303809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563539225851861072202539 2345308838777791608303809)
        ·
          refine ⟨1758981629083343706227857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345308838777791608303809 1758981629083343706227857)
          ·
            refine ⟨1319236221812507779670893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758981629083343706227857 1319236221812507779670893)
            ·
              refine ⟨494713583179690417376585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319236221812507779670893 494713583179690417376585)
              ·
                refine ⟨371035187384767813032439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494713583179690417376585 371035187384767813032439)
                ·
                  refine ⟨556552781077151719548659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371035187384767813032439 556552781077151719548659)
                  ·
                    refine ⟨834829171615727579322989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556552781077151719548659 834829171615727579322989)
                    ·
                      refine ⟨313060939355897842246121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834829171615727579322989 313060939355897842246121)
                      ·
                        rfl

theorem cell23_609684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_609684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609684 prefixEnd_609684 := by exact prefixLift 609684
  have htrace : WordTrace (prefixWord ++ tailWord_609684) baseStart_609684 baseEnd_609684 := by
    simpa [prefixWord, tailWord_609684, baseEnd_609684] using wordTrace_append hprefix tailTrace_609684
  have hstable : (prefixWord ++ tailWord_609684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609684).length < 2 ^ (prefixWord ++ tailWord_609684).sum := by decide
  have hdescent : baseEnd_609684 < baseStart_609684 := by decide
  rcases family_descends (prefixWord ++ tailWord_609684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609699 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_609699 : Nat := 118140960795 + 609699 * 2 ^ 59
def prefixEnd_609699 : Nat := 4983230072969 + 3 ^ 40 * 609699 * 2
def baseEnd_609699 : Nat := 313068641565715283558551

theorem tailTrace_609699 : CollatzResearch.WordTrace tailWord_609699 prefixEnd_609699 313068641565715283558551 := by
  unfold tailWord_609699
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237549418172126144232151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14825032945448084096154767 22237549418172126144232151)
  ·
    refine ⟨33356324127258189216348227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22237549418172126144232151 33356324127258189216348227)
    ·
      refine ⟨50034486190887283824522341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33356324127258189216348227 50034486190887283824522341)
      ·
        refine ⟨9381466160791365717097939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50034486190887283824522341 9381466160791365717097939)
        ·
          refine ⟨14072199241187048575646909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9381466160791365717097939 14072199241187048575646909)
          ·
            refine ⟨5277074715445143215867591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14072199241187048575646909 5277074715445143215867591)
            ·
              refine ⟨7915612073167714823801387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277074715445143215867591 7915612073167714823801387)
              ·
                refine ⟨11873418109751572235702081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7915612073167714823801387 11873418109751572235702081)
                ·
                  refine ⟨8905063582313679176776561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873418109751572235702081 8905063582313679176776561)
                  ·
                    refine ⟨6678797686735259382582421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8905063582313679176776561 6678797686735259382582421)
                    ·
                      refine ⟨313068641565715283558551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6678797686735259382582421 313068641565715283558551)
                      ·
                        rfl

theorem cell23_609699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_609699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609699 prefixEnd_609699 := by exact prefixLift 609699
  have htrace : WordTrace (prefixWord ++ tailWord_609699) baseStart_609699 baseEnd_609699 := by
    simpa [prefixWord, tailWord_609699, baseEnd_609699] using wordTrace_append hprefix tailTrace_609699
  have hstable : (prefixWord ++ tailWord_609699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609699).length < 2 ^ (prefixWord ++ tailWord_609699).sum := by decide
  have hdescent : baseEnd_609699 < baseStart_609699 := by decide
  rcases family_descends (prefixWord ++ tailWord_609699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609730 : List Nat := [3, 5, 2, 1, 12]
def baseStart_609730 : Nat := 118140960795 + 609730 * 2 ^ 59
def prefixEnd_609730 : Nat := 4983230072969 + 3 ^ 40 * 609730 * 2
def baseEnd_609730 : Nat := 429471274987660716421

theorem tailTrace_609730 : CollatzResearch.WordTrace tailWord_609730 prefixEnd_609730 429471274987660716421 := by
  unfold tailWord_609730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559670020264954609652661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14825786720706545625740429 5559670020264954609652661)
  ·
    refine ⟨521219064399839494654937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5559670020264954609652661 521219064399839494654937)
    ·
      refine ⟨390914298299879620991203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521219064399839494654937 390914298299879620991203)
      ·
        refine ⟨586371447449819431486805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390914298299879620991203 586371447449819431486805)
        ·
          refine ⟨429471274987660716421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 586371447449819431486805 429471274987660716421)
          ·
            rfl

theorem cell23_609730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 12].length) (baseStart_609730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609730 prefixEnd_609730 := by exact prefixLift 609730
  have htrace : WordTrace (prefixWord ++ tailWord_609730) baseStart_609730 baseEnd_609730 := by
    simpa [prefixWord, tailWord_609730, baseEnd_609730] using wordTrace_append hprefix tailTrace_609730
  have hstable : (prefixWord ++ tailWord_609730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609730).length < 2 ^ (prefixWord ++ tailWord_609730).sum := by decide
  have hdescent : baseEnd_609730 < baseStart_609730 := by decide
  rcases family_descends (prefixWord ++ tailWord_609730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609740 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_609740 : Nat := 118140960795 + 609740 * 2 ^ 59
def prefixEnd_609740 : Nat := 4983230072969 + 3 ^ 40 * 609740 * 2
def baseEnd_609740 : Nat := 313089694272549623145863

theorem tailTrace_609740 : CollatzResearch.WordTrace tailWord_609740 prefixEnd_609740 313089694272549623145863 := by
  unfold tailWord_609740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119522405511795073237337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14826029874015726764316449 11119522405511795073237337)
  ·
    refine ⟨8339641804133846304928003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11119522405511795073237337 8339641804133846304928003)
    ·
      refine ⟨12509462706200769457392005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339641804133846304928003 12509462706200769457392005)
      ·
        refine ⟨2345524257412644273261001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12509462706200769457392005 2345524257412644273261001)
        ·
          refine ⟨1759143193059483204945751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345524257412644273261001 1759143193059483204945751)
          ·
            refine ⟨2638714789589224807418627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759143193059483204945751 2638714789589224807418627)
            ·
              refine ⟨3958072184383837211127941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638714789589224807418627 3958072184383837211127941)
              ·
                refine ⟨742138534571969477086489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3958072184383837211127941 742138534571969477086489)
                ·
                  refine ⟨556603900928977107814867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742138534571969477086489 556603900928977107814867)
                  ·
                    refine ⟨834905851393465661722301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556603900928977107814867 834905851393465661722301)
                    ·
                      refine ⟨313089694272549623145863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834905851393465661722301 313089694272549623145863)
                      ·
                        rfl

theorem cell23_609740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_609740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609740 prefixEnd_609740 := by exact prefixLift 609740
  have htrace : WordTrace (prefixWord ++ tailWord_609740) baseStart_609740 baseEnd_609740 := by
    simpa [prefixWord, tailWord_609740, baseEnd_609740] using wordTrace_append hprefix tailTrace_609740
  have hstable : (prefixWord ++ tailWord_609740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609740).length < 2 ^ (prefixWord ++ tailWord_609740).sum := by decide
  have hdescent : baseEnd_609740 < baseStart_609740 := by decide
  rcases family_descends (prefixWord ++ tailWord_609740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609803 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 7]
def baseStart_609803 : Nat := 118140960795 + 609803 * 2 ^ 59
def prefixEnd_609803 : Nat := 4983230072969 + 3 ^ 40 * 609803 * 2
def baseEnd_609803 : Nat := 34791338172642541850897

theorem tailTrace_609803 : CollatzResearch.WordTrace tailWord_609803 prefixEnd_609803 34791338172642541850897 := by
  unfold tailWord_609803
  simp only [CollatzResearch.WordTrace]
  refine ⟨22241342609795351906018063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14827561739863567937345375 22241342609795351906018063)
  ·
    refine ⟨33362013914693027859027095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22241342609795351906018063 33362013914693027859027095)
    ·
      refine ⟨50043020872039541788540643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33362013914693027859027095 50043020872039541788540643)
      ·
        refine ⟨75064531308059312682810965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50043020872039541788540643 75064531308059312682810965)
        ·
          refine ⟨879662476266320070501691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 75064531308059312682810965 879662476266320070501691)
          ·
            refine ⟨1319493714399480105752537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879662476266320070501691 1319493714399480105752537)
            ·
              refine ⟨989620285799610079314403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319493714399480105752537 989620285799610079314403)
              ·
                refine ⟨1484430428699415118971605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989620285799610079314403 1484430428699415118971605)
                ·
                  refine ⟨34791338172642541850897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1484430428699415118971605 34791338172642541850897)
                  ·
                    rfl

theorem cell23_609803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 7].length) (baseStart_609803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609803 prefixEnd_609803 := by exact prefixLift 609803
  have htrace : WordTrace (prefixWord ++ tailWord_609803) baseStart_609803 baseEnd_609803 := by
    simpa [prefixWord, tailWord_609803, baseEnd_609803] using wordTrace_append hprefix tailTrace_609803
  have hstable : (prefixWord ++ tailWord_609803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609803).length < 2 ^ (prefixWord ++ tailWord_609803).sum := by decide
  have hdescent : baseEnd_609803 < baseStart_609803 := by decide
  rcases family_descends (prefixWord ++ tailWord_609803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609813 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_609813 : Nat := 118140960795 + 609813 * 2 ^ 59
def prefixEnd_609813 : Nat := 4983230072969 + 3 ^ 40 * 609813 * 2
def baseEnd_609813 : Nat := 313127178360327837533027

theorem tailTrace_609813 : CollatzResearch.WordTrace tailWord_609813 prefixEnd_609813 313127178360327837533027 := by
  unfold tailWord_609813
  simp only [CollatzResearch.WordTrace]
  refine ⟨22241707339759123613882093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14827804893172749075921395 22241707339759123613882093)
  ·
    refine ⟨8340640252409671355205785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22241707339759123613882093 8340640252409671355205785)
    ·
      refine ⟨6255480189307253516404339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8340640252409671355205785 6255480189307253516404339)
      ·
        refine ⟨9383220283960880274606509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6255480189307253516404339 9383220283960880274606509)
        ·
          refine ⟨3518707606485330102977441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9383220283960880274606509 3518707606485330102977441)
          ·
            refine ⟨2639030704863997577233081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518707606485330102977441 2639030704863997577233081)
            ·
              refine ⟨1979273028647998182924811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639030704863997577233081 1979273028647998182924811)
              ·
                refine ⟨2968909542971997274387217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979273028647998182924811 2968909542971997274387217)
                ·
                  refine ⟨2226682157228997955790413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968909542971997274387217 2226682157228997955790413)
                  ·
                    refine ⟨835005808960874233421405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226682157228997955790413 835005808960874233421405)
                    ·
                      refine ⟨313127178360327837533027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835005808960874233421405 313127178360327837533027)
                      ·
                        rfl

theorem cell23_609813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_609813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609813 prefixEnd_609813 := by exact prefixLift 609813
  have htrace : WordTrace (prefixWord ++ tailWord_609813) baseStart_609813 baseEnd_609813 := by
    simpa [prefixWord, tailWord_609813, baseEnd_609813] using wordTrace_append hprefix tailTrace_609813
  have hstable : (prefixWord ++ tailWord_609813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609813).length < 2 ^ (prefixWord ++ tailWord_609813).sum := by decide
  have hdescent : baseEnd_609813 < baseStart_609813 := by decide
  rcases family_descends (prefixWord ++ tailWord_609813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609823 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 5, 2]
def baseStart_609823 : Nat := 118140960795 + 609823 * 2 ^ 59
def prefixEnd_609823 : Nat := 4983230072969 + 3 ^ 40 * 609823 * 2
def baseEnd_609823 : Nat := 313132313166872798407981

theorem tailTrace_609823 : CollatzResearch.WordTrace tailWord_609823 prefixEnd_609823 313132313166872798407981 := by
  unfold tailWord_609823
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242072069722895321746123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14828048046481930214497415 22242072069722895321746123)
  ·
    refine ⟨33363108104584342982619185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22242072069722895321746123 33363108104584342982619185)
    ·
      refine ⟨25022331078438257236964389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33363108104584342982619185 25022331078438257236964389)
      ·
        refine ⟨4691687077207173231930823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25022331078438257236964389 4691687077207173231930823)
        ·
          refine ⟨7037530615810759847896235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691687077207173231930823 7037530615810759847896235)
          ·
            refine ⟨10556295923716139771844353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037530615810759847896235 10556295923716139771844353)
            ·
              refine ⟨7917221942787104828883265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10556295923716139771844353 7917221942787104828883265)
              ·
                refine ⟨5937916457090328621662449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917221942787104828883265 5937916457090328621662449)
                ·
                  refine ⟨4453437342817746466246837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937916457090328621662449 4453437342817746466246837)
                  ·
                    refine ⟨417509750889163731210641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4453437342817746466246837 417509750889163731210641)
                    ·
                      refine ⟨313132313166872798407981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417509750889163731210641 313132313166872798407981)
                      ·
                        rfl

theorem cell23_609823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_609823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609823 prefixEnd_609823 := by exact prefixLift 609823
  have htrace : WordTrace (prefixWord ++ tailWord_609823) baseStart_609823 baseEnd_609823 := by
    simpa [prefixWord, tailWord_609823, baseEnd_609823] using wordTrace_append hprefix tailTrace_609823
  have hstable : (prefixWord ++ tailWord_609823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609823).length < 2 ^ (prefixWord ++ tailWord_609823).sum := by decide
  have hdescent : baseEnd_609823 < baseStart_609823 := by decide
  rcases family_descends (prefixWord ++ tailWord_609823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609873 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_609873 : Nat := 118140960795 + 609873 * 2 ^ 59
def prefixEnd_609873 : Nat := 4983230072969 + 3 ^ 40 * 609873 * 2
def baseEnd_609873 : Nat := 313157987199597602782751

theorem tailTrace_609873 : CollatzResearch.WordTrace tailWord_609873 prefixEnd_609873 313157987199597602782751 := by
  unfold tailWord_609873
  simp only [CollatzResearch.WordTrace]
  refine ⟨22243895719541753861066273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14829263813027835907377515 22243895719541753861066273)
  ·
    refine ⟨16682921789656315395799705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22243895719541753861066273 16682921789656315395799705)
    ·
      refine ⟨12512191342242236546849779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16682921789656315395799705 12512191342242236546849779)
      ·
        refine ⟨18768287013363354820274669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512191342242236546849779 18768287013363354820274669)
        ·
          refine ⟨7038107630011258057603001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18768287013363354820274669 7038107630011258057603001)
          ·
            refine ⟨5278580722508443543202251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038107630011258057603001 5278580722508443543202251)
            ·
              refine ⟨7917871083762665314803377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278580722508443543202251 7917871083762665314803377)
              ·
                refine ⟨5938403312821998986102533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917871083762665314803377 5938403312821998986102533)
                ·
                  refine ⟨1113450621154124809894225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5938403312821998986102533 1113450621154124809894225)
                  ·
                    refine ⟨835087965865593607420669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1113450621154124809894225 835087965865593607420669)
                    ·
                      refine ⟨313157987199597602782751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835087965865593607420669 313157987199597602782751)
                      ·
                        rfl

theorem cell23_609873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_609873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609873 prefixEnd_609873 := by exact prefixLift 609873
  have htrace : WordTrace (prefixWord ++ tailWord_609873) baseStart_609873 baseEnd_609873 := by
    simpa [prefixWord, tailWord_609873, baseEnd_609873] using wordTrace_append hprefix tailTrace_609873
  have hstable : (prefixWord ++ tailWord_609873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609873).length < 2 ^ (prefixWord ++ tailWord_609873).sum := by decide
  have hdescent : baseEnd_609873 < baseStart_609873 := by decide
  rcases family_descends (prefixWord ++ tailWord_609873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609910 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_609910 : Nat := 118140960795 + 609910 * 2 ^ 59
def prefixEnd_609910 : Nat := 4983230072969 + 3 ^ 40 * 609910 * 2
def baseEnd_609910 : Nat := 34797442887090439780009

theorem tailTrace_609910 : CollatzResearch.WordTrace tailWord_609910 prefixEnd_609910 34797442887090439780009 := by
  unfold tailWord_609910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390327826275481823760199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14830163480271806120108789 1390327826275481823760199)
  ·
    refine ⟨2085491739413222735640299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390327826275481823760199 2085491739413222735640299)
    ·
      refine ⟨3128237609119834103460449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085491739413222735640299 3128237609119834103460449)
      ·
        refine ⟨2346178206839875577595337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3128237609119834103460449 2346178206839875577595337)
        ·
          refine ⟨1759633655129906683196503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346178206839875577595337 1759633655129906683196503)
          ·
            refine ⟨2639450482694860024794755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759633655129906683196503 2639450482694860024794755)
            ·
              refine ⟨3959175724042290037192133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639450482694860024794755 3959175724042290037192133)
              ·
                refine ⟨742345448257929381973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3959175724042290037192133 742345448257929381973525)
                ·
                  refine ⟨34797442887090439780009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 742345448257929381973525 34797442887090439780009)
                  ·
                    rfl

theorem cell23_609910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_609910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609910 prefixEnd_609910 := by exact prefixLift 609910
  have htrace : WordTrace (prefixWord ++ tailWord_609910) baseStart_609910 baseEnd_609910 := by
    simpa [prefixWord, tailWord_609910, baseEnd_609910] using wordTrace_append hprefix tailTrace_609910
  have hstable : (prefixWord ++ tailWord_609910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609910).length < 2 ^ (prefixWord ++ tailWord_609910).sum := by decide
  have hdescent : baseEnd_609910 < baseStart_609910 := by decide
  rcases family_descends (prefixWord ++ tailWord_609910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609920 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_609920 : Nat := 118140960795 + 609920 * 2 ^ 59
def prefixEnd_609920 : Nat := 4983230072969 + 3 ^ 40 * 609920 * 2
def baseEnd_609920 : Nat := 313182120790358918895035

theorem tailTrace_609920 : CollatzResearch.WordTrace tailWord_609920 prefixEnd_609920 313182120790358918895035 := by
  unfold tailWord_609920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122804975185740444013607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14830406633580987258684809 11122804975185740444013607)
  ·
    refine ⟨16684207462778610666020411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122804975185740444013607 16684207462778610666020411)
    ·
      refine ⟨25026311194167915999030617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16684207462778610666020411 25026311194167915999030617)
      ·
        refine ⟨18769733395625936999272963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25026311194167915999030617 18769733395625936999272963)
        ·
          refine ⟨28154600093438905498909445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18769733395625936999272963 28154600093438905498909445)
          ·
            refine ⟨5278987517519794781045521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28154600093438905498909445 5278987517519794781045521)
            ·
              refine ⟨3959240638139846085784141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278987517519794781045521 3959240638139846085784141)
              ·
                refine ⟨1484715239302442282169053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959240638139846085784141 1484715239302442282169053)
                ·
                  refine ⟨556768214738415855813395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1484715239302442282169053 556768214738415855813395)
                  ·
                    refine ⟨835152322107623783720093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556768214738415855813395 835152322107623783720093)
                    ·
                      refine ⟨313182120790358918895035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835152322107623783720093 313182120790358918895035)
                      ·
                        rfl

theorem cell23_609920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_609920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609920 prefixEnd_609920 := by exact prefixLift 609920
  have htrace : WordTrace (prefixWord ++ tailWord_609920) baseStart_609920 baseEnd_609920 := by
    simpa [prefixWord, tailWord_609920, baseEnd_609920] using wordTrace_append hprefix tailTrace_609920
  have hstable : (prefixWord ++ tailWord_609920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609920).length < 2 ^ (prefixWord ++ tailWord_609920).sum := by decide
  have hdescent : baseEnd_609920 < baseStart_609920 := by decide
  rcases family_descends (prefixWord ++ tailWord_609920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609977 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 3, 2, 2]
def baseStart_609977 : Nat := 118140960795 + 609977 * 2 ^ 59
def prefixEnd_609977 : Nat := 4983230072969 + 3 ^ 40 * 609977 * 2
def baseEnd_609977 : Nat := 313211389187665195882273

theorem tailTrace_609977 : CollatzResearch.WordTrace tailWord_609977 prefixEnd_609977 313211389187665195882273 := by
  unfold tailWord_609977
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247688911164979622852185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831792607443319748568123 22247688911164979622852185)
  ·
    refine ⟨16685766683373734717139139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22247688911164979622852185 16685766683373734717139139)
    ·
      refine ⟨25028650025060602075708709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16685766683373734717139139 25028650025060602075708709)
      ·
        refine ⟨4692871879698862889195383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25028650025060602075708709 4692871879698862889195383)
        ·
          refine ⟨7039307819548294333793075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692871879698862889195383 7039307819548294333793075)
          ·
            refine ⟨10558961729322441500689613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7039307819548294333793075 10558961729322441500689613)
            ·
              refine ⟨3959610648495915562758605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10558961729322441500689613 3959610648495915562758605)
              ·
                refine ⟨1484853993185968336034477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959610648495915562758605 1484853993185968336034477)
                ·
                  refine ⟨556820247444738126012929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1484853993185968336034477 556820247444738126012929)
                  ·
                    refine ⟨417615185583553594509697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 556820247444738126012929 417615185583553594509697)
                    ·
                      refine ⟨313211389187665195882273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417615185583553594509697 313211389187665195882273)
                      ·
                        rfl

theorem cell23_609977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_609977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609977 prefixEnd_609977 := by exact prefixLift 609977
  have htrace : WordTrace (prefixWord ++ tailWord_609977) baseStart_609977 baseEnd_609977 := by
    simpa [prefixWord, tailWord_609977, baseEnd_609977] using wordTrace_append hprefix tailTrace_609977
  have hstable : (prefixWord ++ tailWord_609977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609977).length < 2 ^ (prefixWord ++ tailWord_609977).sum := by decide
  have hdescent : baseEnd_609977 < baseStart_609977 := by decide
  rcases family_descends (prefixWord ++ tailWord_609977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609980 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_609980 : Nat := 118140960795 + 609980 * 2 ^ 59
def prefixEnd_609980 : Nat := 4983230072969 + 3 ^ 40 * 609980 * 2
def baseEnd_609980 : Nat := 313212929629628684144759

theorem tailTrace_609980 : CollatzResearch.WordTrace tailWord_609980 prefixEnd_609980 313212929629628684144759 := by
  unfold tailWord_609980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123899165077055567605697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14831865553436074090140929 11123899165077055567605697)
  ·
    refine ⟨8342924373807791675704273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11123899165077055567605697 8342924373807791675704273)
    ·
      refine ⟨6257193280355843756778205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8342924373807791675704273 6257193280355843756778205)
      ·
        refine ⟨2346447480133441408791827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6257193280355843756778205 2346447480133441408791827)
        ·
          refine ⟨3519671220200162113187741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346447480133441408791827 3519671220200162113187741)
          ·
            refine ⟨1319876707575060792445403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3519671220200162113187741 1319876707575060792445403)
            ·
              refine ⟨1979815061362591188668105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319876707575060792445403 1979815061362591188668105)
              ·
                refine ⟨1484861296021943391501079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979815061362591188668105 1484861296021943391501079)
                ·
                  refine ⟨2227291944032915087251619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484861296021943391501079 2227291944032915087251619)
                  ·
                    refine ⟨3340937916049372630877429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227291944032915087251619 3340937916049372630877429)
                    ·
                      refine ⟨313212929629628684144759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3340937916049372630877429 313212929629628684144759)
                      ·
                        rfl

theorem cell23_609980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_609980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609980 prefixEnd_609980 := by exact prefixLift 609980
  have htrace : WordTrace (prefixWord ++ tailWord_609980) baseStart_609980 baseEnd_609980 := by
    simpa [prefixWord, tailWord_609980, baseEnd_609980] using wordTrace_append hprefix tailTrace_609980
  have hstable : (prefixWord ++ tailWord_609980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609980).length < 2 ^ (prefixWord ++ tailWord_609980).sum := by decide
  have hdescent : baseEnd_609980 < baseStart_609980 := by decide
  rcases family_descends (prefixWord ++ tailWord_609980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610063 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_610063 : Nat := 118140960795 + 610063 * 2 ^ 59
def prefixEnd_610063 : Nat := 4983230072969 + 3 ^ 40 * 610063 * 2
def baseEnd_610063 : Nat := 313255548523951859406877

theorem tailTrace_610063 : CollatzResearch.WordTrace tailWord_610063 prefixEnd_610063 313255548523951859406877 := by
  unfold tailWord_610063
  simp only [CollatzResearch.WordTrace]
  refine ⟨22250825588853416310482843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14833883725902277540321895 22250825588853416310482843)
  ·
    refine ⟨33376238383280124465724265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22250825588853416310482843 33376238383280124465724265)
    ·
      refine ⟨25032178787460093349293199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33376238383280124465724265 25032178787460093349293199)
      ·
        refine ⟨37548268181190140023939799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25032178787460093349293199 37548268181190140023939799)
        ·
          refine ⟨56322402271785210035909699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37548268181190140023939799 56322402271785210035909699)
          ·
            refine ⟨84483603407677815053864549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56322402271785210035909699 84483603407677815053864549)
            ·
              refine ⟨15840675638939590322599603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84483603407677815053864549 15840675638939590322599603)
              ·
                refine ⟨23761013458409385483899405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15840675638939590322599603 23761013458409385483899405)
                ·
                  refine ⟨8910380046903519556462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23761013458409385483899405 8910380046903519556462277)
                  ·
                    refine ⟨1670696258794409916836677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8910380046903519556462277 1670696258794409916836677)
                    ·
                      refine ⟨313255548523951859406877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1670696258794409916836677 313255548523951859406877)
                      ·
                        rfl

theorem cell23_610063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_610063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610063 prefixEnd_610063 := by exact prefixLift 610063
  have htrace : WordTrace (prefixWord ++ tailWord_610063) baseStart_610063 baseEnd_610063 := by
    simpa [prefixWord, tailWord_610063, baseEnd_610063] using wordTrace_append hprefix tailTrace_610063
  have hstable : (prefixWord ++ tailWord_610063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610063).length < 2 ^ (prefixWord ++ tailWord_610063).sum := by decide
  have hdescent : baseEnd_610063 < baseStart_610063 := by decide
  rcases family_descends (prefixWord ++ tailWord_610063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610067 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 4, 2, 2]
def baseStart_610067 : Nat := 118140960795 + 610067 * 2 ^ 59
def prefixEnd_610067 : Nat := 4983230072969 + 3 ^ 40 * 610067 * 2
def baseEnd_610067 : Nat := 313257602446569843756859

theorem tailTrace_610067 : CollatzResearch.WordTrace tailWord_610067 prefixEnd_610067 313257602446569843756859 := by
  unfold tailWord_610067
  simp only [CollatzResearch.WordTrace]
  refine ⟨22250971480838924993628455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14833980987225949995752303 22250971480838924993628455)
  ·
    refine ⟨33376457221258387490442683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22250971480838924993628455 33376457221258387490442683)
    ·
      refine ⟨50064685831887581235664025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33376457221258387490442683 50064685831887581235664025)
      ·
        refine ⟨37548514373915685926748019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50064685831887581235664025 37548514373915685926748019)
        ·
          refine ⟨56322771560873528890122029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37548514373915685926748019 56322771560873528890122029)
          ·
            refine ⟨21121039335327573333795761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56322771560873528890122029 21121039335327573333795761)
            ·
              refine ⟨15840779501495680000346821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21121039335327573333795761 15840779501495680000346821)
              ·
                refine ⟨2970146156530440000065029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15840779501495680000346821 2970146156530440000065029)
                ·
                  refine ⟨556902404349457500012193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2970146156530440000065029 556902404349457500012193)
                  ·
                    refine ⟨417676803262093125009145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 556902404349457500012193 417676803262093125009145)
                    ·
                      refine ⟨313257602446569843756859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417676803262093125009145 313257602446569843756859)
                      ·
                        rfl

theorem cell23_610067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2, 2].length) (baseStart_610067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610067 prefixEnd_610067 := by exact prefixLift 610067
  have htrace : WordTrace (prefixWord ++ tailWord_610067) baseStart_610067 baseEnd_610067 := by
    simpa [prefixWord, tailWord_610067, baseEnd_610067] using wordTrace_append hprefix tailTrace_610067
  have hstable : (prefixWord ++ tailWord_610067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610067).length < 2 ^ (prefixWord ++ tailWord_610067).sum := by decide
  have hdescent : baseEnd_610067 < baseStart_610067 := by decide
  rcases family_descends (prefixWord ++ tailWord_610067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610071 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_610071 : Nat := 118140960795 + 610071 * 2 ^ 59
def prefixEnd_610071 : Nat := 4983230072969 + 3 ^ 40 * 610071 * 2
def baseEnd_610071 : Nat := 313259656369187828106841

theorem tailTrace_610071 : CollatzResearch.WordTrace tailWord_610071 prefixEnd_610071 313259656369187828106841 := by
  unfold tailWord_610071
  simp only [CollatzResearch.WordTrace]
  refine ⟨22251117372824433676774067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14834078248549622451182711 22251117372824433676774067)
  ·
    refine ⟨33376676059236650515161101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22251117372824433676774067 33376676059236650515161101)
    ·
      refine ⟨12516253522213743943185413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33376676059236650515161101 12516253522213743943185413)
      ·
        refine ⟨2346797535415076989347265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12516253522213743943185413 2346797535415076989347265)
        ·
          refine ⟨1760098151561307742010449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346797535415076989347265 1760098151561307742010449)
          ·
            refine ⟨1320073613670980806507837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760098151561307742010449 1320073613670980806507837)
            ·
              refine ⟨495027605126617802440439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1320073613670980806507837 495027605126617802440439)
              ·
                refine ⟨742541407689926703660659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495027605126617802440439 742541407689926703660659)
                ·
                  refine ⟨1113812111534890055490989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742541407689926703660659 1113812111534890055490989)
                  ·
                    refine ⟨417679541825583770809121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113812111534890055490989 417679541825583770809121)
                    ·
                      refine ⟨313259656369187828106841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417679541825583770809121 313259656369187828106841)
                      ·
                        rfl

theorem cell23_610071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_610071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610071 prefixEnd_610071 := by exact prefixLift 610071
  have htrace : WordTrace (prefixWord ++ tailWord_610071) baseStart_610071 baseEnd_610071 := by
    simpa [prefixWord, tailWord_610071, baseEnd_610071] using wordTrace_append hprefix tailTrace_610071
  have hstable : (prefixWord ++ tailWord_610071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610071).length < 2 ^ (prefixWord ++ tailWord_610071).sum := by decide
  have hdescent : baseEnd_610071 < baseStart_610071 := by decide
  rcases family_descends (prefixWord ++ tailWord_610071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610080 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_610080 : Nat := 118140960795 + 610080 * 2 ^ 59
def prefixEnd_610080 : Nat := 4983230072969 + 3 ^ 40 * 610080 * 2
def baseEnd_610080 : Nat := 313264277695078292894299

theorem tailTrace_610080 : CollatzResearch.WordTrace tailWord_610080 prefixEnd_610080 313264277695078292894299 := by
  unfold tailWord_610080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125722814895914106925847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14834297086527885475901129 11125722814895914106925847)
  ·
    refine ⟨16688584222343871160388771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11125722814895914106925847 16688584222343871160388771)
    ·
      refine ⟨25032876333515806740583157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16688584222343871160388771 25032876333515806740583157)
      ·
        refine ⟨2346832156267106881929671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25032876333515806740583157 2346832156267106881929671)
        ·
          refine ⟨3520248234400660322894507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346832156267106881929671 3520248234400660322894507)
          ·
            refine ⟨5280372351600990484341761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520248234400660322894507 5280372351600990484341761)
            ·
              refine ⟨3960279263700742863256321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5280372351600990484341761 3960279263700742863256321)
              ·
                refine ⟨2970209447775557147442241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3960279263700742863256321 2970209447775557147442241)
                ·
                  refine ⟨2227657085831667860581681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970209447775557147442241 2227657085831667860581681)
                  ·
                    refine ⟨1670742814373750895436261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227657085831667860581681 1670742814373750895436261)
                    ·
                      refine ⟨313264277695078292894299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1670742814373750895436261 313264277695078292894299)
                      ·
                        rfl

theorem cell23_610080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_610080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610080 prefixEnd_610080 := by exact prefixLift 610080
  have htrace : WordTrace (prefixWord ++ tailWord_610080) baseStart_610080 baseEnd_610080 := by
    simpa [prefixWord, tailWord_610080, baseEnd_610080] using wordTrace_append hprefix tailTrace_610080
  have hstable : (prefixWord ++ tailWord_610080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610080).length < 2 ^ (prefixWord ++ tailWord_610080).sum := by decide
  have hdescent : baseEnd_610080 < baseStart_610080 := by decide
  rcases family_descends (prefixWord ++ tailWord_610080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610083 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_610083 : Nat := 118140960795 + 610083 * 2 ^ 59
def prefixEnd_610083 : Nat := 4983230072969 + 3 ^ 40 * 610083 * 2
def baseEnd_610083 : Nat := 313265818137041781156785

theorem tailTrace_610083 : CollatzResearch.WordTrace tailWord_610083 prefixEnd_610083 313265818137041781156785 := by
  unfold tailWord_610083
  simp only [CollatzResearch.WordTrace]
  refine ⟨22251555048780959726210903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14834370032520639817473935 22251555048780959726210903)
  ·
    refine ⟨33377332573171439589316355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22251555048780959726210903 33377332573171439589316355)
    ·
      refine ⟨50065998859757159383974533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33377332573171439589316355 50065998859757159383974533)
      ·
        refine ⟨9387374786204467384495225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50065998859757159383974533 9387374786204467384495225)
        ·
          refine ⟨7040531089653350538371419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387374786204467384495225 7040531089653350538371419)
          ·
            refine ⟨10560796634480025807557129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040531089653350538371419 10560796634480025807557129)
            ·
              refine ⟨7920597475860019355667847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10560796634480025807557129 7920597475860019355667847)
              ·
                refine ⟨11880896213790029033501771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920597475860019355667847 11880896213790029033501771)
                ·
                  refine ⟨17821344320685043550252657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11880896213790029033501771 17821344320685043550252657)
                  ·
                    refine ⟨13366008240513782662689493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17821344320685043550252657 13366008240513782662689493)
                    ·
                      refine ⟨313265818137041781156785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13366008240513782662689493 313265818137041781156785)
                      ·
                        rfl

theorem cell23_610083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_610083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610083 prefixEnd_610083 := by exact prefixLift 610083
  have htrace : WordTrace (prefixWord ++ tailWord_610083) baseStart_610083 baseEnd_610083 := by
    simpa [prefixWord, tailWord_610083, baseEnd_610083] using wordTrace_append hprefix tailTrace_610083
  have hstable : (prefixWord ++ tailWord_610083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610083).length < 2 ^ (prefixWord ++ tailWord_610083).sum := by decide
  have hdescent : baseEnd_610083 < baseStart_610083 := by decide
  rcases family_descends (prefixWord ++ tailWord_610083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610120 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_610120 : Nat := 118140960795 + 610120 * 2 ^ 59
def prefixEnd_610120 : Nat := 4983230072969 + 3 ^ 40 * 610120 * 2
def baseEnd_610120 : Nat := 104428272307086045464705

theorem tailTrace_610120 : CollatzResearch.WordTrace tailWord_610120 prefixEnd_610120 104428272307086045464705 := by
  unfold tailWord_610120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126452274823457522653907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14835269699764610030205209 11126452274823457522653907)
  ·
    refine ⟨16689678412235186283980861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11126452274823457522653907 16689678412235186283980861)
    ·
      refine ⟨6258629404588194856492823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16689678412235186283980861 6258629404588194856492823)
      ·
        refine ⟨9387944106882292284739235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258629404588194856492823 9387944106882292284739235)
        ·
          refine ⟨14081916160323438427108853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9387944106882292284739235 14081916160323438427108853)
          ·
            refine ⟨1320179640030322352541455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14081916160323438427108853 1320179640030322352541455)
            ·
              refine ⟨1980269460045483528812183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320179640030322352541455 1980269460045483528812183)
              ·
                refine ⟨2970404190068225293218275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980269460045483528812183 2970404190068225293218275)
                ·
                  refine ⟨4455606285102337939827413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970404190068225293218275 4455606285102337939827413)
                  ·
                    refine ⟨104428272307086045464705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4455606285102337939827413 104428272307086045464705)
                    ·
                      rfl

theorem cell23_610120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_610120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610120 prefixEnd_610120 := by exact prefixLift 610120
  have htrace : WordTrace (prefixWord ++ tailWord_610120) baseStart_610120 baseEnd_610120 := by
    simpa [prefixWord, tailWord_610120, baseEnd_610120] using wordTrace_append hprefix tailTrace_610120
  have hstable : (prefixWord ++ tailWord_610120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610120).length < 2 ^ (prefixWord ++ tailWord_610120).sum := by decide
  have hdescent : baseEnd_610120 < baseStart_610120 := by decide
  rcases family_descends (prefixWord ++ tailWord_610120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610124 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 5]
def baseStart_610124 : Nat := 118140960795 + 610124 * 2 ^ 59
def prefixEnd_610124 : Nat := 4983230072969 + 3 ^ 40 * 610124 * 2
def baseEnd_610124 : Nat := 34809652315986235638233

theorem tailTrace_610124 : CollatzResearch.WordTrace tailWord_610124 prefixEnd_610124 34809652315986235638233 := by
  unfold tailWord_610124
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126525220816211864226713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14835366961088282485635617 11126525220816211864226713)
  ·
    refine ⟨8344893915612158898170035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11126525220816211864226713 8344893915612158898170035)
    ·
      refine ⟨12517340873418238347255053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8344893915612158898170035 12517340873418238347255053)
      ·
        refine ⟨4694002827531839380220645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12517340873418238347255053 4694002827531839380220645)
        ·
          refine ⟨880125530162219883791371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4694002827531839380220645 880125530162219883791371)
          ·
            refine ⟨1320188295243329825687057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880125530162219883791371 1320188295243329825687057)
            ·
              refine ⟨990141221432497369265293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320188295243329825687057 990141221432497369265293)
              ·
                refine ⟨371302958037186513474485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990141221432497369265293 371302958037186513474485)
                ·
                  refine ⟨34809652315986235638233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371302958037186513474485 34809652315986235638233)
                  ·
                    rfl

theorem cell23_610124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_610124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610124 prefixEnd_610124 := by exact prefixLift 610124
  have htrace : WordTrace (prefixWord ++ tailWord_610124) baseStart_610124 baseEnd_610124 := by
    simpa [prefixWord, tailWord_610124, baseEnd_610124] using wordTrace_append hprefix tailTrace_610124
  have hstable : (prefixWord ++ tailWord_610124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610124).length < 2 ^ (prefixWord ++ tailWord_610124).sum := by decide
  have hdescent : baseEnd_610124 < baseStart_610124 := by decide
  rcases family_descends (prefixWord ++ tailWord_610124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610174 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_610174 : Nat := 118140960795 + 610174 * 2 ^ 59
def prefixEnd_610174 : Nat := 4983230072969 + 3 ^ 40 * 610174 * 2
def baseEnd_610174 : Nat := 313312544876600925118867

theorem tailTrace_610174 : CollatzResearch.WordTrace tailWord_610174 prefixEnd_610174 313312544876600925118867 := by
  unfold tailWord_610174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781859261431410283471697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14836582727634188178515717 2781859261431410283471697)
  ·
    refine ⟨2086394446073557712603773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2781859261431410283471697 2086394446073557712603773)
    ·
      refine ⟨782397917277584142226415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2086394446073557712603773 782397917277584142226415)
      ·
        refine ⟨1173596875916376213339623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782397917277584142226415 1173596875916376213339623)
        ·
          refine ⟨1760395313874564320009435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173596875916376213339623 1760395313874564320009435)
          ·
            refine ⟨2640592970811846480014153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760395313874564320009435 2640592970811846480014153)
            ·
              refine ⟨1980444728108884860010615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640592970811846480014153 1980444728108884860010615)
              ·
                refine ⟨2970667092163327290015923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980444728108884860010615 2970667092163327290015923)
                ·
                  refine ⟨4456000638244990935023885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970667092163327290015923 4456000638244990935023885)
                  ·
                    refine ⟨1671000239341871600633957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4456000638244990935023885 1671000239341871600633957)
                    ·
                      refine ⟨313312544876600925118867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1671000239341871600633957 313312544876600925118867)
                      ·
                        rfl

theorem cell23_610174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_610174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610174 prefixEnd_610174 := by exact prefixLift 610174
  have htrace : WordTrace (prefixWord ++ tailWord_610174) baseStart_610174 baseEnd_610174 := by
    simpa [prefixWord, tailWord_610174, baseEnd_610174] using wordTrace_append hprefix tailTrace_610174
  have hstable : (prefixWord ++ tailWord_610174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610174).length < 2 ^ (prefixWord ++ tailWord_610174).sum := by decide
  have hdescent : baseEnd_610174 < baseStart_610174 := by decide
  rcases family_descends (prefixWord ++ tailWord_610174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610180 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 8]
def baseStart_610180 : Nat := 118140960795 + 610180 * 2 ^ 59
def prefixEnd_610180 : Nat := 4983230072969 + 3 ^ 40 * 610180 * 2
def baseEnd_610180 : Nat := 34812847306725322404871

theorem tailTrace_610180 : CollatzResearch.WordTrace tailWord_610180 prefixEnd_610180 34812847306725322404871 := by
  unfold tailWord_610180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127546464714772646245997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14836728619619696861661329 11127546464714772646245997)
  ·
    refine ⟨4172829924268039742342249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11127546464714772646245997 4172829924268039742342249)
    ·
      refine ⟨3129622443201029806756687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4172829924268039742342249 3129622443201029806756687)
      ·
        refine ⟨4694433664801544710135031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129622443201029806756687 4694433664801544710135031)
        ·
          refine ⟨7041650497202317065202547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694433664801544710135031 7041650497202317065202547)
          ·
            refine ⟨10562475745803475597803821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041650497202317065202547 10562475745803475597803821)
            ·
              refine ⟨3960928404676303349176433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10562475745803475597803821 3960928404676303349176433)
              ·
                refine ⟨2970696303507227511882325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3960928404676303349176433 2970696303507227511882325)
                ·
                  refine ⟨34812847306725322404871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2970696303507227511882325 34812847306725322404871)
                  ·
                    rfl

theorem cell23_610180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_610180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610180 prefixEnd_610180 := by exact prefixLift 610180
  have htrace : WordTrace (prefixWord ++ tailWord_610180) baseStart_610180 baseEnd_610180 := by
    simpa [prefixWord, tailWord_610180, baseEnd_610180] using wordTrace_append hprefix tailTrace_610180
  have hstable : (prefixWord ++ tailWord_610180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610180).length < 2 ^ (prefixWord ++ tailWord_610180).sum := by decide
  have hdescent : baseEnd_610180 < baseStart_610180 := by decide
  rcases family_descends (prefixWord ++ tailWord_610180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610194 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_610194 : Nat := 118140960795 + 610194 * 2 ^ 59
def prefixEnd_610194 : Nat := 4983230072969 + 3 ^ 40 * 610194 * 2
def baseEnd_610194 : Nat := 313322814489690846868775

theorem tailTrace_610194 : CollatzResearch.WordTrace tailWord_610194 prefixEnd_610194 313322814489690846868775 := by
  unfold tailWord_610194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563900887844706420875409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14837069034252550455667757 5563900887844706420875409)
  ·
    refine ⟨4172925665883529815656557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5563900887844706420875409 4172925665883529815656557)
    ·
      refine ⟨1564847124706323680871209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4172925665883529815656557 1564847124706323680871209)
      ·
        refine ⟨1173635343529742760653407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1564847124706323680871209 1173635343529742760653407)
        ·
          refine ⟨1760453015294614140980111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173635343529742760653407 1760453015294614140980111)
          ·
            refine ⟨2640679522941921211470167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760453015294614140980111 2640679522941921211470167)
            ·
              refine ⟨3961019284412881817205251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640679522941921211470167 3961019284412881817205251)
              ·
                refine ⟨5941528926619322725807877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961019284412881817205251 5941528926619322725807877)
                ·
                  refine ⟨1114036673741123011088977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5941528926619322725807877 1114036673741123011088977)
                  ·
                    refine ⟨835527505305842258316733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114036673741123011088977 835527505305842258316733)
                    ·
                      refine ⟨313322814489690846868775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835527505305842258316733 313322814489690846868775)
                      ·
                        rfl

theorem cell23_610194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_610194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610194 prefixEnd_610194 := by exact prefixLift 610194
  have htrace : WordTrace (prefixWord ++ tailWord_610194) baseStart_610194 baseEnd_610194 := by
    simpa [prefixWord, tailWord_610194, baseEnd_610194] using wordTrace_append hprefix tailTrace_610194
  have hstable : (prefixWord ++ tailWord_610194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610194).length < 2 ^ (prefixWord ++ tailWord_610194).sum := by decide
  have hdescent : baseEnd_610194 < baseStart_610194 := by decide
  rcases family_descends (prefixWord ++ tailWord_610194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610217 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 5, 2]
def baseStart_610217 : Nat := 118140960795 + 610217 * 2 ^ 59
def prefixEnd_610217 : Nat := 4983230072969 + 3 ^ 40 * 610217 * 2
def baseEnd_610217 : Nat := 313334624544744256881169

theorem tailTrace_610217 : CollatzResearch.WordTrace tailWord_610217 prefixEnd_610217 313334624544744256881169 := by
  unfold tailWord_610217
  simp only [CollatzResearch.WordTrace]
  refine ⟨22256442430295500611588905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14837628286863667074392603 22256442430295500611588905)
  ·
    refine ⟨16692331822721625458691679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22256442430295500611588905 16692331822721625458691679)
    ·
      refine ⟨25038497734082438188037519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16692331822721625458691679 25038497734082438188037519)
      ·
        refine ⟨37557746601123657282056279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25038497734082438188037519 37557746601123657282056279)
        ·
          refine ⟨56336619901685485923084419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37557746601123657282056279 56336619901685485923084419)
          ·
            refine ⟨84504929852528228884626629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56336619901685485923084419 84504929852528228884626629)
            ·
              refine ⟨15844674347349042915867493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84504929852528228884626629 15844674347349042915867493)
              ·
                refine ⟨2970876440127945546725155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15844674347349042915867493 2970876440127945546725155)
                ·
                  refine ⟨4456314660191918320087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970876440127945546725155 4456314660191918320087733)
                  ·
                    refine ⟨417779499392992342508225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4456314660191918320087733 417779499392992342508225)
                    ·
                      refine ⟨313334624544744256881169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417779499392992342508225 313334624544744256881169)
                      ·
                        rfl

theorem cell23_610217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5, 2].length) (baseStart_610217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610217 prefixEnd_610217 := by exact prefixLift 610217
  have htrace : WordTrace (prefixWord ++ tailWord_610217) baseStart_610217 baseEnd_610217 := by
    simpa [prefixWord, tailWord_610217, baseEnd_610217] using wordTrace_append hprefix tailTrace_610217
  have hstable : (prefixWord ++ tailWord_610217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610217).length < 2 ^ (prefixWord ++ tailWord_610217).sum := by decide
  have hdescent : baseEnd_610217 < baseStart_610217 := by decide
  rcases family_descends (prefixWord ++ tailWord_610217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610228 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_610228 : Nat := 118140960795 + 610228 * 2 ^ 59
def prefixEnd_610228 : Nat := 4983230072969 + 3 ^ 40 * 610228 * 2
def baseEnd_610228 : Nat := 313340272831943713843619

theorem tailTrace_610228 : CollatzResearch.WordTrace tailWord_610228 prefixEnd_610228 313340272831943713843619 := by
  unfold tailWord_610228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128421816627824745119669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14837895755503766326826225 11128421816627824745119669)
  ·
    refine ⟨1043289545308858569854969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11128421816627824745119669 1043289545308858569854969)
    ·
      refine ⟨782467158981643927391227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043289545308858569854969 782467158981643927391227)
      ·
        refine ⟨1173700738472465891086841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782467158981643927391227 1173700738472465891086841)
        ·
          refine ⟨880275553854349418315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173700738472465891086841 880275553854349418315131)
          ·
            refine ⟨1320413330781524127472697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880275553854349418315131 1320413330781524127472697)
            ·
              refine ⟨990309998086143095604523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320413330781524127472697 990309998086143095604523)
              ·
                refine ⟨1485464997129214643406785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990309998086143095604523 1485464997129214643406785)
                ·
                  refine ⟨1114098747846910982555089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485464997129214643406785 1114098747846910982555089)
                  ·
                    refine ⟨835574060885183236916317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114098747846910982555089 835574060885183236916317)
                    ·
                      refine ⟨313340272831943713843619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835574060885183236916317 313340272831943713843619)
                      ·
                        rfl

theorem cell23_610228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_610228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610228 prefixEnd_610228 := by exact prefixLift 610228
  have htrace : WordTrace (prefixWord ++ tailWord_610228) baseStart_610228 baseEnd_610228 := by
    simpa [prefixWord, tailWord_610228, baseEnd_610228] using wordTrace_append hprefix tailTrace_610228
  have hstable : (prefixWord ++ tailWord_610228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610228).length < 2 ^ (prefixWord ++ tailWord_610228).sum := by decide
  have hdescent : baseEnd_610228 < baseStart_610228 := by decide
  rcases family_descends (prefixWord ++ tailWord_610228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610285 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_610285 : Nat := 118140960795 + 610285 * 2 ^ 59
def prefixEnd_610285 : Nat := 4983230072969 + 3 ^ 40 * 610285 * 2
def baseEnd_610285 : Nat := 313369541229249990830857

theorem tailTrace_610285 : CollatzResearch.WordTrace tailWord_610285 prefixEnd_610285 313369541229249990830857 := by
  unfold tailWord_610285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258922594049148225064309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839281729366098816709539 22258922594049148225064309)
  ·
    refine ⟨2086773993192107646099779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22258922594049148225064309 2086773993192107646099779)
    ·
      refine ⟨3130160989788161469149669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2086773993192107646099779 3130160989788161469149669)
      ·
        refine ⟨586905185585280275465563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3130160989788161469149669 586905185585280275465563)
        ·
          refine ⟨880357778377920413198345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586905185585280275465563 880357778377920413198345)
          ·
            refine ⟨660268333783440309898759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880357778377920413198345 660268333783440309898759)
            ·
              refine ⟨990402500675160464848139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660268333783440309898759 990402500675160464848139)
              ·
                refine ⟨1485603751012740697272209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990402500675160464848139 1485603751012740697272209)
                ·
                  refine ⟨1114202813259555522954157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485603751012740697272209 1114202813259555522954157)
                  ·
                    refine ⟨417826054972333321107809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114202813259555522954157 417826054972333321107809)
                    ·
                      refine ⟨313369541229249990830857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417826054972333321107809 313369541229249990830857)
                      ·
                        rfl

theorem cell23_610285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_610285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610285 prefixEnd_610285 := by exact prefixLift 610285
  have htrace : WordTrace (prefixWord ++ tailWord_610285) baseStart_610285 baseEnd_610285 := by
    simpa [prefixWord, tailWord_610285, baseEnd_610285] using wordTrace_append hprefix tailTrace_610285
  have hstable : (prefixWord ++ tailWord_610285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610285).length < 2 ^ (prefixWord ++ tailWord_610285).sum := by decide
  have hdescent : baseEnd_610285 < baseStart_610285 := by decide
  rcases family_descends (prefixWord ++ tailWord_610285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610287 : List Nat := [1, 1, 2, 1, 4, 2, 5, 7]
def baseStart_610287 : Nat := 118140960795 + 610287 * 2 ^ 59
def prefixEnd_610287 : Nat := 4983230072969 + 3 ^ 40 * 610287 * 2
def baseEnd_610287 : Nat := 11606317340391073444661

theorem tailTrace_610287 : CollatzResearch.WordTrace tailWord_610287 prefixEnd_610287 11606317340391073444661 := by
  unfold tailWord_610287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258995540041902566637115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839330360027935044424743 22258995540041902566637115)
  ·
    refine ⟨33388493310062853849955673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258995540041902566637115 33388493310062853849955673)
    ·
      refine ⟨25041369982547140387466755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33388493310062853849955673 25041369982547140387466755)
      ·
        refine ⟨37562054973820710581200133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25041369982547140387466755 37562054973820710581200133)
        ·
          refine ⟨7042885307591383233975025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37562054973820710581200133 7042885307591383233975025)
          ·
            refine ⟨5282163980693537425481269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042885307591383233975025 5282163980693537425481269)
            ·
              refine ⟨495202873190019133638869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5282163980693537425481269 495202873190019133638869)
              ·
                refine ⟨11606317340391073444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 495202873190019133638869 11606317340391073444661)
                ·
                  rfl

theorem cell23_610287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 7].length) (baseStart_610287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610287 prefixEnd_610287 := by exact prefixLift 610287
  have htrace : WordTrace (prefixWord ++ tailWord_610287) baseStart_610287 baseEnd_610287 := by
    simpa [prefixWord, tailWord_610287, baseEnd_610287] using wordTrace_append hprefix tailTrace_610287
  have hstable : (prefixWord ++ tailWord_610287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610287).length < 2 ^ (prefixWord ++ tailWord_610287).sum := by decide
  have hdescent : baseEnd_610287 < baseStart_610287 := by decide
  rcases family_descends (prefixWord ++ tailWord_610287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610301 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_610301 : Nat := 118140960795 + 610301 * 2 ^ 59
def prefixEnd_610301 : Nat := 4983230072969 + 3 ^ 40 * 610301 * 2
def baseEnd_610301 : Nat := 313377756919721928230783

theorem tailTrace_610301 : CollatzResearch.WordTrace tailWord_610301 prefixEnd_610301 313377756919721928230783 := by
  unfold tailWord_610301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259506161991182957646757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839670774660788638431171 22259506161991182957646757)
  ·
    refine ⟨4173657405373346804558767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22259506161991182957646757 4173657405373346804558767)
    ·
      refine ⟨6260486108060020206838151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173657405373346804558767 6260486108060020206838151)
      ·
        refine ⟨9390729162090030310257227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260486108060020206838151 9390729162090030310257227)
        ·
          refine ⟨14086093743135045465385841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390729162090030310257227 14086093743135045465385841)
          ·
            refine ⟨10564570307351284099039381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14086093743135045465385841 10564570307351284099039381)
            ·
              refine ⟨495214233157091442142471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10564570307351284099039381 495214233157091442142471)
              ·
                refine ⟨742821349735637163213707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495214233157091442142471 742821349735637163213707)
                ·
                  refine ⟨1114232024603455744820561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742821349735637163213707 1114232024603455744820561)
                  ·
                    refine ⟨835674018452591808615421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114232024603455744820561 835674018452591808615421)
                    ·
                      refine ⟨313377756919721928230783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835674018452591808615421 313377756919721928230783)
                      ·
                        rfl

theorem cell23_610301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_610301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610301 prefixEnd_610301 := by exact prefixLift 610301
  have htrace : WordTrace (prefixWord ++ tailWord_610301) baseStart_610301 baseEnd_610301 := by
    simpa [prefixWord, tailWord_610301, baseEnd_610301] using wordTrace_append hprefix tailTrace_610301
  have hstable : (prefixWord ++ tailWord_610301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610301).length < 2 ^ (prefixWord ++ tailWord_610301).sum := by decide
  have hdescent : baseEnd_610301 < baseStart_610301 := by decide
  rcases family_descends (prefixWord ++ tailWord_610301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610341 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_610341 : Nat := 118140960795 + 610341 * 2 ^ 59
def prefixEnd_610341 : Nat := 4983230072969 + 3 ^ 40 * 610341 * 2
def baseEnd_610341 : Nat := 313398296145901771730599

theorem tailTrace_610341 : CollatzResearch.WordTrace tailWord_610341 prefixEnd_610341 313398296145901771730599 := by
  unfold tailWord_610341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260965081846269789102877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14840643387897513192735251 22260965081846269789102877)
  ·
    refine ⟨8347861905692351170913579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22260965081846269789102877 8347861905692351170913579)
    ·
      refine ⟨12521792858538526756370369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8347861905692351170913579 12521792858538526756370369)
      ·
        refine ⟨9391344643903895067277777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12521792858538526756370369 9391344643903895067277777)
        ·
          refine ⟨7043508482927921300458333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9391344643903895067277777 7043508482927921300458333)
          ·
            refine ⟨2641315681097970487671875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7043508482927921300458333 2641315681097970487671875)
            ·
              refine ⟨3961973521646955731507813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641315681097970487671875 3961973521646955731507813)
              ·
                refine ⟨742870035308804199657715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3961973521646955731507813 742870035308804199657715)
                ·
                  refine ⟨1114305052963206299486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742870035308804199657715 1114305052963206299486573)
                  ·
                    refine ⟨417864394861202362307465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114305052963206299486573 417864394861202362307465)
                    ·
                      refine ⟨313398296145901771730599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417864394861202362307465 313398296145901771730599)
                      ·
                        rfl

theorem cell23_610341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_610341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610341 prefixEnd_610341 := by exact prefixLift 610341
  have htrace : WordTrace (prefixWord ++ tailWord_610341) baseStart_610341 baseEnd_610341 := by
    simpa [prefixWord, tailWord_610341, baseEnd_610341] using wordTrace_append hprefix tailTrace_610341
  have hstable : (prefixWord ++ tailWord_610341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610341).length < 2 ^ (prefixWord ++ tailWord_610341).sum := by decide
  have hdescent : baseEnd_610341 < baseStart_610341 := by decide
  rcases family_descends (prefixWord ++ tailWord_610341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610357 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_610357 : Nat := 118140960795 + 610357 * 2 ^ 59
def prefixEnd_610357 : Nat := 4983230072969 + 3 ^ 40 * 610357 * 2
def baseEnd_610357 : Nat := 313406511836373709130525

theorem tailTrace_610357 : CollatzResearch.WordTrace tailWord_610357 prefixEnd_610357 313406511836373709130525 := by
  unfold tailWord_610357
  simp only [CollatzResearch.WordTrace]
  refine ⟨22261548649788304521685325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14841032433192203014456883 22261548649788304521685325)
  ·
    refine ⟨8348080743670614195631997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22261548649788304521685325 8348080743670614195631997)
    ·
      refine ⟨3130530278876480323361999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8348080743670614195631997 3130530278876480323361999)
      ·
        refine ⟨4695795418314720485042999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130530278876480323361999 4695795418314720485042999)
        ·
          refine ⟨7043693127472080727564499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695795418314720485042999 7043693127472080727564499)
          ·
            refine ⟨10565539691208121091346749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043693127472080727564499 10565539691208121091346749)
            ·
              refine ⟨3962077384203045409255031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10565539691208121091346749 3962077384203045409255031)
              ·
                refine ⟨5943116076304568113882547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962077384203045409255031 5943116076304568113882547)
                ·
                  refine ⟨8914674114456852170823821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943116076304568113882547 8914674114456852170823821)
                  ·
                    refine ⟨3343002792921319564058933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8914674114456852170823821 3343002792921319564058933)
                    ·
                      refine ⟨313406511836373709130525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3343002792921319564058933 313406511836373709130525)
                      ·
                        rfl

theorem cell23_610357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_610357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610357 prefixEnd_610357 := by exact prefixLift 610357
  have htrace : WordTrace (prefixWord ++ tailWord_610357) baseStart_610357 baseEnd_610357 := by
    simpa [prefixWord, tailWord_610357, baseEnd_610357] using wordTrace_append hprefix tailTrace_610357
  have hstable : (prefixWord ++ tailWord_610357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610357).length < 2 ^ (prefixWord ++ tailWord_610357).sum := by decide
  have hdescent : baseEnd_610357 < baseStart_610357 := by decide
  rcases family_descends (prefixWord ++ tailWord_610357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610358 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_610358 : Nat := 118140960795 + 610358 * 2 ^ 59
def prefixEnd_610358 : Nat := 4983230072969 + 3 ^ 40 * 610358 * 2
def baseEnd_610358 : Nat := 313407025317028205218021

theorem tailTrace_610358 : CollatzResearch.WordTrace tailWord_610358 prefixEnd_610358 313407025317028205218021 := by
  unfold tailWord_610358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391349070174042605779483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14841056748523121128314485 1391349070174042605779483)
  ·
    refine ⟨2087023605261063908669225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1391349070174042605779483 2087023605261063908669225)
    ·
      refine ⟨1565267703945797931501919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087023605261063908669225 1565267703945797931501919)
      ·
        refine ⟨2347901555918696897252879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565267703945797931501919 2347901555918696897252879)
        ·
          refine ⟨3521852333878045345879319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2347901555918696897252879 3521852333878045345879319)
          ·
            refine ⟨5282778500817068018818979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521852333878045345879319 5282778500817068018818979)
            ·
              refine ⟨7924167751225602028228469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282778500817068018818979 7924167751225602028228469)
              ·
                refine ⟨742890726677400190146419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7924167751225602028228469 742890726677400190146419)
                ·
                  refine ⟨1114336090016100285219629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742890726677400190146419 1114336090016100285219629)
                  ·
                    refine ⟨417876033756037606957361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114336090016100285219629 417876033756037606957361)
                    ·
                      refine ⟨313407025317028205218021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417876033756037606957361 313407025317028205218021)
                      ·
                        rfl

theorem cell23_610358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_610358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610358 prefixEnd_610358 := by exact prefixLift 610358
  have htrace : WordTrace (prefixWord ++ tailWord_610358) baseStart_610358 baseEnd_610358 := by
    simpa [prefixWord, tailWord_610358, baseEnd_610358] using wordTrace_append hprefix tailTrace_610358
  have hstable : (prefixWord ++ tailWord_610358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610358).length < 2 ^ (prefixWord ++ tailWord_610358).sum := by decide
  have hdescent : baseEnd_610358 < baseStart_610358 := by decide
  rcases family_descends (prefixWord ++ tailWord_610358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610367 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_610367 : Nat := 118140960795 + 610367 * 2 ^ 59
def prefixEnd_610367 : Nat := 4983230072969 + 3 ^ 40 * 610367 * 2
def baseEnd_610367 : Nat := 313411646642918670005479

theorem tailTrace_610367 : CollatzResearch.WordTrace tailWord_610367 prefixEnd_610367 313411646642918670005479 := by
  unfold tailWord_610367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22261913379752076229549355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14841275586501384153032903 22261913379752076229549355)
  ·
    refine ⟨33392870069628114344324033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22261913379752076229549355 33392870069628114344324033)
    ·
      refine ⟨25044652552221085758243025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33392870069628114344324033 25044652552221085758243025)
      ·
        refine ⟨18783489414165814318682269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25044652552221085758243025 18783489414165814318682269)
        ·
          refine ⟨7043808530312180369505851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18783489414165814318682269 7043808530312180369505851)
          ·
            refine ⟨10565712795468270554258777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043808530312180369505851 10565712795468270554258777)
            ·
              refine ⟨7924284596601202915694083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10565712795468270554258777 7924284596601202915694083)
              ·
                refine ⟨11886426894901804373541125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924284596601202915694083 11886426894901804373541125)
                ·
                  refine ⟨2228705042794088320038961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11886426894901804373541125 2228705042794088320038961)
                  ·
                    refine ⟨1671528782095566240029221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2228705042794088320038961 1671528782095566240029221)
                    ·
                      refine ⟨313411646642918670005479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1671528782095566240029221 313411646642918670005479)
                      ·
                        rfl

theorem cell23_610367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_610367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610367 prefixEnd_610367 := by exact prefixLift 610367
  have htrace : WordTrace (prefixWord ++ tailWord_610367) baseStart_610367 baseEnd_610367 := by
    simpa [prefixWord, tailWord_610367, baseEnd_610367] using wordTrace_append hprefix tailTrace_610367
  have hstable : (prefixWord ++ tailWord_610367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610367).length < 2 ^ (prefixWord ++ tailWord_610367).sum := by decide
  have hdescent : baseEnd_610367 < baseStart_610367 := by decide
  rcases family_descends (prefixWord ++ tailWord_610367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610417 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_610417 : Nat := 118140960795 + 610417 * 2 ^ 59
def prefixEnd_610417 : Nat := 4983230072969 + 3 ^ 40 * 610417 * 2
def baseEnd_610417 : Nat := 313437320675643474380249

theorem tailTrace_610417 : CollatzResearch.WordTrace tailWord_610417 prefixEnd_610417 313437320675643474380249 := by
  unfold tailWord_610417
  simp only [CollatzResearch.WordTrace]
  refine ⟨22263737029570934768869505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14842491353047289845913003 22263737029570934768869505)
  ·
    refine ⟨16697802772178201076652129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22263737029570934768869505 16697802772178201076652129)
    ·
      refine ⟨12523352079133650807489097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16697802772178201076652129 12523352079133650807489097)
      ·
        refine ⟨9392514059350238105616823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12523352079133650807489097 9392514059350238105616823)
        ·
          refine ⟨14088771089025357158425235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392514059350238105616823 14088771089025357158425235)
          ·
            refine ⟨21133156633538035737637853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14088771089025357158425235 21133156633538035737637853)
            ·
              refine ⟨7924933737576763401614195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21133156633538035737637853 7924933737576763401614195)
              ·
                refine ⟨11887400606365145102421293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924933737576763401614195 11887400606365145102421293)
                ·
                  refine ⟨4457775227386929413407985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11887400606365145102421293 4457775227386929413407985)
                  ·
                    refine ⟨3343331420540197060055989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4457775227386929413407985 3343331420540197060055989)
                    ·
                      refine ⟨313437320675643474380249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3343331420540197060055989 313437320675643474380249)
                      ·
                        rfl

theorem cell23_610417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_610417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610417 prefixEnd_610417 := by exact prefixLift 610417
  have htrace : WordTrace (prefixWord ++ tailWord_610417) baseStart_610417 baseEnd_610417 := by
    simpa [prefixWord, tailWord_610417, baseEnd_610417] using wordTrace_append hprefix tailTrace_610417
  have hstable : (prefixWord ++ tailWord_610417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610417).length < 2 ^ (prefixWord ++ tailWord_610417).sum := by decide
  have hdescent : baseEnd_610417 < baseStart_610417 := by decide
  rcases family_descends (prefixWord ++ tailWord_610417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610427 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_610427 : Nat := 118140960795 + 610427 * 2 ^ 59
def prefixEnd_610427 : Nat := 4983230072969 + 3 ^ 40 * 610427 * 2
def baseEnd_610427 : Nat := 313442455482188435255203

theorem tailTrace_610427 : CollatzResearch.WordTrace tailWord_610427 prefixEnd_610427 313442455482188435255203 := by
  unfold tailWord_610427
  simp only [CollatzResearch.WordTrace]
  refine ⟨22264101759534706476733535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14842734506356470984489023 22264101759534706476733535)
  ·
    refine ⟨33396152639302059715100303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22264101759534706476733535 33396152639302059715100303)
    ·
      refine ⟨50094228958953089572650455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33396152639302059715100303 50094228958953089572650455)
      ·
        refine ⟨75141343438429634358975683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50094228958953089572650455 75141343438429634358975683)
        ·
          refine ⟨112712015157644451538463525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75141343438429634358975683 112712015157644451538463525)
          ·
            refine ⟨21133502842058334663461911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112712015157644451538463525 21133502842058334663461911)
            ·
              refine ⟨31700254263087501995192867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21133502842058334663461911 31700254263087501995192867)
              ·
                refine ⟨47550381394631252992789301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31700254263087501995192867 47550381394631252992789301)
                ·
                  refine ⟨4457848255746679968073997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47550381394631252992789301 4457848255746679968073997)
                  ·
                    refine ⟨1671693095905004988027749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4457848255746679968073997 1671693095905004988027749)
                    ·
                      refine ⟨313442455482188435255203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1671693095905004988027749 313442455482188435255203)
                      ·
                        rfl

theorem cell23_610427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_610427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610427 prefixEnd_610427 := by exact prefixLift 610427
  have htrace : WordTrace (prefixWord ++ tailWord_610427) baseStart_610427 baseEnd_610427 := by
    simpa [prefixWord, tailWord_610427, baseEnd_610427] using wordTrace_append hprefix tailTrace_610427
  have hstable : (prefixWord ++ tailWord_610427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610427).length < 2 ^ (prefixWord ++ tailWord_610427).sum := by decide
  have hdescent : baseEnd_610427 < baseStart_610427 := by decide
  rcases family_descends (prefixWord ++ tailWord_610427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610428 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 5]
def baseStart_610428 : Nat := 118140960795 + 610428 * 2 ^ 59
def prefixEnd_610428 : Nat := 4983230072969 + 3 ^ 40 * 610428 * 2
def baseEnd_610428 : Nat := 34826996551426992371411

theorem tailTrace_610428 : CollatzResearch.WordTrace tailWord_610428 prefixEnd_610428 34826996551426992371411 := by
  unfold tailWord_610428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11132069116265541823759969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14842758821687389098346625 11132069116265541823759969)
  ·
    refine ⟨8349051837199156367819977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11132069116265541823759969 8349051837199156367819977)
    ·
      refine ⟨6261788877899367275864983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8349051837199156367819977 6261788877899367275864983)
      ·
        refine ⟨9392683316849050913797475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261788877899367275864983 9392683316849050913797475)
        ·
          refine ⟨14089024975273576370696213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392683316849050913797475 14089024975273576370696213)
          ·
            refine ⟨660423045715948892376385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14089024975273576370696213 660423045715948892376385)
            ·
              refine ⟨495317284286961669282289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660423045715948892376385 495317284286961669282289)
              ·
                refine ⟨371487963215221251961717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495317284286961669282289 371487963215221251961717)
                ·
                  refine ⟨34826996551426992371411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371487963215221251961717 34826996551426992371411)
                  ·
                    rfl

theorem cell23_610428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_610428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610428 prefixEnd_610428 := by exact prefixLift 610428
  have htrace : WordTrace (prefixWord ++ tailWord_610428) baseStart_610428 baseEnd_610428 := by
    simpa [prefixWord, tailWord_610428, baseEnd_610428] using wordTrace_append hprefix tailTrace_610428
  have hstable : (prefixWord ++ tailWord_610428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610428).length < 2 ^ (prefixWord ++ tailWord_610428).sum := by decide
  have hdescent : baseEnd_610428 < baseStart_610428 := by decide
  rcases family_descends (prefixWord ++ tailWord_610428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610457 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_610457 : Nat := 118140960795 + 610457 * 2 ^ 59
def prefixEnd_610457 : Nat := 4983230072969 + 3 ^ 40 * 610457 * 2
def baseEnd_610457 : Nat := 313457859901823317880065

theorem tailTrace_610457 : CollatzResearch.WordTrace tailWord_610457 prefixEnd_610457 313457859901823317880065 := by
  unfold tailWord_610457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22265195949426021600325625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14843463966284014400217083 22265195949426021600325625)
  ·
    refine ⟨16698896962069516200244219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22265195949426021600325625 16698896962069516200244219)
    ·
      refine ⟨25048345443104274300366329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16698896962069516200244219 25048345443104274300366329)
      ·
        refine ⟨18786259082328205725274747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25048345443104274300366329 18786259082328205725274747)
        ·
          refine ⟨28179388623492308587912121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18786259082328205725274747 28179388623492308587912121)
          ·
            refine ⟨21134541467619231440934091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28179388623492308587912121 21134541467619231440934091)
            ·
              refine ⟨31701812201428847161401137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21134541467619231440934091 31701812201428847161401137)
              ·
                refine ⟨23776359151071635371050853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31701812201428847161401137 23776359151071635371050853)
                ·
                  refine ⟨4458067340825931632072035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23776359151071635371050853 4458067340825931632072035)
                  ·
                    refine ⟨6687101011238897448108053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458067340825931632072035 6687101011238897448108053)
                    ·
                      refine ⟨313457859901823317880065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6687101011238897448108053 313457859901823317880065)
                      ·
                        rfl

theorem cell23_610457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_610457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610457 prefixEnd_610457 := by exact prefixLift 610457
  have htrace : WordTrace (prefixWord ++ tailWord_610457) baseStart_610457 baseEnd_610457 := by
    simpa [prefixWord, tailWord_610457, baseEnd_610457] using wordTrace_append hprefix tailTrace_610457
  have hstable : (prefixWord ++ tailWord_610457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610457).length < 2 ^ (prefixWord ++ tailWord_610457).sum := by decide
  have hdescent : baseEnd_610457 < baseStart_610457 := by decide
  rcases family_descends (prefixWord ++ tailWord_610457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610458 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_610458 : Nat := 118140960795 + 610458 * 2 ^ 59
def prefixEnd_610458 : Nat := 4983230072969 + 3 ^ 40 * 610458 * 2
def baseEnd_610458 : Nat := 104486124460825937989187

theorem tailTrace_610458 : CollatzResearch.WordTrace tailWord_610458 prefixEnd_610458 104486124460825937989187 := by
  unfold tailWord_610458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566308105605599692778007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14843488281614932514074685 5566308105605599692778007)
  ·
    refine ⟨8349462158408399539167011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5566308105605599692778007 8349462158408399539167011)
    ·
      refine ⟨12524193237612599308750517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349462158408399539167011 12524193237612599308750517)
      ·
        refine ⟨1174143116026181185195361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12524193237612599308750517 1174143116026181185195361)
        ·
          refine ⟨880607337019635888896521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174143116026181185195361 880607337019635888896521)
          ·
            refine ⟨660455502764726916672391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880607337019635888896521 660455502764726916672391)
            ·
              refine ⟨990683254147090375008587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660455502764726916672391 990683254147090375008587)
              ·
                refine ⟨1486024881220635562512881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990683254147090375008587 1486024881220635562512881)
                ·
                  refine ⟨1114518660915476671884661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486024881220635562512881 1114518660915476671884661)
                  ·
                    refine ⟨104486124460825937989187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1114518660915476671884661 104486124460825937989187)
                    ·
                      rfl

theorem cell23_610458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_610458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610458 prefixEnd_610458 := by exact prefixLift 610458
  have htrace : WordTrace (prefixWord ++ tailWord_610458) baseStart_610458 baseEnd_610458 := by
    simpa [prefixWord, tailWord_610458, baseEnd_610458] using wordTrace_append hprefix tailTrace_610458
  have hstable : (prefixWord ++ tailWord_610458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610458).length < 2 ^ (prefixWord ++ tailWord_610458).sum := by decide
  have hdescent : baseEnd_610458 < baseStart_610458 := by decide
  rcases family_descends (prefixWord ++ tailWord_610458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610461 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_610461 : Nat := 118140960795 + 610461 * 2 ^ 59
def prefixEnd_610461 : Nat := 4983230072969 + 3 ^ 40 * 610461 * 2
def baseEnd_610461 : Nat := 313459913824441302230047

theorem tailTrace_610461 : CollatzResearch.WordTrace tailWord_610461 prefixEnd_610461 313459913824441302230047 := by
  unfold tailWord_610461
  simp only [CollatzResearch.WordTrace]
  refine ⟨22265341841411530283471237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14843561227607686855647491 22265341841411530283471237)
  ·
    refine ⟨4174751595264661928150857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22265341841411530283471237 4174751595264661928150857)
    ·
      refine ⟨3131063696448496446113143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4174751595264661928150857 3131063696448496446113143)
      ·
        refine ⟨4696595544672744669169715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131063696448496446113143 4696595544672744669169715)
        ·
          refine ⟨7044893317009117003754573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696595544672744669169715 7044893317009117003754573)
          ·
            refine ⟨2641834993878418876407965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7044893317009117003754573 2641834993878418876407965)
            ·
              refine ⟨990688122704407078652987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2641834993878418876407965 990688122704407078652987)
              ·
                refine ⟨1486032184056610617979481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990688122704407078652987 1486032184056610617979481)
                ·
                  refine ⟨1114524138042457963484611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486032184056610617979481 1114524138042457963484611)
                  ·
                    refine ⟨1671786207063686945226917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114524138042457963484611 1671786207063686945226917)
                    ·
                      refine ⟨313459913824441302230047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1671786207063686945226917 313459913824441302230047)
                      ·
                        rfl

theorem cell23_610461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_610461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610461 prefixEnd_610461 := by exact prefixLift 610461
  have htrace : WordTrace (prefixWord ++ tailWord_610461) baseStart_610461 baseEnd_610461 := by
    simpa [prefixWord, tailWord_610461, baseEnd_610461] using wordTrace_append hprefix tailTrace_610461
  have hstable : (prefixWord ++ tailWord_610461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610461).length < 2 ^ (prefixWord ++ tailWord_610461).sum := by decide
  have hdescent : baseEnd_610461 < baseStart_610461 := by decide
  rcases family_descends (prefixWord ++ tailWord_610461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610511 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_610511 : Nat := 118140960795 + 610511 * 2 ^ 59
def prefixEnd_610511 : Nat := 4983230072969 + 3 ^ 40 * 610511 * 2
def baseEnd_610511 : Nat := 313485587857166106604817

theorem tailTrace_610511 : CollatzResearch.WordTrace tailWord_610511 prefixEnd_610511 313485587857166106604817 := by
  unfold tailWord_610511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22267165491230388822791387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14844776994153592548527591 22267165491230388822791387)
  ·
    refine ⟨33400748236845583234187081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22267165491230388822791387 33400748236845583234187081)
    ·
      refine ⟨25050561177634187425640311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33400748236845583234187081 25050561177634187425640311)
      ·
        refine ⟨37575841766451281138460467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25050561177634187425640311 37575841766451281138460467)
        ·
          refine ⟨56363762649676921707690701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37575841766451281138460467 56363762649676921707690701)
          ·
            refine ⟨21136410993628845640384013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56363762649676921707690701 21136410993628845640384013)
            ·
              refine ⟨7926154122610817115144005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21136410993628845640384013 7926154122610817115144005)
              ·
                refine ⟨1486153897989528209089501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7926154122610817115144005 1486153897989528209089501)
                ·
                  refine ⟨557307711746073078408563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1486153897989528209089501 557307711746073078408563)
                  ·
                    refine ⟨835961567619109617612845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 557307711746073078408563 835961567619109617612845)
                    ·
                      refine ⟨313485587857166106604817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 835961567619109617612845 313485587857166106604817)
                      ·
                        rfl

theorem cell23_610511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_610511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610511 prefixEnd_610511 := by exact prefixLift 610511
  have htrace : WordTrace (prefixWord ++ tailWord_610511) baseStart_610511 baseEnd_610511 := by
    simpa [prefixWord, tailWord_610511, baseEnd_610511] using wordTrace_append hprefix tailTrace_610511
  have hstable : (prefixWord ++ tailWord_610511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610511).length < 2 ^ (prefixWord ++ tailWord_610511).sum := by decide
  have hdescent : baseEnd_610511 < baseStart_610511 := by decide
  rcases family_descends (prefixWord ++ tailWord_610511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610521 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 5, 2]
def baseStart_610521 : Nat := 118140960795 + 610521 * 2 ^ 59
def prefixEnd_610521 : Nat := 4983230072969 + 3 ^ 40 * 610521 * 2
def baseEnd_610521 : Nat := 313490722663711067479771

theorem tailTrace_610521 : CollatzResearch.WordTrace tailWord_610521 prefixEnd_610521 313490722663711067479771 := by
  unfold tailWord_610521
  simp only [CollatzResearch.WordTrace]
  refine ⟨22267530221194160530655417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14845020147462773687103611 22267530221194160530655417)
  ·
    refine ⟨16700647665895620397991563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22267530221194160530655417 16700647665895620397991563)
    ·
      refine ⟨25050971498843430596987345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16700647665895620397991563 25050971498843430596987345)
      ·
        refine ⟨18788228624132572947740509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25050971498843430596987345 18788228624132572947740509)
        ·
          refine ⟨7045585734049714855402691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18788228624132572947740509 7045585734049714855402691)
          ·
            refine ⟨10568378601074572283104037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045585734049714855402691 10568378601074572283104037)
            ·
              refine ⟨1981570987701482303082007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10568378601074572283104037 1981570987701482303082007)
              ·
                refine ⟨2972356481552223454623011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981570987701482303082007 2972356481552223454623011)
                ·
                  refine ⟨4458534722328335181934517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972356481552223454623011 4458534722328335181934517)
                  ·
                    refine ⟨417987630218281423306361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4458534722328335181934517 417987630218281423306361)
                    ·
                      refine ⟨313490722663711067479771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417987630218281423306361 313490722663711067479771)
                      ·
                        rfl

theorem cell23_610521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_610521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610521 prefixEnd_610521 := by exact prefixLift 610521
  have htrace : WordTrace (prefixWord ++ tailWord_610521) baseStart_610521 baseEnd_610521 := by
    simpa [prefixWord, tailWord_610521, baseEnd_610521] using wordTrace_append hprefix tailTrace_610521
  have hstable : (prefixWord ++ tailWord_610521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610521).length < 2 ^ (prefixWord ++ tailWord_610521).sum := by decide
  have hdescent : baseEnd_610521 < baseStart_610521 := by decide
  rcases family_descends (prefixWord ++ tailWord_610521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610538 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_610538 : Nat := 118140960795 + 610538 * 2 ^ 59
def prefixEnd_610538 : Nat := 4983230072969 + 3 ^ 40 * 610538 * 2
def baseEnd_610538 : Nat := 313499451834837500967193

theorem tailTrace_610538 : CollatzResearch.WordTrace tailWord_610538 prefixEnd_610538 313499451834837500967193 := by
  unfold tailWord_610538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567037565533143108506067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14845433508088381622682845 5567037565533143108506067)
  ·
    refine ⟨8350556348299714662759101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567037565533143108506067 8350556348299714662759101)
    ·
      refine ⟨3131458630612392998534663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8350556348299714662759101 3131458630612392998534663)
      ·
        refine ⟨4697187945918589497801995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131458630612392998534663 4697187945918589497801995)
        ·
          refine ⟨7045781918877884246702993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697187945918589497801995 7045781918877884246702993)
          ·
            refine ⟨5284336439158413185027245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7045781918877884246702993 5284336439158413185027245)
            ·
              refine ⟨1981626164684404944385217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5284336439158413185027245 1981626164684404944385217)
              ·
                refine ⟨1486219623513303708288913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981626164684404944385217 1486219623513303708288913)
                ·
                  refine ⟨1114664717634977781216685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486219623513303708288913 1114664717634977781216685)
                  ·
                    refine ⟨417999269113116667956257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114664717634977781216685 417999269113116667956257)
                    ·
                      refine ⟨313499451834837500967193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417999269113116667956257 313499451834837500967193)
                      ·
                        rfl

theorem cell23_610538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_610538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610538 prefixEnd_610538 := by exact prefixLift 610538
  have htrace : WordTrace (prefixWord ++ tailWord_610538) baseStart_610538 baseEnd_610538 := by
    simpa [prefixWord, tailWord_610538, baseEnd_610538] using wordTrace_append hprefix tailTrace_610538
  have hstable : (prefixWord ++ tailWord_610538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610538).length < 2 ^ (prefixWord ++ tailWord_610538).sum := by decide
  have hdescent : baseEnd_610538 < baseStart_610538 := by decide
  rcases family_descends (prefixWord ++ tailWord_610538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610568 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_610568 : Nat := 118140960795 + 610568 * 2 ^ 59
def prefixEnd_610568 : Nat := 4983230072969 + 3 ^ 40 * 610568 * 2
def baseEnd_610568 : Nat := 313514856254472383592055

theorem tailTrace_610568 : CollatzResearch.WordTrace tailWord_610568 prefixEnd_610568 313514856254472383592055 := by
  unfold tailWord_610568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134622226011943778808179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14846162968015925038410905 11134622226011943778808179)
  ·
    refine ⟨16701933339017915668212269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134622226011943778808179 16701933339017915668212269)
    ·
      refine ⟨6263225002131718375579601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16701933339017915668212269 6263225002131718375579601)
      ·
        refine ⟨4697418751598788781684701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6263225002131718375579601 4697418751598788781684701)
        ·
          refine ⟨1761532031849545793131763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4697418751598788781684701 1761532031849545793131763)
          ·
            refine ⟨2642298047774318689697645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761532031849545793131763 2642298047774318689697645)
            ·
              refine ⟨990861767915369508636617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2642298047774318689697645 990861767915369508636617)
              ·
                refine ⟨743146325936527131477463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990861767915369508636617 743146325936527131477463)
                ·
                  refine ⟨1114719488904790697216195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743146325936527131477463 1114719488904790697216195)
                  ·
                    refine ⟨1672079233357186045824293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1114719488904790697216195 1672079233357186045824293)
                    ·
                      refine ⟨313514856254472383592055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1672079233357186045824293 313514856254472383592055)
                      ·
                        rfl

theorem cell23_610568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_610568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610568 prefixEnd_610568 := by exact prefixLift 610568
  have htrace : WordTrace (prefixWord ++ tailWord_610568) baseStart_610568 baseEnd_610568 := by
    simpa [prefixWord, tailWord_610568, baseEnd_610568] using wordTrace_append hprefix tailTrace_610568
  have hstable : (prefixWord ++ tailWord_610568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610568).length < 2 ^ (prefixWord ++ tailWord_610568).sum := by decide
  have hdescent : baseEnd_610568 < baseStart_610568 := by decide
  rcases family_descends (prefixWord ++ tailWord_610568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610571 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3]
def baseStart_610571 : Nat := 118140960795 + 610571 * 2 ^ 59
def prefixEnd_610571 : Nat := 4983230072969 + 3 ^ 40 * 610571 * 2
def baseEnd_610571 : Nat := 313516396696435871854541

theorem tailTrace_610571 : CollatzResearch.WordTrace tailWord_610571 prefixEnd_610571 313516396696435871854541 := by
  unfold tailWord_610571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269353871013019069975567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14846235914008679379983711 22269353871013019069975567)
  ·
    refine ⟨33404030806519528604963351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22269353871013019069975567 33404030806519528604963351)
    ·
      refine ⟨50106046209779292907445027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33404030806519528604963351 50106046209779292907445027)
      ·
        refine ⟨75159069314668939361167541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50106046209779292907445027 75159069314668939361167541)
        ·
          refine ⟨7046162748250213065109457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75159069314668939361167541 7046162748250213065109457)
          ·
            refine ⟨5284622061187659798832093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046162748250213065109457 5284622061187659798832093)
            ·
              refine ⟨1981733272945372424562035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5284622061187659798832093 1981733272945372424562035)
              ·
                refine ⟨2972599909418058636843053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981733272945372424562035 2972599909418058636843053)
                ·
                  refine ⟨1114724966031771988816145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2972599909418058636843053 1114724966031771988816145)
                  ·
                    refine ⟨836043724523828991612109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114724966031771988816145 836043724523828991612109)
                    ·
                      refine ⟨313516396696435871854541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836043724523828991612109 313516396696435871854541)
                      ·
                        rfl

theorem cell23_610571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].length) (baseStart_610571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610571 prefixEnd_610571 := by exact prefixLift 610571
  have htrace : WordTrace (prefixWord ++ tailWord_610571) baseStart_610571 baseEnd_610571 := by
    simpa [prefixWord, tailWord_610571, baseEnd_610571] using wordTrace_append hprefix tailTrace_610571
  have hstable : (prefixWord ++ tailWord_610571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610571).length < 2 ^ (prefixWord ++ tailWord_610571).sum := by decide
  have hdescent : baseEnd_610571 < baseStart_610571 := by decide
  rcases family_descends (prefixWord ++ tailWord_610571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610574 : List Nat := [4, 1, 1, 2, 1, 2, 1, 11]
def baseStart_610574 : Nat := 118140960795 + 610574 * 2 ^ 59
def prefixEnd_610574 : Nat := 4983230072969 + 3 ^ 40 * 610574 * 2
def baseEnd_610574 : Nat := 11611775449570346671001

theorem tailTrace_610574 : CollatzResearch.WordTrace tailWord_610574 prefixEnd_610574 11611775449570346671001 := by
  unfold tailWord_610574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783682911250268822791847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14846308860001433721556517 2783682911250268822791847)
  ·
    refine ⟨4175524366875403234187771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783682911250268822791847 4175524366875403234187771)
    ·
      refine ⟨6263286550313104851281657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175524366875403234187771 6263286550313104851281657)
      ·
        refine ⟨4697464912734828638461243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6263286550313104851281657 4697464912734828638461243)
        ·
          refine ⟨7046197369102242957691865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697464912734828638461243 7046197369102242957691865)
          ·
            refine ⟨5284648026826682218268899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046197369102242957691865 5284648026826682218268899)
            ·
              refine ⟨7926972040240023327403349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284648026826682218268899 7926972040240023327403349)
              ·
                refine ⟨11611775449570346671001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7926972040240023327403349 11611775449570346671001)
                ·
                  rfl

theorem cell23_610574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_610574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610574 prefixEnd_610574 := by exact prefixLift 610574
  have htrace : WordTrace (prefixWord ++ tailWord_610574) baseStart_610574 baseEnd_610574 := by
    simpa [prefixWord, tailWord_610574, baseEnd_610574] using wordTrace_append hprefix tailTrace_610574
  have hstable : (prefixWord ++ tailWord_610574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610574).length < 2 ^ (prefixWord ++ tailWord_610574).sum := by decide
  have hdescent : baseEnd_610574 < baseStart_610574 := by decide
  rcases family_descends (prefixWord ++ tailWord_610574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610604 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_610604 : Nat := 118140960795 + 610604 * 2 ^ 59
def prefixEnd_610604 : Nat := 4983230072969 + 3 ^ 40 * 610604 * 2
def baseEnd_610604 : Nat := 104511113852678080913963

theorem tailTrace_610604 : CollatzResearch.WordTrace tailWord_610604 prefixEnd_610604 104511113852678080913963 := by
  unfold tailWord_610604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11135278739946732852963433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14847038319928977137284577 11135278739946732852963433)
  ·
    refine ⟨8351459054960049639722575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11135278739946732852963433 8351459054960049639722575)
    ·
      refine ⟨12527188582440074459583863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351459054960049639722575 12527188582440074459583863)
      ·
        refine ⟨18790782873660111689375795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527188582440074459583863 18790782873660111689375795)
        ·
          refine ⟨28186174310490167534063693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18790782873660111689375795 28186174310490167534063693)
          ·
            refine ⟨10569815366433812825273885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28186174310490167534063693 10569815366433812825273885)
            ·
              refine ⟨3963680762412679809477707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10569815366433812825273885 3963680762412679809477707)
              ·
                refine ⟨5945521143619019714216561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963680762412679809477707 5945521143619019714216561)
                ·
                  refine ⟨4459140857714264785662421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5945521143619019714216561 4459140857714264785662421)
                  ·
                    refine ⟨104511113852678080913963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4459140857714264785662421 104511113852678080913963)
                    ·
                      rfl

theorem cell23_610604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_610604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610604 prefixEnd_610604 := by exact prefixLift 610604
  have htrace : WordTrace (prefixWord ++ tailWord_610604) baseStart_610604 baseEnd_610604 := by
    simpa [prefixWord, tailWord_610604, baseEnd_610604] using wordTrace_append hprefix tailTrace_610604
  have hstable : (prefixWord ++ tailWord_610604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610604).length < 2 ^ (prefixWord ++ tailWord_610604).sum := by decide
  have hdescent : baseEnd_610604 < baseStart_610604 := by decide
  rcases family_descends (prefixWord ++ tailWord_610604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610618 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_610618 : Nat := 118140960795 + 610618 * 2 ^ 59
def prefixEnd_610618 : Nat := 4983230072969 + 3 ^ 40 * 610618 * 2
def baseEnd_610618 : Nat := 313540530287197187966825

theorem tailTrace_610618 : CollatzResearch.WordTrace tailWord_610618 prefixEnd_610618 313540530287197187966825 := by
  unfold tailWord_610618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567767025460686524234127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14847378734561830731291005 5567767025460686524234127)
  ·
    refine ⟨8351650538191029786351191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567767025460686524234127 8351650538191029786351191)
    ·
      refine ⟨12527475807286544679526787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351650538191029786351191 12527475807286544679526787)
      ·
        refine ⟨18791213710929817019290181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527475807286544679526787 18791213710929817019290181)
        ·
          refine ⟨3523352570799340691116909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18791213710929817019290181 3523352570799340691116909)
          ·
            refine ⟨1321257214049752759168841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3523352570799340691116909 1321257214049752759168841)
            ·
              refine ⟨990942910537314569376631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321257214049752759168841 990942910537314569376631)
              ·
                refine ⟨1486414365805971854064947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990942910537314569376631 1486414365805971854064947)
                ·
                  refine ⟨2229621548708957781097421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486414365805971854064947 2229621548708957781097421)
                  ·
                    refine ⟨836108080765859167911533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229621548708957781097421 836108080765859167911533)
                    ·
                      refine ⟨313540530287197187966825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836108080765859167911533 313540530287197187966825)
                      ·
                        rfl

theorem cell23_610618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_610618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610618 prefixEnd_610618 := by exact prefixLift 610618
  have htrace : WordTrace (prefixWord ++ tailWord_610618) baseStart_610618 baseEnd_610618 := by
    simpa [prefixWord, tailWord_610618, baseEnd_610618] using wordTrace_append hprefix tailTrace_610618
  have hstable : (prefixWord ++ tailWord_610618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610618).length < 2 ^ (prefixWord ++ tailWord_610618).sum := by decide
  have hdescent : baseEnd_610618 < baseStart_610618 := by decide
  rcases family_descends (prefixWord ++ tailWord_610618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610652 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_610652 : Nat := 118140960795 + 610652 * 2 ^ 59
def prefixEnd_610652 : Nat := 4983230072969 + 3 ^ 40 * 610652 * 2
def baseEnd_610652 : Nat := 313557988629450054941669

theorem tailTrace_610652 : CollatzResearch.WordTrace tailWord_610652 prefixEnd_610652 313557988629450054941669 := by
  unfold tailWord_610652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136154091859784951837105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14848205455813046602449473 11136154091859784951837105)
  ·
    refine ⟨8352115568894838713877829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11136154091859784951837105 8352115568894838713877829)
    ·
      refine ⟨1566021669167782258852093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8352115568894838713877829 1566021669167782258852093)
      ·
        refine ⟨587258125937918347069535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1566021669167782258852093 587258125937918347069535)
        ·
          refine ⟨880887188906877520604303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587258125937918347069535 880887188906877520604303)
          ·
            refine ⟨1321330783360316280906455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880887188906877520604303 1321330783360316280906455)
            ·
              refine ⟨1981996175040474421359683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321330783360316280906455 1981996175040474421359683)
              ·
                refine ⟨2972994262560711632039525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981996175040474421359683 2972994262560711632039525)
                ·
                  refine ⟨557436424230133431007411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2972994262560711632039525 557436424230133431007411)
                  ·
                    refine ⟨836154636345200146511117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 557436424230133431007411 836154636345200146511117)
                    ·
                      refine ⟨313557988629450054941669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836154636345200146511117 313557988629450054941669)
                      ·
                        rfl

theorem cell23_610652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_610652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610652 prefixEnd_610652 := by exact prefixLift 610652
  have htrace : WordTrace (prefixWord ++ tailWord_610652) baseStart_610652 baseEnd_610652 := by
    simpa [prefixWord, tailWord_610652, baseEnd_610652] using wordTrace_append hprefix tailTrace_610652
  have hstable : (prefixWord ++ tailWord_610652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610652).length < 2 ^ (prefixWord ++ tailWord_610652).sum := by decide
  have hdescent : baseEnd_610652 < baseStart_610652 := by decide
  rcases family_descends (prefixWord ++ tailWord_610652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610711 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 4, 5]
def baseStart_610711 : Nat := 118140960795 + 610711 * 2 ^ 59
def prefixEnd_610711 : Nat := 4983230072969 + 3 ^ 40 * 610711 * 2
def baseEnd_610711 : Nat := 104529427996021774701299

theorem tailTrace_610711 : CollatzResearch.WordTrace tailWord_610711 prefixEnd_610711 104529427996021774701299 := by
  unfold tailWord_610711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22274460090505822980071987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14849640060337215320047991 22274460090505822980071987)
  ·
    refine ⟨33411690135758734470107981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22274460090505822980071987 33411690135758734470107981)
    ·
      refine ⟨12529383800909525426290493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33411690135758734470107981 12529383800909525426290493)
      ·
        refine ⟨4698518925341072034858935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12529383800909525426290493 4698518925341072034858935)
        ·
          refine ⟨7047778388011608052288403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698518925341072034858935 7047778388011608052288403)
          ·
            refine ⟨10571667582017412078432605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047778388011608052288403 10571667582017412078432605)
            ·
              refine ⟨3964375343256529529412227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10571667582017412078432605 3964375343256529529412227)
              ·
                refine ⟨5946563014884794294118341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964375343256529529412227 5946563014884794294118341)
                ·
                  refine ⟨1114980565290898930147189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5946563014884794294118341 1114980565290898930147189)
                  ·
                    refine ⟨104529427996021774701299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1114980565290898930147189 104529427996021774701299)
                    ·
                      rfl

theorem cell23_610711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_610711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610711 prefixEnd_610711 := by exact prefixLift 610711
  have htrace : WordTrace (prefixWord ++ tailWord_610711) baseStart_610711 baseEnd_610711 := by
    simpa [prefixWord, tailWord_610711, baseEnd_610711] using wordTrace_append hprefix tailTrace_610711
  have hstable : (prefixWord ++ tailWord_610711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610711).length < 2 ^ (prefixWord ++ tailWord_610711).sum := by decide
  have hdescent : baseEnd_610711 < baseStart_610711 := by decide
  rcases family_descends (prefixWord ++ tailWord_610711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610831 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 6]
def baseStart_610831 : Nat := 118140960795 + 610831 * 2 ^ 59
def prefixEnd_610831 : Nat := 4983230072969 + 3 ^ 40 * 610831 * 2
def baseEnd_610831 : Nat := 104549967222201618201115

theorem tailTrace_610831 : CollatzResearch.WordTrace tailWord_610831 prefixEnd_610831 104549967222201618201115 := by
  unfold tailWord_610831
  simp only [CollatzResearch.WordTrace]
  refine ⟨22278836850071083474440347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14852557900047388982960231 22278836850071083474440347)
  ·
    refine ⟨33418255275106625211660521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22278836850071083474440347 33418255275106625211660521)
    ·
      refine ⟨25063691456329968908745391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33418255275106625211660521 25063691456329968908745391)
      ·
        refine ⟨37595537184494953363118087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25063691456329968908745391 37595537184494953363118087)
        ·
          refine ⟨56393305776742430044677131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37595537184494953363118087 56393305776742430044677131)
          ·
            refine ⟨84589958665113645067015697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56393305776742430044677131 84589958665113645067015697)
            ·
              refine ⟨63442468998835233800261773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84589958665113645067015697 63442468998835233800261773)
              ·
                refine ⟨23790925874563212675098165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63442468998835233800261773 23790925874563212675098165)
                ·
                  refine ⟨2230399300740301188290453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23790925874563212675098165 2230399300740301188290453)
                  ·
                    refine ⟨104549967222201618201115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2230399300740301188290453 104549967222201618201115)
                    ·
                      rfl

theorem cell23_610831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_610831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610831 prefixEnd_610831 := by exact prefixLift 610831
  have htrace : WordTrace (prefixWord ++ tailWord_610831) baseStart_610831 baseEnd_610831 := by
    simpa [prefixWord, tailWord_610831, baseEnd_610831] using wordTrace_append hprefix tailTrace_610831
  have hstable : (prefixWord ++ tailWord_610831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610831).length < 2 ^ (prefixWord ++ tailWord_610831).sum := by decide
  have hdescent : baseEnd_610831 < baseStart_610831 := by decide
  rcases family_descends (prefixWord ++ tailWord_610831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610898 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_610898 : Nat := 118140960795 + 610898 * 2 ^ 59
def prefixEnd_610898 : Nat := 4983230072969 + 3 ^ 40 * 610898 * 2
def baseEnd_610898 : Nat := 313684304870456092465537

theorem tailTrace_610898 : CollatzResearch.WordTrace tailWord_610898 prefixEnd_610898 313684304870456092465537 := by
  unfold tailWord_610898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570320135207088479282337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14854187027218902611419565 5570320135207088479282337)
  ·
    refine ⟨4177740101405316359461753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5570320135207088479282337 4177740101405316359461753)
    ·
      refine ⟨3133305076053987269596315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4177740101405316359461753 3133305076053987269596315)
      ·
        refine ⟨4699957614080980904394473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133305076053987269596315 4699957614080980904394473)
        ·
          refine ⟨3524968210560735678295855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699957614080980904394473 3524968210560735678295855)
          ·
            refine ⟨5287452315841103517443783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524968210560735678295855 5287452315841103517443783)
            ·
              refine ⟨7931178473761655276165675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287452315841103517443783 7931178473761655276165675)
              ·
                refine ⟨11896767710642482914248513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7931178473761655276165675 11896767710642482914248513)
                ·
                  refine ⟨8922575782981862185686385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11896767710642482914248513 8922575782981862185686385)
                  ·
                    refine ⟨6691931837236396639264789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8922575782981862185686385 6691931837236396639264789)
                    ·
                      refine ⟨313684304870456092465537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6691931837236396639264789 313684304870456092465537)
                      ·
                        rfl

theorem cell23_610898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_610898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610898 prefixEnd_610898 := by exact prefixLift 610898
  have htrace : WordTrace (prefixWord ++ tailWord_610898) baseStart_610898 baseEnd_610898 := by
    simpa [prefixWord, tailWord_610898, baseEnd_610898] using wordTrace_append hprefix tailTrace_610898
  have hstable : (prefixWord ++ tailWord_610898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610898).length < 2 ^ (prefixWord ++ tailWord_610898).sum := by decide
  have hdescent : baseEnd_610898 < baseStart_610898 := by decide
  rcases family_descends (prefixWord ++ tailWord_610898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610946 : List Nat := [3, 4, 3, 1, 1, 2, 1, 8]
def baseStart_610946 : Nat := 118140960795 + 610946 * 2 ^ 59
def prefixEnd_610946 : Nat := 4983230072969 + 3 ^ 40 * 610946 * 2
def baseEnd_610946 : Nat := 11618850071921181654271

theorem tailTrace_610946 : CollatzResearch.WordTrace tailWord_610946 prefixEnd_610946 11618850071921181654271 := by
  unfold tailWord_610946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570757811163614528719173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14855354163102972076584461 5570757811163614528719173)
  ·
    refine ⟨1044517089593177724134845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5570757811163614528719173 1044517089593177724134845)
    ·
      refine ⟨391693908597441646550567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1044517089593177724134845 391693908597441646550567)
      ·
        refine ⟨587540862896162469825851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391693908597441646550567 587540862896162469825851)
        ·
          refine ⟨881311294344243704738777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587540862896162469825851 881311294344243704738777)
          ·
            refine ⟨660983470758182778554083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881311294344243704738777 660983470758182778554083)
            ·
              refine ⟨991475206137274167831125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660983470758182778554083 991475206137274167831125)
              ·
                refine ⟨11618850071921181654271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 991475206137274167831125 11618850071921181654271)
                ·
                  rfl

theorem cell23_610946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_610946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610946 prefixEnd_610946 := by exact prefixLift 610946
  have htrace : WordTrace (prefixWord ++ tailWord_610946) baseStart_610946 baseEnd_610946 := by
    simpa [prefixWord, tailWord_610946, baseEnd_610946] using wordTrace_append hprefix tailTrace_610946
  have hstable : (prefixWord ++ tailWord_610946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610946).length < 2 ^ (prefixWord ++ tailWord_610946).sum := by decide
  have hdescent : baseEnd_610946 < baseStart_610946 := by decide
  rcases family_descends (prefixWord ++ tailWord_610946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610985 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 5]
def baseStart_610985 : Nat := 118140960795 + 610985 * 2 ^ 59
def prefixEnd_610985 : Nat := 4983230072969 + 3 ^ 40 * 610985 * 2
def baseEnd_610985 : Nat := 34858775298599694675293

theorem tailTrace_610985 : CollatzResearch.WordTrace tailWord_610985 prefixEnd_610985 34858775298599694675293 := by
  unfold tailWord_610985
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284453691513167775546409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14856302461008778517030939 22284453691513167775546409)
  ·
    refine ⟨16713340268634875831659807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22284453691513167775546409 16713340268634875831659807)
    ·
      refine ⟨25070010402952313747489711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16713340268634875831659807 25070010402952313747489711)
      ·
        refine ⟨37605015604428470621234567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25070010402952313747489711 37605015604428470621234567)
        ·
          refine ⟨56407523406642705931851851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37605015604428470621234567 56407523406642705931851851)
          ·
            refine ⟨84611285109964058897777777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56407523406642705931851851 84611285109964058897777777)
            ·
              refine ⟨63458463832473044173333333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84611285109964058897777777 63458463832473044173333333)
              ·
                refine ⟨371826936518396743203125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 63458463832473044173333333 371826936518396743203125)
                ·
                  refine ⟨34858775298599694675293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371826936518396743203125 34858775298599694675293)
                  ·
                    rfl

theorem cell23_610985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 5].length) (baseStart_610985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610985 prefixEnd_610985 := by exact prefixLift 610985
  have htrace : WordTrace (prefixWord ++ tailWord_610985) baseStart_610985 baseEnd_610985 := by
    simpa [prefixWord, tailWord_610985, baseEnd_610985] using wordTrace_append hprefix tailTrace_610985
  have hstable : (prefixWord ++ tailWord_610985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610985).length < 2 ^ (prefixWord ++ tailWord_610985).sum := by decide
  have hdescent : baseEnd_610985 < baseStart_610985 := by decide
  rcases family_descends (prefixWord ++ tailWord_610985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610995 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3]
def baseStart_610995 : Nat := 118140960795 + 610995 * 2 ^ 59
def prefixEnd_610995 : Nat := 4983230072969 + 3 ^ 40 * 610995 * 2
def baseEnd_610995 : Nat := 313734112493942212952591

theorem tailTrace_610995 : CollatzResearch.WordTrace tailWord_610995 prefixEnd_610995 313734112493942212952591 := by
  unfold tailWord_610995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284818421476939483410439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14856545614317959655606959 22284818421476939483410439)
  ·
    refine ⟨33427227632215409225115659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22284818421476939483410439 33427227632215409225115659)
    ·
      refine ⟨50140841448323113837673489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33427227632215409225115659 50140841448323113837673489)
      ·
        refine ⟨37605631086242335378255117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50140841448323113837673489 37605631086242335378255117)
        ·
          refine ⟨14102111657340875766845669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37605631086242335378255117 14102111657340875766845669)
          ·
            refine ⟨2644145935751414206283563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14102111657340875766845669 2644145935751414206283563)
            ·
              refine ⟨3966218903627121309425345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644145935751414206283563 3966218903627121309425345)
              ·
                refine ⟨2974664177720340982069009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966218903627121309425345 2974664177720340982069009)
                ·
                  refine ⟨2230998133290255736551757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974664177720340982069009 2230998133290255736551757)
                  ·
                    refine ⟨836624299983845901206909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2230998133290255736551757 836624299983845901206909)
                    ·
                      refine ⟨313734112493942212952591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836624299983845901206909 313734112493942212952591)
                      ·
                        rfl

theorem cell23_610995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_610995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_610995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_610995 prefixEnd_610995 := by exact prefixLift 610995
  have htrace : WordTrace (prefixWord ++ tailWord_610995) baseStart_610995 baseEnd_610995 := by
    simpa [prefixWord, tailWord_610995, baseEnd_610995] using wordTrace_append hprefix tailTrace_610995
  have hstable : (prefixWord ++ tailWord_610995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610995).length < 2 ^ (prefixWord ++ tailWord_610995).sum := by decide
  have hdescent : baseEnd_610995 < baseStart_610995 := by decide
  rcases family_descends (prefixWord ++ tailWord_610995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611012 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_611012 : Nat := 118140960795 + 611012 * 2 ^ 59
def prefixEnd_611012 : Nat := 4983230072969 + 3 ^ 40 * 611012 * 2
def baseEnd_611012 : Nat := 313742841665068646440013

theorem tailTrace_611012 : CollatzResearch.WordTrace tailWord_611012 prefixEnd_611012 313742841665068646440013 := by
  unfold tailWord_611012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142719231207675693389645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14856958974943567591186193 11142719231207675693389645)
  ·
    refine ⟨4178519711702878385021117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11142719231207675693389645 4178519711702878385021117)
    ·
      refine ⟨1566944891888579394382919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4178519711702878385021117 1566944891888579394382919)
      ·
        refine ⟨2350417337832869091574379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566944891888579394382919 2350417337832869091574379)
        ·
          refine ⟨3525626006749303637361569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350417337832869091574379 3525626006749303637361569)
          ·
            refine ⟨2644219505061977728021177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525626006749303637361569 2644219505061977728021177)
            ·
              refine ⟨1983164628796483296015883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644219505061977728021177 1983164628796483296015883)
              ·
                refine ⟨2974746943194724944023825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983164628796483296015883 2974746943194724944023825)
                ·
                  refine ⟨2231060207396043708017869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974746943194724944023825 2231060207396043708017869)
                  ·
                    refine ⟨836647577773516390506701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231060207396043708017869 836647577773516390506701)
                    ·
                      refine ⟨313742841665068646440013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836647577773516390506701 313742841665068646440013)
                      ·
                        rfl

theorem cell23_611012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_611012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611012 prefixEnd_611012 := by exact prefixLift 611012
  have htrace : WordTrace (prefixWord ++ tailWord_611012) baseStart_611012 baseEnd_611012 := by
    simpa [prefixWord, tailWord_611012, baseEnd_611012] using wordTrace_append hprefix tailTrace_611012
  have hstable : (prefixWord ++ tailWord_611012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611012).length < 2 ^ (prefixWord ++ tailWord_611012).sum := by decide
  have hdescent : baseEnd_611012 < baseStart_611012 := by decide
  rcases family_descends (prefixWord ++ tailWord_611012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611036 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 5]
def baseStart_611036 : Nat := 118140960795 + 611036 * 2 ^ 59
def prefixEnd_611036 : Nat := 4983230072969 + 3 ^ 40 * 611036 * 2
def baseEnd_611036 : Nat := 34861685022308505837767

theorem tailTrace_611036 : CollatzResearch.WordTrace tailWord_611036 prefixEnd_611036 34861685022308505837767 := by
  unfold tailWord_611036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143156907164201742826481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14857542542885602323768641 11143156907164201742826481)
  ·
    refine ⟨8357367680373151307119861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11143156907164201742826481 8357367680373151307119861)
    ·
      refine ⟨783503220034982935042487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8357367680373151307119861 783503220034982935042487)
      ·
        refine ⟨1175254830052474402563731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783503220034982935042487 1175254830052474402563731)
        ·
          refine ⟨1762882245078711603845597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175254830052474402563731 1762882245078711603845597)
          ·
            refine ⟨661080841904516851442099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1762882245078711603845597 661080841904516851442099)
            ·
              refine ⟨991621262856775277163149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661080841904516851442099 991621262856775277163149)
              ·
                refine ⟨371857973571290728936181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991621262856775277163149 371857973571290728936181)
                ·
                  refine ⟨34861685022308505837767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371857973571290728936181 34861685022308505837767)
                  ·
                    rfl

theorem cell23_611036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_611036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611036 prefixEnd_611036 := by exact prefixLift 611036
  have htrace : WordTrace (prefixWord ++ tailWord_611036) baseStart_611036 baseEnd_611036 := by
    simpa [prefixWord, tailWord_611036, baseEnd_611036] using wordTrace_append hprefix tailTrace_611036
  have hstable : (prefixWord ++ tailWord_611036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611036).length < 2 ^ (prefixWord ++ tailWord_611036).sum := by decide
  have hdescent : baseEnd_611036 < baseStart_611036 := by decide
  rcases family_descends (prefixWord ++ tailWord_611036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611140 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_611140 : Nat := 118140960795 + 611140 * 2 ^ 59
def prefixEnd_611140 : Nat := 4983230072969 + 3 ^ 40 * 611140 * 2
def baseEnd_611140 : Nat := 313808567188844145639425

theorem tailTrace_611140 : CollatzResearch.WordTrace tailWord_611140 prefixEnd_611140 313808567188844145639425 := by
  unfold tailWord_611140
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145053502975814623719437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14860071337301086164959249 11145053502975814623719437)
  ·
    refine ⟨4179395063615930483894789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11145053502975814623719437 4179395063615930483894789)
    ·
      refine ⟨783636574427986965730273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4179395063615930483894789 783636574427986965730273)
      ·
        refine ⟨587727430820990224297705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783636574427986965730273 587727430820990224297705)
        ·
          refine ⟨440795573115742668223279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587727430820990224297705 440795573115742668223279)
          ·
            refine ⟨661193359673614002334919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440795573115742668223279 661193359673614002334919)
            ·
              refine ⟨991790039510421003502379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661193359673614002334919 991790039510421003502379)
              ·
                refine ⟨1487685059265631505253569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991790039510421003502379 1487685059265631505253569)
                ·
                  refine ⟨1115763794449223628940177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487685059265631505253569 1115763794449223628940177)
                  ·
                    refine ⟨836822845836917721705133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115763794449223628940177 836822845836917721705133)
                    ·
                      refine ⟨313808567188844145639425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836822845836917721705133 313808567188844145639425)
                      ·
                        rfl

theorem cell23_611140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_611140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611140 prefixEnd_611140 := by exact prefixLift 611140
  have htrace : WordTrace (prefixWord ++ tailWord_611140) baseStart_611140 baseEnd_611140 := by
    simpa [prefixWord, tailWord_611140, baseEnd_611140] using wordTrace_append hprefix tailTrace_611140
  have hstable : (prefixWord ++ tailWord_611140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611140).length < 2 ^ (prefixWord ++ tailWord_611140).sum := by decide
  have hdescent : baseEnd_611140 < baseStart_611140 := by decide
  rcases family_descends (prefixWord ++ tailWord_611140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611153 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_611153 : Nat := 118140960795 + 611153 * 2 ^ 59
def prefixEnd_611153 : Nat := 4983230072969 + 3 ^ 40 * 611153 * 2
def baseEnd_611153 : Nat := 313815242437352594776865

theorem tailTrace_611153 : CollatzResearch.WordTrace tailWord_611153 prefixEnd_611153 313815242437352594776865 := by
  unfold tailWord_611153
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290581154904532467662113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14860387436603021645108075 22290581154904532467662113)
  ·
    refine ⟨16717935866178399350746585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22290581154904532467662113 16717935866178399350746585)
    ·
      refine ⟨12538451899633799513059939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16717935866178399350746585 12538451899633799513059939)
      ·
        refine ⟨18807677849450699269589909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12538451899633799513059939 18807677849450699269589909)
        ·
          refine ⟨881609899193001528262027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18807677849450699269589909 881609899193001528262027)
          ·
            refine ⟨1322414848789502292393041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881609899193001528262027 1322414848789502292393041)
            ·
              refine ⟨991811136592126719294781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322414848789502292393041 991811136592126719294781)
              ·
                refine ⟨371929176222047519735543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991811136592126719294781 371929176222047519735543)
                ·
                  refine ⟨557893764333071279603315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371929176222047519735543 557893764333071279603315)
                  ·
                    refine ⟨836840646499606919404973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 557893764333071279603315 836840646499606919404973)
                    ·
                      refine ⟨313815242437352594776865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836840646499606919404973 313815242437352594776865)
                      ·
                        rfl

theorem cell23_611153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_611153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611153 prefixEnd_611153 := by exact prefixLift 611153
  have htrace : WordTrace (prefixWord ++ tailWord_611153) baseStart_611153 baseEnd_611153 := by
    simpa [prefixWord, tailWord_611153, baseEnd_611153] using wordTrace_append hprefix tailTrace_611153
  have hstable : (prefixWord ++ tailWord_611153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611153).length < 2 ^ (prefixWord ++ tailWord_611153).sum := by decide
  have hdescent : baseEnd_611153 < baseStart_611153 := by decide
  rcases family_descends (prefixWord ++ tailWord_611153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611159 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_611159 : Nat := 118140960795 + 611159 * 2 ^ 59
def prefixEnd_611159 : Nat := 4983230072969 + 3 ^ 40 * 611159 * 2
def baseEnd_611159 : Nat := 313818323321279571301837

theorem tailTrace_611159 : CollatzResearch.WordTrace tailWord_611159 prefixEnd_611159 313818323321279571301837 := by
  unfold tailWord_611159
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290799992882795492380531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14860533328588530328253687 22290799992882795492380531)
  ·
    refine ⟨33436199989324193238570797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22290799992882795492380531 33436199989324193238570797)
    ·
      refine ⟨12538574995996572464464049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33436199989324193238570797 12538574995996572464464049)
      ·
        refine ⟨9403931246997429348348037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12538574995996572464464049 9403931246997429348348037)
        ·
          refine ⟨1763237108812018002815257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9403931246997429348348037 1763237108812018002815257)
          ·
            refine ⟨1322427831609013502111443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763237108812018002815257 1322427831609013502111443)
            ·
              refine ⟨1983641747413520253167165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322427831609013502111443 1983641747413520253167165)
              ·
                refine ⟨743865655280070094937687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1983641747413520253167165 743865655280070094937687)
                ·
                  refine ⟨1115798482920105142406531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743865655280070094937687 1115798482920105142406531)
                  ·
                    refine ⟨1673697724380157713609797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1115798482920105142406531 1673697724380157713609797)
                    ·
                      refine ⟨313818323321279571301837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1673697724380157713609797 313818323321279571301837)
                      ·
                        rfl

theorem cell23_611159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_611159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611159 prefixEnd_611159 := by exact prefixLift 611159
  have htrace : WordTrace (prefixWord ++ tailWord_611159) baseStart_611159 baseEnd_611159 := by
    simpa [prefixWord, tailWord_611159, baseEnd_611159] using wordTrace_append hprefix tailTrace_611159
  have hstable : (prefixWord ++ tailWord_611159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611159).length < 2 ^ (prefixWord ++ tailWord_611159).sum := by decide
  have hdescent : baseEnd_611159 < baseStart_611159 := by decide
  rcases family_descends (prefixWord ++ tailWord_611159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611176 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_611176 : Nat := 118140960795 + 611176 * 2 ^ 59
def prefixEnd_611176 : Nat := 4983230072969 + 3 ^ 40 * 611176 * 2
def baseEnd_611176 : Nat := 313827052492406004789259

theorem tailTrace_611176 : CollatzResearch.WordTrace tailWord_611176 prefixEnd_611176 313827052492406004789259 := by
  unfold tailWord_611176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145710016910603697874691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14860946689214138263832921 11145710016910603697874691)
  ·
    refine ⟨16718565025365905546812037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11145710016910603697874691 16718565025365905546812037)
    ·
      refine ⟨3134730942256107290027257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16718565025365905546812037 3134730942256107290027257)
      ·
        refine ⟨2351048206692080467520443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134730942256107290027257 2351048206692080467520443)
        ·
          refine ⟨3526572310038120701280665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351048206692080467520443 3526572310038120701280665)
          ·
            refine ⟨2644929232528590525960499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526572310038120701280665 2644929232528590525960499)
            ·
              refine ⟨3967393848792885788940749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644929232528590525960499 3967393848792885788940749)
              ·
                refine ⟨1487772693297332170852781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3967393848792885788940749 1487772693297332170852781)
                ·
                  refine ⟨557914759986499564069793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1487772693297332170852781 557914759986499564069793)
                  ·
                    refine ⟨418436069989874673052345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557914759986499564069793 418436069989874673052345)
                    ·
                      refine ⟨313827052492406004789259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418436069989874673052345 313827052492406004789259)
                      ·
                        rfl

theorem cell23_611176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_611176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611176 prefixEnd_611176 := by exact prefixLift 611176
  have htrace : WordTrace (prefixWord ++ tailWord_611176) baseStart_611176 baseEnd_611176 := by
    simpa [prefixWord, tailWord_611176, baseEnd_611176] using wordTrace_append hprefix tailTrace_611176
  have hstable : (prefixWord ++ tailWord_611176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611176).length < 2 ^ (prefixWord ++ tailWord_611176).sum := by decide
  have hdescent : baseEnd_611176 < baseStart_611176 := by decide
  rcases family_descends (prefixWord ++ tailWord_611176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611189 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_611189 : Nat := 118140960795 + 611189 * 2 ^ 59
def prefixEnd_611189 : Nat := 4983230072969 + 3 ^ 40 * 611189 * 2
def baseEnd_611189 : Nat := 313833727740914453926699

theorem tailTrace_611189 : CollatzResearch.WordTrace tailWord_611189 prefixEnd_611189 313833727740914453926699 := by
  unfold tailWord_611189
  simp only [CollatzResearch.WordTrace]
  refine ⟨22291894182774110615972621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14861262788516073743981747 22291894182774110615972621)
  ·
    refine ⟨8359460318540291480989733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22291894182774110615972621 8359460318540291480989733)
    ·
      refine ⟨1567398809726304652685575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8359460318540291480989733 1567398809726304652685575)
      ·
        refine ⟨2351098214589456979028363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567398809726304652685575 2351098214589456979028363)
        ·
          refine ⟨3526647321884185468542545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351098214589456979028363 3526647321884185468542545)
          ·
            refine ⟨2644985491413139101406909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526647321884185468542545 2644985491413139101406909)
            ·
              refine ⟨991869559279927163027591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2644985491413139101406909 991869559279927163027591)
              ·
                refine ⟨1487804338919890744541387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991869559279927163027591 1487804338919890744541387)
                ·
                  refine ⟨2231706508379836116812081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487804338919890744541387 2231706508379836116812081)
                  ·
                    refine ⟨1673779881284877087609061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231706508379836116812081 1673779881284877087609061)
                    ·
                      refine ⟨313833727740914453926699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1673779881284877087609061 313833727740914453926699)
                      ·
                        rfl

theorem cell23_611189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_611189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611189 prefixEnd_611189 := by exact prefixLift 611189
  have htrace : WordTrace (prefixWord ++ tailWord_611189) baseStart_611189 baseEnd_611189 := by
    simpa [prefixWord, tailWord_611189, baseEnd_611189] using wordTrace_append hprefix tailTrace_611189
  have hstable : (prefixWord ++ tailWord_611189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611189).length < 2 ^ (prefixWord ++ tailWord_611189).sum := by decide
  have hdescent : baseEnd_611189 < baseStart_611189 := by decide
  rcases family_descends (prefixWord ++ tailWord_611189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611192 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_611192 : Nat := 118140960795 + 611192 * 2 ^ 59
def prefixEnd_611192 : Nat := 4983230072969 + 3 ^ 40 * 611192 * 2
def baseEnd_611192 : Nat := 313835268182877942189185

theorem tailTrace_611192 : CollatzResearch.WordTrace tailWord_611192 prefixEnd_611192 313835268182877942189185 := by
  unfold tailWord_611192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146001800881621064165915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14861335734508828085554553 11146001800881621064165915)
  ·
    refine ⟨16719002701322431596248873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11146001800881621064165915 16719002701322431596248873)
    ·
      refine ⟨12539252025991823697186655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16719002701322431596248873 12539252025991823697186655)
      ·
        refine ⟨18808878038987735545779983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12539252025991823697186655 18808878038987735545779983)
        ·
          refine ⟨28213317058481603318669975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18808878038987735545779983 28213317058481603318669975)
          ·
            refine ⟨42319975587722404978004963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28213317058481603318669975 42319975587722404978004963)
            ·
              refine ⟨63479963381583607467007445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42319975587722404978004963 63479963381583607467007445)
              ·
                refine ⟨1487811641755865800007987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63479963381583607467007445 1487811641755865800007987)
                ·
                  refine ⟨2231717462633798700011981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487811641755865800007987 2231717462633798700011981)
                  ·
                    refine ⟨836894048487674512504493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231717462633798700011981 836894048487674512504493)
                    ·
                      refine ⟨313835268182877942189185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836894048487674512504493 313835268182877942189185)
                      ·
                        rfl

theorem cell23_611192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_611192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611192 prefixEnd_611192 := by exact prefixLift 611192
  have htrace : WordTrace (prefixWord ++ tailWord_611192) baseStart_611192 baseEnd_611192 := by
    simpa [prefixWord, tailWord_611192, baseEnd_611192] using wordTrace_append hprefix tailTrace_611192
  have hstable : (prefixWord ++ tailWord_611192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611192).length < 2 ^ (prefixWord ++ tailWord_611192).sum := by decide
  have hdescent : baseEnd_611192 < baseStart_611192 := by decide
  rcases family_descends (prefixWord ++ tailWord_611192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611195 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 7]
def baseStart_611195 : Nat := 118140960795 + 611195 * 2 ^ 59
def prefixEnd_611195 : Nat := 4983230072969 + 3 ^ 40 * 611195 * 2
def baseEnd_611195 : Nat := 104612269541613810150557

theorem tailTrace_611195 : CollatzResearch.WordTrace tailWord_611195 prefixEnd_611195 104612269541613810150557 := by
  unfold tailWord_611195
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292113020752373640691039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14861408680501582427127359 22292113020752373640691039)
  ·
    refine ⟨33438169531128560461036559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22292113020752373640691039 33438169531128560461036559)
    ·
      refine ⟨50157254296692840691554839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33438169531128560461036559 50157254296692840691554839)
      ·
        refine ⟨75235881445039261037332259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50157254296692840691554839 75235881445039261037332259)
        ·
          refine ⟨112853822167558891555998389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75235881445039261037332259 112853822167558891555998389)
          ·
            refine ⟨10580045828208646083374849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112853822167558891555998389 10580045828208646083374849)
            ·
              refine ⟨7935034371156484562531137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580045828208646083374849 7935034371156484562531137)
              ·
                refine ⟨5951275778367363421898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935034371156484562531137 5951275778367363421898353)
                ·
                  refine ⟨4463456833775522566423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951275778367363421898353 4463456833775522566423765)
                  ·
                    refine ⟨104612269541613810150557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4463456833775522566423765 104612269541613810150557)
                    ·
                      rfl

theorem cell23_611195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_611195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611195 prefixEnd_611195 := by exact prefixLift 611195
  have htrace : WordTrace (prefixWord ++ tailWord_611195) baseStart_611195 baseEnd_611195 := by
    simpa [prefixWord, tailWord_611195, baseEnd_611195] using wordTrace_append hprefix tailTrace_611195
  have hstable : (prefixWord ++ tailWord_611195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611195).length < 2 ^ (prefixWord ++ tailWord_611195).sum := by decide
  have hdescent : baseEnd_611195 < baseStart_611195 := by decide
  rcases family_descends (prefixWord ++ tailWord_611195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611209 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_611209 : Nat := 118140960795 + 611209 * 2 ^ 59
def prefixEnd_611209 : Nat := 4983230072969 + 3 ^ 40 * 611209 * 2
def baseEnd_611209 : Nat := 313843997354004375676607

theorem tailTrace_611209 : CollatzResearch.WordTrace tailWord_611209 prefixEnd_611209 313843997354004375676607 := by
  unfold tailWord_611209
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292623642701654031700681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14861749095134436021133787 22292623642701654031700681)
  ·
    refine ⟨16719467732026240523775511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22292623642701654031700681 16719467732026240523775511)
    ·
      refine ⟨25079201598039360785663267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16719467732026240523775511 25079201598039360785663267)
      ·
        refine ⟨37618802397059041178494901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079201598039360785663267 37618802397059041178494901)
        ·
          refine ⟨3526762724724285110483897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37618802397059041178494901 3526762724724285110483897)
          ·
            refine ⟨2645072043543213832862923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526762724724285110483897 2645072043543213832862923)
            ·
              refine ⟨3967608065314820749294385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645072043543213832862923 3967608065314820749294385)
              ·
                refine ⟨2975706048986115561970789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967608065314820749294385 2975706048986115561970789)
                ·
                  refine ⟨557944884184896667869523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2975706048986115561970789 557944884184896667869523)
                  ·
                    refine ⟨836917326277345001804285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 557944884184896667869523 836917326277345001804285)
                    ·
                      refine ⟨313843997354004375676607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 836917326277345001804285 313843997354004375676607)
                      ·
                        rfl

theorem cell23_611209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_611209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611209 prefixEnd_611209 := by exact prefixLift 611209
  have htrace : WordTrace (prefixWord ++ tailWord_611209) baseStart_611209 baseEnd_611209 := by
    simpa [prefixWord, tailWord_611209, baseEnd_611209] using wordTrace_append hprefix tailTrace_611209
  have hstable : (prefixWord ++ tailWord_611209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611209).length < 2 ^ (prefixWord ++ tailWord_611209).sum := by decide
  have hdescent : baseEnd_611209 < baseStart_611209 := by decide
  rcases family_descends (prefixWord ++ tailWord_611209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611210 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_611210 : Nat := 118140960795 + 611210 * 2 ^ 59
def prefixEnd_611210 : Nat := 4983230072969 + 3 ^ 40 * 611210 * 2
def baseEnd_611210 : Nat := 313844510834658871764103

theorem tailTrace_611210 : CollatzResearch.WordTrace tailWord_611210 prefixEnd_611210 313844510834658871764103 := by
  unfold tailWord_611210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573165028924507800621771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14861773410465354134991389 5573165028924507800621771)
  ·
    refine ⟨8359747543386761700932657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573165028924507800621771 8359747543386761700932657)
    ·
      refine ⟨6269810657540071275699493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359747543386761700932657 6269810657540071275699493)
      ·
        refine ⟨1175589498288763364193655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6269810657540071275699493 1175589498288763364193655)
        ·
          refine ⟨1763384247433145046290483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175589498288763364193655 1763384247433145046290483)
          ·
            refine ⟨2645076371149717569435725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763384247433145046290483 2645076371149717569435725)
            ·
              refine ⟨991903639181144088538397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2645076371149717569435725 991903639181144088538397)
              ·
                refine ⟨371963864692929033201899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991903639181144088538397 371963864692929033201899)
                ·
                  refine ⟨557945797039393549802849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371963864692929033201899 557945797039393549802849)
                  ·
                    refine ⟨418459347779545162352137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557945797039393549802849 418459347779545162352137)
                    ·
                      refine ⟨313844510834658871764103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418459347779545162352137 313844510834658871764103)
                      ·
                        rfl

theorem cell23_611210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_611210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611210 prefixEnd_611210 := by exact prefixLift 611210
  have htrace : WordTrace (prefixWord ++ tailWord_611210) baseStart_611210 baseEnd_611210 := by
    simpa [prefixWord, tailWord_611210, baseEnd_611210] using wordTrace_append hprefix tailTrace_611210
  have hstable : (prefixWord ++ tailWord_611210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611210).length < 2 ^ (prefixWord ++ tailWord_611210).sum := by decide
  have hdescent : baseEnd_611210 < baseStart_611210 := by decide
  rcases family_descends (prefixWord ++ tailWord_611210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611286 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_611286 : Nat := 118140960795 + 611286 * 2 ^ 59
def prefixEnd_611286 : Nat := 4983230072969 + 3 ^ 40 * 611286 * 2
def baseEnd_611286 : Nat := 313883535364400574413753

theorem tailTrace_611286 : CollatzResearch.WordTrace tailWord_611286 prefixEnd_611286 313883535364400574413753 := by
  unfold tailWord_611286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393464503963918511390857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14863621375615130788169141 1393464503963918511390857)
  ·
    refine ⟨1045098377972938883543143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1393464503963918511390857 1045098377972938883543143)
    ·
      refine ⟨1567647566959408325314715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045098377972938883543143 1567647566959408325314715)
      ·
        refine ⟨2351471350439112487972073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567647566959408325314715 2351471350439112487972073)
        ·
          refine ⟨1763603512829334365979055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351471350439112487972073 1763603512829334365979055)
          ·
            refine ⟨2645405269244001548968583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763603512829334365979055 2645405269244001548968583)
            ·
              refine ⟨3968107903866002323452875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645405269244001548968583 3968107903866002323452875)
              ·
                refine ⟨5952161855799003485179313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968107903866002323452875 5952161855799003485179313)
                ·
                  refine ⟨4464121391849252613884485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5952161855799003485179313 4464121391849252613884485)
                  ·
                    refine ⟨837022760971734865103341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464121391849252613884485 837022760971734865103341)
                    ·
                      refine ⟨313883535364400574413753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837022760971734865103341 313883535364400574413753)
                      ·
                        rfl

theorem cell23_611286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_611286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611286 prefixEnd_611286 := by exact prefixLift 611286
  have htrace : WordTrace (prefixWord ++ tailWord_611286) baseStart_611286 baseEnd_611286 := by
    simpa [prefixWord, tailWord_611286, baseEnd_611286] using wordTrace_append hprefix tailTrace_611286
  have hstable : (prefixWord ++ tailWord_611286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611286).length < 2 ^ (prefixWord ++ tailWord_611286).sum := by decide
  have hdescent : baseEnd_611286 < baseStart_611286 := by decide
  rcases family_descends (prefixWord ++ tailWord_611286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611299 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3]
def baseStart_611299 : Nat := 118140960795 + 611299 * 2 ^ 59
def prefixEnd_611299 : Nat := 4983230072969 + 3 ^ 40 * 611299 * 2
def baseEnd_611299 : Nat := 313890210612909023551193

theorem tailTrace_611299 : CollatzResearch.WordTrace tailWord_611299 prefixEnd_611299 313890210612909023551193 := by
  unfold tailWord_611299
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295906212375599402476951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14863937474917066268317967 22295906212375599402476951)
  ·
    refine ⟨33443859318563399103715427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22295906212375599402476951 33443859318563399103715427)
    ·
      refine ⟨50165788977845098655573141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33443859318563399103715427 50165788977845098655573141)
      ·
        refine ⟨2351521358336488999479991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50165788977845098655573141 2351521358336488999479991)
        ·
          refine ⟨3527282037504733499219987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351521358336488999479991 3527282037504733499219987)
          ·
            refine ⟨5290923056257100248829981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527282037504733499219987 5290923056257100248829981)
            ·
              refine ⟨1984096146096412593311243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5290923056257100248829981 1984096146096412593311243)
              ·
                refine ⟨2976144219144618889966865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984096146096412593311243 2976144219144618889966865)
                ·
                  refine ⟨2232108164358464167475149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976144219144618889966865 2232108164358464167475149)
                  ·
                    refine ⟨837040561634424062803181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2232108164358464167475149 837040561634424062803181)
                    ·
                      refine ⟨313890210612909023551193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837040561634424062803181 313890210612909023551193)
                      ·
                        rfl

theorem cell23_611299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_611299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611299 prefixEnd_611299 := by exact prefixLift 611299
  have htrace : WordTrace (prefixWord ++ tailWord_611299) baseStart_611299 baseEnd_611299 := by
    simpa [prefixWord, tailWord_611299, baseEnd_611299] using wordTrace_append hprefix tailTrace_611299
  have hstable : (prefixWord ++ tailWord_611299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611299).length < 2 ^ (prefixWord ++ tailWord_611299).sum := by decide
  have hdescent : baseEnd_611299 < baseStart_611299 := by decide
  rcases family_descends (prefixWord ++ tailWord_611299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611359 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_611359 : Nat := 118140960795 + 611359 * 2 ^ 59
def prefixEnd_611359 : Nat := 4983230072969 + 3 ^ 40 * 611359 * 2
def baseEnd_611359 : Nat := 313921019452178788800917

theorem tailTrace_611359 : CollatzResearch.WordTrace tailWord_611359 prefixEnd_611359 313921019452178788800917 := by
  unfold tailWord_611359
  simp only [CollatzResearch.WordTrace]
  refine ⟨22298094592158229649661131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14865396394772153099774087 22298094592158229649661131)
  ·
    refine ⟨33447141888237344474491697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22298094592158229649661131 33447141888237344474491697)
    ·
      refine ⟨25085356416178008355868773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33447141888237344474491697 25085356416178008355868773)
      ·
        refine ⟨4703504328033376566725395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25085356416178008355868773 4703504328033376566725395)
        ·
          refine ⟨7055256492050064850088093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703504328033376566725395 7055256492050064850088093)
          ·
            refine ⟨2645721184518774318783035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7055256492050064850088093 2645721184518774318783035)
            ·
              refine ⟨3968581776778161478174553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645721184518774318783035 3968581776778161478174553)
              ·
                refine ⟨2976436332583621108630915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968581776778161478174553 2976436332583621108630915)
                ·
                  refine ⟨4464654498875431662946373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976436332583621108630915 4464654498875431662946373)
                  ·
                    refine ⟨837122718539143436802445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4464654498875431662946373 837122718539143436802445)
                    ·
                      refine ⟨313921019452178788800917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837122718539143436802445 313921019452178788800917)
                      ·
                        rfl

theorem cell23_611359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_611359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611359 prefixEnd_611359 := by exact prefixLift 611359
  have htrace : WordTrace (prefixWord ++ tailWord_611359) baseStart_611359 baseEnd_611359 := by
    simpa [prefixWord, tailWord_611359, baseEnd_611359] using wordTrace_append hprefix tailTrace_611359
  have hstable : (prefixWord ++ tailWord_611359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611359).length < 2 ^ (prefixWord ++ tailWord_611359).sum := by decide
  have hdescent : baseEnd_611359 < baseStart_611359 := by decide
  rcases family_descends (prefixWord ++ tailWord_611359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611393 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_611393 : Nat := 118140960795 + 611393 * 2 ^ 59
def prefixEnd_611393 : Nat := 4983230072969 + 3 ^ 40 * 611393 * 2
def baseEnd_611393 : Nat := 313938477794431655775761

theorem tailTrace_611393 : CollatzResearch.WordTrace tailWord_611393 prefixEnd_611393 313938477794431655775761 := by
  unfold tailWord_611393
  simp only [CollatzResearch.WordTrace]
  refine ⟨22299334674035053456398833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14866223116023368970932555 22299334674035053456398833)
  ·
    refine ⟨16724501005526290092299125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22299334674035053456398833 16724501005526290092299125)
    ·
      refine ⟨1567921969268089696153043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16724501005526290092299125 1567921969268089696153043)
      ·
        refine ⟨2351882953902134544229565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567921969268089696153043 2351882953902134544229565)
        ·
          refine ⟨881956107713300454086087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351882953902134544229565 881956107713300454086087)
          ·
            refine ⟨1322934161569950681129131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881956107713300454086087 1322934161569950681129131)
            ·
              refine ⟨1984401242354926021693697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322934161569950681129131 1984401242354926021693697)
              ·
                refine ⟨1488300931766194516270273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984401242354926021693697 1488300931766194516270273)
                ·
                  refine ⟨1116225698824645887202705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488300931766194516270273 1116225698824645887202705)
                  ·
                    refine ⟨837169274118484415402029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116225698824645887202705 837169274118484415402029)
                    ·
                      refine ⟨313938477794431655775761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837169274118484415402029 313938477794431655775761)
                      ·
                        rfl

theorem cell23_611393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_611393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611393 prefixEnd_611393 := by exact prefixLift 611393
  have htrace : WordTrace (prefixWord ++ tailWord_611393) baseStart_611393 baseEnd_611393 := by
    simpa [prefixWord, tailWord_611393, baseEnd_611393] using wordTrace_append hprefix tailTrace_611393
  have hstable : (prefixWord ++ tailWord_611393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611393).length < 2 ^ (prefixWord ++ tailWord_611393).sum := by decide
  have hdescent : baseEnd_611393 < baseStart_611393 := by decide
  rcases family_descends (prefixWord ++ tailWord_611393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611416 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_611416 : Nat := 118140960795 + 611416 * 2 ^ 59
def prefixEnd_611416 : Nat := 4983230072969 + 3 ^ 40 * 611416 * 2
def baseEnd_611416 : Nat := 313950287849485065788155

theorem tailTrace_611416 : CollatzResearch.WordTrace tailWord_611416 prefixEnd_611416 313950287849485065788155 := by
  unfold tailWord_611416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150086776475864192243051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14866782368634485589657401 11150086776475864192243051)
  ·
    refine ⟨16725130164713796288364577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11150086776475864192243051 16725130164713796288364577)
    ·
      refine ⟨12543847623535347216273433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16725130164713796288364577 12543847623535347216273433)
      ·
        refine ⟨9407885717651510412205075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12543847623535347216273433 9407885717651510412205075)
        ·
          refine ⟨14111828576477265618307613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407885717651510412205075 14111828576477265618307613)
          ·
            refine ⟨5291935716178974606865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14111828576477265618307613 5291935716178974606865355)
            ·
              refine ⟨7937903574268461910298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291935716178974606865355 7937903574268461910298033)
              ·
                refine ⟨5953427680701346432723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7937903574268461910298033 5953427680701346432723525)
                ·
                  refine ⟨1116267690131502456135661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5953427680701346432723525 1116267690131502456135661)
                  ·
                    refine ⟨418600383799313421050873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116267690131502456135661 418600383799313421050873)
                    ·
                      refine ⟨313950287849485065788155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418600383799313421050873 313950287849485065788155)
                      ·
                        rfl

theorem cell23_611416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_611416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611416 prefixEnd_611416 := by exact prefixLift 611416
  have htrace : WordTrace (prefixWord ++ tailWord_611416) baseStart_611416 baseEnd_611416 := by
    simpa [prefixWord, tailWord_611416, baseEnd_611416] using wordTrace_append hprefix tailTrace_611416
  have hstable : (prefixWord ++ tailWord_611416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611416).length < 2 ^ (prefixWord ++ tailWord_611416).sum := by decide
  have hdescent : baseEnd_611416 < baseStart_611416 := by decide
  rcases family_descends (prefixWord ++ tailWord_611416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611433 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 2, 3, 2]
def baseStart_611433 : Nat := 118140960795 + 611433 * 2 ^ 59
def prefixEnd_611433 : Nat := 4983230072969 + 3 ^ 40 * 611433 * 2
def baseEnd_611433 : Nat := 313959017020611499275577

theorem tailTrace_611433 : CollatzResearch.WordTrace tailWord_611433 prefixEnd_611433 313959017020611499275577 := by
  unfold tailWord_611433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300793593890140287854953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867195729260093525236635 22300793593890140287854953)
  ·
    refine ⟨16725595195417605215891215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22300793593890140287854953 16725595195417605215891215)
    ·
      refine ⟨25088392793126407823836823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16725595195417605215891215 25088392793126407823836823)
      ·
        refine ⟨37632589189689611735755235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25088392793126407823836823 37632589189689611735755235)
        ·
          refine ⟨56448883784534417603632853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37632589189689611735755235 56448883784534417603632853)
          ·
            refine ⟨1323020713700025412585145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56448883784534417603632853 1323020713700025412585145)
            ·
              refine ⟨992265535275019059438859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323020713700025412585145 992265535275019059438859)
              ·
                refine ⟨1488398302912528589158289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992265535275019059438859 1488398302912528589158289)
                ·
                  refine ⟨1116298727184396441868717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488398302912528589158289 1116298727184396441868717)
                  ·
                    refine ⟨418612022694148665700769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116298727184396441868717 418612022694148665700769)
                    ·
                      refine ⟨313959017020611499275577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418612022694148665700769 313959017020611499275577)
                      ·
                        rfl

theorem cell23_611433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3, 2].length) (baseStart_611433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611433 prefixEnd_611433 := by exact prefixLift 611433
  have htrace : WordTrace (prefixWord ++ tailWord_611433) baseStart_611433 baseEnd_611433 := by
    simpa [prefixWord, tailWord_611433, baseEnd_611433] using wordTrace_append hprefix tailTrace_611433
  have hstable : (prefixWord ++ tailWord_611433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611433).length < 2 ^ (prefixWord ++ tailWord_611433).sum := by decide
  have hdescent : baseEnd_611433 < baseStart_611433 := by decide
  rcases family_descends (prefixWord ++ tailWord_611433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611439 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 6]
def baseStart_611439 : Nat := 118140960795 + 611439 * 2 ^ 59
def prefixEnd_611439 : Nat := 4983230072969 + 3 ^ 40 * 611439 * 2
def baseEnd_611439 : Nat := 104654032634846158600183

theorem tailTrace_611439 : CollatzResearch.WordTrace tailWord_611439 prefixEnd_611439 104654032634846158600183 := by
  unfold tailWord_611439
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301012431868403312573371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867341621245602208382247 22301012431868403312573371)
  ·
    refine ⟨33451518647802604968860057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22301012431868403312573371 33451518647802604968860057)
    ·
      refine ⟨25088638985851953726645043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33451518647802604968860057 25088638985851953726645043)
      ·
        refine ⟨37632958478777930589967565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25088638985851953726645043 37632958478777930589967565)
        ·
          refine ⟨14112359429541723971237837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37632958478777930589967565 14112359429541723971237837)
          ·
            refine ⟨5292134786078146489214189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14112359429541723971237837 5292134786078146489214189)
            ·
              refine ⟨1984550544779304933455321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5292134786078146489214189 1984550544779304933455321)
              ·
                refine ⟨1488412908584478700091491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984550544779304933455321 1488412908584478700091491)
                ·
                  refine ⟨2232619362876718050137237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488412908584478700091491 2232619362876718050137237)
                  ·
                    refine ⟨104654032634846158600183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2232619362876718050137237 104654032634846158600183)
                    ·
                      rfl

theorem cell23_611439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_611439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611439 prefixEnd_611439 := by exact prefixLift 611439
  have htrace : WordTrace (prefixWord ++ tailWord_611439) baseStart_611439 baseEnd_611439 := by
    simpa [prefixWord, tailWord_611439, baseEnd_611439] using wordTrace_append hprefix tailTrace_611439
  have hstable : (prefixWord ++ tailWord_611439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611439).length < 2 ^ (prefixWord ++ tailWord_611439).sum := by decide
  have hdescent : baseEnd_611439 < baseStart_611439 := by decide
  rcases family_descends (prefixWord ++ tailWord_611439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611456 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_611456 : Nat := 118140960795 + 611456 * 2 ^ 59
def prefixEnd_611456 : Nat := 4983230072969 + 3 ^ 40 * 611456 * 2
def baseEnd_611456 : Nat := 104656942358554969762657

theorem tailTrace_611456 : CollatzResearch.WordTrace tailWord_611456 prefixEnd_611456 104656942358554969762657 := by
  unfold tailWord_611456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150816236403407607971111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14867754981871210143961481 11150816236403407607971111)
  ·
    refine ⟨16726224354605111411956667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11150816236403407607971111 16726224354605111411956667)
    ·
      refine ⟨25089336531907667117935001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16726224354605111411956667 25089336531907667117935001)
      ·
        refine ⟨18817002398930750338451251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25089336531907667117935001 18817002398930750338451251)
        ·
          refine ⟨28225503598396125507676877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18817002398930750338451251 28225503598396125507676877)
          ·
            refine ⟨10584563849398547065378829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28225503598396125507676877 10584563849398547065378829)
            ·
              refine ⟨3969211443524455149517061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10584563849398547065378829 3969211443524455149517061)
              ·
                refine ⟨744227145660835340534449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3969211443524455149517061 744227145660835340534449)
                ·
                  refine ⟨558170359245626505400837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744227145660835340534449 558170359245626505400837)
                  ·
                    refine ⟨104656942358554969762657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 558170359245626505400837 104656942358554969762657)
                    ·
                      rfl

theorem cell23_611456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_611456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611456 prefixEnd_611456 := by exact prefixLift 611456
  have htrace : WordTrace (prefixWord ++ tailWord_611456) baseStart_611456 baseEnd_611456 := by
    simpa [prefixWord, tailWord_611456, baseEnd_611456] using wordTrace_append hprefix tailTrace_611456
  have hstable : (prefixWord ++ tailWord_611456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611456).length < 2 ^ (prefixWord ++ tailWord_611456).sum := by decide
  have hdescent : baseEnd_611456 < baseStart_611456 := by decide
  rcases family_descends (prefixWord ++ tailWord_611456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611457 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_611457 : Nat := 118140960795 + 611457 * 2 ^ 59
def prefixEnd_611457 : Nat := 4983230072969 + 3 ^ 40 * 611457 * 2
def baseEnd_611457 : Nat := 313971340556319405375467

theorem tailTrace_611457 : CollatzResearch.WordTrace tailWord_611457 prefixEnd_611457 313971340556319405375467 := by
  unfold tailWord_611457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301668945803192386728625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867779297202128257819083 22301668945803192386728625)
  ·
    refine ⟨16726251709352394290046469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22301668945803192386728625 16726251709352394290046469)
    ·
      refine ⟨3136172195503573929383713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16726251709352394290046469 3136172195503573929383713)
      ·
        refine ⟨2352129146627680447037785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136172195503573929383713 2352129146627680447037785)
        ·
          refine ⟨1764096859970760335278339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352129146627680447037785 1764096859970760335278339)
          ·
            refine ⟨2646145289956140502917509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764096859970760335278339 2646145289956140502917509)
            ·
              refine ⟨496152241866776344297033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2646145289956140502917509 496152241866776344297033)
              ·
                refine ⟨372114181400082258222775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496152241866776344297033 372114181400082258222775)
                ·
                  refine ⟨558171272100123387334163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372114181400082258222775 558171272100123387334163)
                  ·
                    refine ⟨837256908150185081001245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558171272100123387334163 837256908150185081001245)
                    ·
                      refine ⟨313971340556319405375467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837256908150185081001245 313971340556319405375467)
                      ·
                        rfl

theorem cell23_611457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_611457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611457 prefixEnd_611457 := by exact prefixLift 611457
  have htrace : WordTrace (prefixWord ++ tailWord_611457) baseStart_611457 baseEnd_611457 := by
    simpa [prefixWord, tailWord_611457, baseEnd_611457] using wordTrace_append hprefix tailTrace_611457
  have hstable : (prefixWord ++ tailWord_611457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611457).length < 2 ^ (prefixWord ++ tailWord_611457).sum := by decide
  have hdescent : baseEnd_611457 < baseStart_611457 := by decide
  rcases family_descends (prefixWord ++ tailWord_611457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611459 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_611459 : Nat := 118140960795 + 611459 * 2 ^ 59
def prefixEnd_611459 : Nat := 4983230072969 + 3 ^ 40 * 611459 * 2
def baseEnd_611459 : Nat := 313972367517628397550457

theorem tailTrace_611459 : CollatzResearch.WordTrace tailWord_611459 prefixEnd_611459 313972367517628397550457 := by
  unfold tailWord_611459
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301741891795946728301431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867827927863964485534287 22301741891795946728301431)
  ·
    refine ⟨33452612837693920092452147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22301741891795946728301431 33452612837693920092452147)
    ·
      refine ⟨50178919256540880138678221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33452612837693920092452147 50178919256540880138678221)
      ·
        refine ⟨18817094721202830052004333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50178919256540880138678221 18817094721202830052004333)
        ·
          refine ⟨7056410520451061269501625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18817094721202830052004333 7056410520451061269501625)
          ·
            refine ⟨5292307890338295952126219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056410520451061269501625 5292307890338295952126219)
            ·
              refine ⟨7938461835507443928189329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292307890338295952126219 7938461835507443928189329)
              ·
                refine ⟨5953846376630582946141997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7938461835507443928189329 5953846376630582946141997)
                ·
                  refine ⟨2232692391236468604803249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5953846376630582946141997 2232692391236468604803249)
                  ·
                    refine ⟨1674519293427351453602437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232692391236468604803249 1674519293427351453602437)
                    ·
                      refine ⟨313972367517628397550457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1674519293427351453602437 313972367517628397550457)
                      ·
                        rfl

theorem cell23_611459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_611459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611459 prefixEnd_611459 := by exact prefixLift 611459
  have htrace : WordTrace (prefixWord ++ tailWord_611459) baseStart_611459 baseEnd_611459 := by
    simpa [prefixWord, tailWord_611459, baseEnd_611459] using wordTrace_append hprefix tailTrace_611459
  have hstable : (prefixWord ++ tailWord_611459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611459).length < 2 ^ (prefixWord ++ tailWord_611459).sum := by decide
  have hdescent : baseEnd_611459 < baseStart_611459 := by decide
  rcases family_descends (prefixWord ++ tailWord_611459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611463 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_611463 : Nat := 118140960795 + 611463 * 2 ^ 59
def prefixEnd_611463 : Nat := 4983230072969 + 3 ^ 40 * 611463 * 2
def baseEnd_611463 : Nat := 313974421440246381900439

theorem tailTrace_611463 : CollatzResearch.WordTrace tailWord_611463 prefixEnd_611463 313974421440246381900439 := by
  unfold tailWord_611463
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301887783781455411447043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867925189187636940964695 22301887783781455411447043)
  ·
    refine ⟨33452831675672183117170565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22301887783781455411447043 33452831675672183117170565)
    ·
      refine ⟨6272405939188534334469481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33452831675672183117170565 6272405939188534334469481)
      ·
        refine ⟨4704304454391400750852111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6272405939188534334469481 4704304454391400750852111)
        ·
          refine ⟨7056456681587101126278167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704304454391400750852111 7056456681587101126278167)
          ·
            refine ⟨10584685022380651689417251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056456681587101126278167 10584685022380651689417251)
            ·
              refine ⟨15877027533570977534125877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584685022380651689417251 15877027533570977534125877)
              ·
                refine ⟨1488471331272279143824301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15877027533570977534125877 1488471331272279143824301)
                ·
                  refine ⟨558176749227104678934113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1488471331272279143824301 558176749227104678934113)
                  ·
                    refine ⟨418632561920328509200585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558176749227104678934113 418632561920328509200585)
                    ·
                      refine ⟨313974421440246381900439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418632561920328509200585 313974421440246381900439)
                      ·
                        rfl

theorem cell23_611463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_611463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611463 prefixEnd_611463 := by exact prefixLift 611463
  have htrace : WordTrace (prefixWord ++ tailWord_611463) baseStart_611463 baseEnd_611463 := by
    simpa [prefixWord, tailWord_611463, baseEnd_611463] using wordTrace_append hprefix tailTrace_611463
  have hstable : (prefixWord ++ tailWord_611463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611463).length < 2 ^ (prefixWord ++ tailWord_611463).sum := by decide
  have hdescent : baseEnd_611463 < baseStart_611463 := by decide
  rcases family_descends (prefixWord ++ tailWord_611463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611466 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_611466 : Nat := 118140960795 + 611466 * 2 ^ 59
def prefixEnd_611466 : Nat := 4983230072969 + 3 ^ 40 * 611466 * 2
def baseEnd_611466 : Nat := 313975961882209870162925

theorem tailTrace_611466 : CollatzResearch.WordTrace tailWord_611466 prefixEnd_611466 313975961882209870162925 := by
  unfold tailWord_611466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575499300692646730951563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14867998135180391282537501 5575499300692646730951563)
  ·
    refine ⟨8363248951038970096427345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5575499300692646730951563 8363248951038970096427345)
    ·
      refine ⟨6272436713279227572320509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8363248951038970096427345 6272436713279227572320509)
      ·
        refine ⟨2352163767479710339620191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6272436713279227572320509 2352163767479710339620191)
        ·
          refine ⟨3528245651219565509430287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352163767479710339620191 3528245651219565509430287)
          ·
            refine ⟨5292368476829348264145431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528245651219565509430287 5292368476829348264145431)
            ·
              refine ⟨7938552715244022396218147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292368476829348264145431 7938552715244022396218147)
              ·
                refine ⟨11907829072866033594327221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938552715244022396218147 11907829072866033594327221)
                ·
                  refine ⟨1116358975581190649468177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11907829072866033594327221 1116358975581190649468177)
                  ·
                    refine ⟨837269231685892987101133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116358975581190649468177 837269231685892987101133)
                    ·
                      refine ⟨313975961882209870162925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837269231685892987101133 313975961882209870162925)
                      ·
                        rfl

theorem cell23_611466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_611466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611466 prefixEnd_611466 := by exact prefixLift 611466
  have htrace : WordTrace (prefixWord ++ tailWord_611466) baseStart_611466 baseEnd_611466 := by
    simpa [prefixWord, tailWord_611466, baseEnd_611466] using wordTrace_append hprefix tailTrace_611466
  have hstable : (prefixWord ++ tailWord_611466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611466).length < 2 ^ (prefixWord ++ tailWord_611466).sum := by decide
  have hdescent : baseEnd_611466 < baseStart_611466 := by decide
  rcases family_descends (prefixWord ++ tailWord_611466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611480 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_611480 : Nat := 118140960795 + 611480 * 2 ^ 59
def prefixEnd_611480 : Nat := 4983230072969 + 3 ^ 40 * 611480 * 2
def baseEnd_611480 : Nat := 313983150611372815387861

theorem tailTrace_611480 : CollatzResearch.WordTrace tailWord_611480 prefixEnd_611480 313983150611372815387861 := by
  unfold tailWord_611480
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151253912359933657407947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14868338549813244876543929 11151253912359933657407947)
  ·
    refine ⟨16726880868539900486111921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11151253912359933657407947 16726880868539900486111921)
    ·
      refine ⟨12545160651404925364583941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16726880868539900486111921 12545160651404925364583941)
      ·
        refine ⟨2352217622138423505859489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12545160651404925364583941 2352217622138423505859489)
        ·
          refine ⟨1764163216603817629394617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352217622138423505859489 1764163216603817629394617)
          ·
            refine ⟨1323122412452863222045963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1764163216603817629394617 1323122412452863222045963)
            ·
              refine ⟨1984683618679294833068945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323122412452863222045963 1984683618679294833068945)
              ·
                refine ⟨1488512714009471124801709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984683618679294833068945 1488512714009471124801709)
                ·
                  refine ⟨558192267753551671800641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1488512714009471124801709 558192267753551671800641)
                  ·
                    refine ⟨418644200815163753850481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558192267753551671800641 418644200815163753850481)
                    ·
                      refine ⟨313983150611372815387861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418644200815163753850481 313983150611372815387861)
                      ·
                        rfl

theorem cell23_611480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_611480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611480 prefixEnd_611480 := by exact prefixLift 611480
  have htrace : WordTrace (prefixWord ++ tailWord_611480) baseStart_611480 baseEnd_611480 := by
    simpa [prefixWord, tailWord_611480, baseEnd_611480] using wordTrace_append hprefix tailTrace_611480
  have hstable : (prefixWord ++ tailWord_611480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611480).length < 2 ^ (prefixWord ++ tailWord_611480).sum := by decide
  have hdescent : baseEnd_611480 < baseStart_611480 := by decide
  rcases family_descends (prefixWord ++ tailWord_611480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611513 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_611513 : Nat := 118140960795 + 611513 * 2 ^ 59
def prefixEnd_611513 : Nat := 4983230072969 + 3 ^ 40 * 611513 * 2
def baseEnd_611513 : Nat := 314000095472971186275209

theorem tailTrace_611513 : CollatzResearch.WordTrace tailWord_611513 prefixEnd_611513 314000095472971186275209 := by
  unfold tailWord_611513
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303711433600313950767193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14869140955733542633844795 22303711433600313950767193)
  ·
    refine ⟨16727783575200235463075395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22303711433600313950767193 16727783575200235463075395)
    ·
      refine ⟨25091675362800353194613093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727783575200235463075395 25091675362800353194613093)
      ·
        refine ⟨4704689130525066223989955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25091675362800353194613093 4704689130525066223989955)
        ·
          refine ⟨7057033695787599335984933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704689130525066223989955 7057033695787599335984933)
          ·
            refine ⟨1323193817960174875497175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7057033695787599335984933 1323193817960174875497175)
            ·
              refine ⟨1984790726940262313245763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323193817960174875497175 1984790726940262313245763)
              ·
                refine ⟨2977186090410393469868645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984790726940262313245763 2977186090410393469868645)
                ·
                  refine ⟨558222391951948775600371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2977186090410393469868645 558222391951948775600371)
                  ·
                    refine ⟨837333587927923163400557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558222391951948775600371 837333587927923163400557)
                    ·
                      refine ⟨314000095472971186275209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837333587927923163400557 314000095472971186275209)
                      ·
                        rfl

theorem cell23_611513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_611513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611513 prefixEnd_611513 := by exact prefixLift 611513
  have htrace : WordTrace (prefixWord ++ tailWord_611513) baseStart_611513 baseEnd_611513 := by
    simpa [prefixWord, tailWord_611513, baseEnd_611513] using wordTrace_append hprefix tailTrace_611513
  have hstable : (prefixWord ++ tailWord_611513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611513).length < 2 ^ (prefixWord ++ tailWord_611513).sum := by decide
  have hdescent : baseEnd_611513 < baseStart_611513 := by decide
  rcases family_descends (prefixWord ++ tailWord_611513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611519 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_611519 : Nat := 118140960795 + 611519 * 2 ^ 59
def prefixEnd_611519 : Nat := 4983230072969 + 3 ^ 40 * 611519 * 2
def baseEnd_611519 : Nat := 314003176356898162800181

theorem tailTrace_611519 : CollatzResearch.WordTrace tailWord_611519 prefixEnd_611519 314003176356898162800181 := by
  unfold tailWord_611519
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303930271578576975485611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14869286847719051316990407 22303930271578576975485611)
  ·
    refine ⟨33455895407367865463228417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22303930271578576975485611 33455895407367865463228417)
    ·
      refine ⟨25091921555525899097421313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33455895407367865463228417 25091921555525899097421313)
      ·
        refine ⟨18818941166644424323065985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25091921555525899097421313 18818941166644424323065985)
        ·
          refine ⟨14114205874983318242299489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18818941166644424323065985 14114205874983318242299489)
          ·
            refine ⟨10585654406237488681724617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14114205874983318242299489 10585654406237488681724617)
            ·
              refine ⟨7939240804678116511293463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10585654406237488681724617 7939240804678116511293463)
              ·
                refine ⟨11908861207017174766940195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939240804678116511293463 11908861207017174766940195)
                ·
                  refine ⟨17863291810525762150410293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11908861207017174766940195 17863291810525762150410293)
                  ·
                    refine ⟨1674683607236790201600965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17863291810525762150410293 1674683607236790201600965)
                    ·
                      refine ⟨314003176356898162800181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1674683607236790201600965 314003176356898162800181)
                      ·
                        rfl

theorem cell23_611519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_611519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611519 prefixEnd_611519 := by exact prefixLift 611519
  have htrace : WordTrace (prefixWord ++ tailWord_611519) baseStart_611519 baseEnd_611519 := by
    simpa [prefixWord, tailWord_611519, baseEnd_611519] using wordTrace_append hprefix tailTrace_611519
  have hstable : (prefixWord ++ tailWord_611519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611519).length < 2 ^ (prefixWord ++ tailWord_611519).sum := by decide
  have hdescent : baseEnd_611519 < baseStart_611519 := by decide
  rcases family_descends (prefixWord ++ tailWord_611519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_611539 : Nat := 118140960795 + 611539 * 2 ^ 59
def prefixEnd_611539 : Nat := 4983230072969 + 3 ^ 40 * 611539 * 2
def baseEnd_611539 : Nat := 314013445969988084550089

theorem tailTrace_611539 : CollatzResearch.WordTrace tailWord_611539 prefixEnd_611539 314013445969988084550089 := by
  unfold tailWord_611539
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304659731506120391213671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14869773154337413594142447 22304659731506120391213671)
  ·
    refine ⟨33456989597259180586820507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22304659731506120391213671 33456989597259180586820507)
    ·
      refine ⟨50185484395888770880230761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33456989597259180586820507 50185484395888770880230761)
      ·
        refine ⟨37639113296916578160173071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50185484395888770880230761 37639113296916578160173071)
        ·
          refine ⟨56458669945374867240259607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37639113296916578160173071 56458669945374867240259607)
          ·
            refine ⟨84688004918062300860389411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56458669945374867240259607 84688004918062300860389411)
            ·
              refine ⟨127032007377093451290584117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84688004918062300860389411 127032007377093451290584117)
              ·
                refine ⟨11909250691602511058492261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127032007377093451290584117 11909250691602511058492261)
                ·
                  refine ⟨2232984504675470823467299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11909250691602511058492261 2232984504675470823467299)
                  ·
                    refine ⟨3349476757013206235200949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232984504675470823467299 3349476757013206235200949)
                    ·
                      refine ⟨314013445969988084550089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3349476757013206235200949 314013445969988084550089)
                      ·
                        rfl

theorem cell23_611539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_611539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611539 prefixEnd_611539 := by exact prefixLift 611539
  have htrace : WordTrace (prefixWord ++ tailWord_611539) baseStart_611539 baseEnd_611539 := by
    simpa [prefixWord, tailWord_611539, baseEnd_611539] using wordTrace_append hprefix tailTrace_611539
  have hstable : (prefixWord ++ tailWord_611539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611539).length < 2 ^ (prefixWord ++ tailWord_611539).sum := by decide
  have hdescent : baseEnd_611539 < baseStart_611539 := by decide
  rcases family_descends (prefixWord ++ tailWord_611539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611566 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_611566 : Nat := 118140960795 + 611566 * 2 ^ 59
def prefixEnd_611566 : Nat := 4983230072969 + 3 ^ 40 * 611566 * 2
def baseEnd_611566 : Nat := 314027309947659478912465

theorem tailTrace_611566 : CollatzResearch.WordTrace tailWord_611566 prefixEnd_611566 314027309947659478912465 := by
  unfold tailWord_611566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788205562801038000305819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14870429668272202668297701 2788205562801038000305819)
  ·
    refine ⟨4182308344201557000458729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788205562801038000305819 4182308344201557000458729)
    ·
      refine ⟨3136731258151167750344047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4182308344201557000458729 3136731258151167750344047)
      ·
        refine ⟨4705096887226751625516071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136731258151167750344047 4705096887226751625516071)
        ·
          refine ⟨7057645330840127438274107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705096887226751625516071 7057645330840127438274107)
          ·
            refine ⟨10586467996260191157411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057645330840127438274107 10586467996260191157411161)
            ·
              refine ⟨7939850997195143368058371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10586467996260191157411161 7939850997195143368058371)
              ·
                refine ⟨11909776495792715052087557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939850997195143368058371 11909776495792715052087557)
                ·
                  refine ⟨2233083092961134072266417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11909776495792715052087557 2233083092961134072266417)
                  ·
                    refine ⟨1674812319720850554199813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2233083092961134072266417 1674812319720850554199813)
                    ·
                      refine ⟨314027309947659478912465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1674812319720850554199813 314027309947659478912465)
                      ·
                        rfl

theorem cell23_611566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_611566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611566 prefixEnd_611566 := by exact prefixLift 611566
  have htrace : WordTrace (prefixWord ++ tailWord_611566) baseStart_611566 baseEnd_611566 := by
    simpa [prefixWord, tailWord_611566, baseEnd_611566] using wordTrace_append hprefix tailTrace_611566
  have hstable : (prefixWord ++ tailWord_611566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611566).length < 2 ^ (prefixWord ++ tailWord_611566).sum := by decide
  have hdescent : baseEnd_611566 < baseStart_611566 := by decide
  rcases family_descends (prefixWord ++ tailWord_611566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611569 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_611569 : Nat := 118140960795 + 611569 * 2 ^ 59
def prefixEnd_611569 : Nat := 4983230072969 + 3 ^ 40 * 611569 * 2
def baseEnd_611569 : Nat := 314028850389622967174951

theorem tailTrace_611569 : CollatzResearch.WordTrace tailWord_611569 prefixEnd_611569 314028850389622967174951 := by
  unfold tailWord_611569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305753921397435514805761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870502614264957009870507 22305753921397435514805761)
  ·
    refine ⟨16729315441048076636104321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22305753921397435514805761 16729315441048076636104321)
    ·
      refine ⟨12546986580786057477078241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16729315441048076636104321 12546986580786057477078241)
      ·
        refine ⟨9410239935589543107808681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12546986580786057477078241 9410239935589543107808681)
        ·
          refine ⟨7057679951692157330856511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410239935589543107808681 7057679951692157330856511)
          ·
            refine ⟨10586519927538235996284767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057679951692157330856511 10586519927538235996284767)
            ·
              refine ⟨15879779891307353994427151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10586519927538235996284767 15879779891307353994427151)
              ·
                refine ⟨23819669836961030991640727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15879779891307353994427151 23819669836961030991640727)
                ·
                  refine ⟨35729504755441546487461091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23819669836961030991640727 35729504755441546487461091)
                  ·
                    refine ⟨53594257133162319731191637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35729504755441546487461091 53594257133162319731191637)
                    ·
                      refine ⟨314028850389622967174951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 53594257133162319731191637 314028850389622967174951)
                      ·
                        rfl

theorem cell23_611569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_611569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611569 prefixEnd_611569 := by exact prefixLift 611569
  have htrace : WordTrace (prefixWord ++ tailWord_611569) baseStart_611569 baseEnd_611569 := by
    simpa [prefixWord, tailWord_611569, baseEnd_611569] using wordTrace_append hprefix tailTrace_611569
  have hstable : (prefixWord ++ tailWord_611569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611569).length < 2 ^ (prefixWord ++ tailWord_611569).sum := by decide
  have hdescent : baseEnd_611569 < baseStart_611569 := by decide
  rcases family_descends (prefixWord ++ tailWord_611569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611587 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 2, 2, 2]
def baseStart_611587 : Nat := 118140960795 + 611587 * 2 ^ 59
def prefixEnd_611587 : Nat := 4983230072969 + 3 ^ 40 * 611587 * 2
def baseEnd_611587 : Nat := 314038093041403896749869

theorem tailTrace_611587 : CollatzResearch.WordTrace tailWord_611587 prefixEnd_611587 314038093041403896749869 := by
  unfold tailWord_611587
  simp only [CollatzResearch.WordTrace]
  refine ⟨22306410435332224588961015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870940290221483059307343 22306410435332224588961015)
  ·
    refine ⟨33459615652998336883441523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22306410435332224588961015 33459615652998336883441523)
    ·
      refine ⟨50189423479497505325162285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33459615652998336883441523 50189423479497505325162285)
      ·
        refine ⟨18821033804811564496935857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50189423479497505325162285 18821033804811564496935857)
        ·
          refine ⟨14115775353608673372701893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18821033804811564496935857 14115775353608673372701893)
          ·
            refine ⟨2646707878801626257381605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14115775353608673372701893 2646707878801626257381605)
            ·
              refine ⟨496257727275304923259051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2646707878801626257381605 496257727275304923259051)
              ·
                refine ⟨744386590912957384888577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496257727275304923259051 744386590912957384888577)
                ·
                  refine ⟨558289943184718038666433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744386590912957384888577 558289943184718038666433)
                  ·
                    refine ⟨418717457388538528999825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558289943184718038666433 418717457388538528999825)
                    ·
                      refine ⟨314038093041403896749869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418717457388538528999825 314038093041403896749869)
                      ·
                        rfl

theorem cell23_611587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_611587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611587 prefixEnd_611587 := by exact prefixLift 611587
  have htrace : WordTrace (prefixWord ++ tailWord_611587) baseStart_611587 baseEnd_611587 := by
    simpa [prefixWord, tailWord_611587, baseEnd_611587] using wordTrace_append hprefix tailTrace_611587
  have hstable : (prefixWord ++ tailWord_611587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611587).length < 2 ^ (prefixWord ++ tailWord_611587).sum := by decide
  have hdescent : baseEnd_611587 < baseStart_611587 := by decide
  rcases family_descends (prefixWord ++ tailWord_611587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611660 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_611660 : Nat := 118140960795 + 611660 * 2 ^ 59
def prefixEnd_611660 : Nat := 4983230072969 + 3 ^ 40 * 611660 * 2
def baseEnd_611660 : Nat := 314075577129182111137033

theorem tailTrace_611660 : CollatzResearch.WordTrace tailWord_611660 prefixEnd_611660 314075577129182111137033 := by
  unfold tailWord_611660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11154536482033879028184217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14872715309378505370912289 11154536482033879028184217)
  ·
    refine ⟨8365902361525409271138163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11154536482033879028184217 8365902361525409271138163)
    ·
      refine ⟨12548853542288113906707245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8365902361525409271138163 12548853542288113906707245)
      ·
        refine ⟨4705820078358042715015217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12548853542288113906707245 4705820078358042715015217)
        ·
          refine ⟨3529365058768532036261413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705820078358042715015217 3529365058768532036261413)
          ·
            refine ⟨661755948519099756799015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3529365058768532036261413 661755948519099756799015)
            ·
              refine ⟨992633922778649635198523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661755948519099756799015 992633922778649635198523)
              ·
                refine ⟨1488950884167974452797785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992633922778649635198523 1488950884167974452797785)
                ·
                  refine ⟨1116713163125980839598339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488950884167974452797785 1116713163125980839598339)
                  ·
                    refine ⟨1675069744688971259397509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1116713163125980839598339 1675069744688971259397509)
                    ·
                      refine ⟨314075577129182111137033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1675069744688971259397509 314075577129182111137033)
                      ·
                        rfl

theorem cell23_611660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_611660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611660 prefixEnd_611660 := by exact prefixLift 611660
  have htrace : WordTrace (prefixWord ++ tailWord_611660) baseStart_611660 baseEnd_611660 := by
    simpa [prefixWord, tailWord_611660, baseEnd_611660] using wordTrace_append hprefix tailTrace_611660
  have hstable : (prefixWord ++ tailWord_611660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611660).length < 2 ^ (prefixWord ++ tailWord_611660).sum := by decide
  have hdescent : baseEnd_611660 < baseStart_611660 := by decide
  rcases family_descends (prefixWord ++ tailWord_611660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611666 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_611666 : Nat := 118140960795 + 611666 * 2 ^ 59
def prefixEnd_611666 : Nat := 4983230072969 + 3 ^ 40 * 611666 * 2
def baseEnd_611666 : Nat := 34897628668123231962445

theorem tailTrace_611666 : CollatzResearch.WordTrace tailWord_611666 prefixEnd_611666 34897628668123231962445 := by
  unfold tailWord_611666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577322950511505270271713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14872861201364014054057901 5577322950511505270271713)
  ·
    refine ⟨4182992212883628952703785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5577322950511505270271713 4182992212883628952703785)
    ·
      refine ⟨3137244159662721714527839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4182992212883628952703785 3137244159662721714527839)
      ·
        refine ⟨4705866239494082571791759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137244159662721714527839 4705866239494082571791759)
        ·
          refine ⟨7058799359241123857687639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705866239494082571791759 7058799359241123857687639)
          ·
            refine ⟨10588199038861685786531459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058799359241123857687639 10588199038861685786531459)
            ·
              refine ⟨15882298558292528679797189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588199038861685786531459 15882298558292528679797189)
              ·
                refine ⟨2977930979679849127461973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15882298558292528679797189 2977930979679849127461973)
                ·
                  refine ⟨34897628668123231962445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2977930979679849127461973 34897628668123231962445)
                  ·
                    rfl

theorem cell23_611666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_611666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611666 prefixEnd_611666 := by exact prefixLift 611666
  have htrace : WordTrace (prefixWord ++ tailWord_611666) baseStart_611666 baseEnd_611666 := by
    simpa [prefixWord, tailWord_611666, baseEnd_611666] using wordTrace_append hprefix tailTrace_611666
  have hstable : (prefixWord ++ tailWord_611666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611666).length < 2 ^ (prefixWord ++ tailWord_611666).sum := by decide
  have hdescent : baseEnd_611666 < baseStart_611666 := by decide
  rcases family_descends (prefixWord ++ tailWord_611666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611683 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 6]
def baseStart_611683 : Nat := 118140960795 + 611683 * 2 ^ 59
def prefixEnd_611683 : Nat := 4983230072969 + 3 ^ 40 * 611683 * 2
def baseEnd_611683 : Nat := 34898598576026169016603

theorem tailTrace_611683 : CollatzResearch.WordTrace tailWord_611683 prefixEnd_611683 34898598576026169016603 := by
  unfold tailWord_611683
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309911842984432984455703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14873274561989621989637135 22309911842984432984455703)
  ·
    refine ⟨33464867764476649476683555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309911842984432984455703 33464867764476649476683555)
    ·
      refine ⟨50197301646714974215025333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33464867764476649476683555 50197301646714974215025333)
      ·
        refine ⟨4705997029379528832658625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50197301646714974215025333 4705997029379528832658625)
        ·
          refine ⟨3529497772034646624493969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705997029379528832658625 3529497772034646624493969)
          ·
            refine ⟨2647123329025984968370477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529497772034646624493969 2647123329025984968370477)
            ·
              refine ⟨992671248384744363138929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647123329025984968370477 992671248384744363138929)
              ·
                refine ⟨744503436288558272354197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992671248384744363138929 744503436288558272354197)
                ·
                  refine ⟨34898598576026169016603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 744503436288558272354197 34898598576026169016603)
                  ·
                    rfl

theorem cell23_611683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 6].length) (baseStart_611683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611683 prefixEnd_611683 := by exact prefixLift 611683
  have htrace : WordTrace (prefixWord ++ tailWord_611683) baseStart_611683 baseEnd_611683 := by
    simpa [prefixWord, tailWord_611683, baseEnd_611683] using wordTrace_append hprefix tailTrace_611683
  have hstable : (prefixWord ++ tailWord_611683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611683).length < 2 ^ (prefixWord ++ tailWord_611683).sum := by decide
  have hdescent : baseEnd_611683 < baseStart_611683 := by decide
  rcases family_descends (prefixWord ++ tailWord_611683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611703 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_611703 : Nat := 118140960795 + 611703 * 2 ^ 59
def prefixEnd_611703 : Nat := 4983230072969 + 3 ^ 40 * 611703 * 2
def baseEnd_611703 : Nat := 314097656797325442899335

theorem tailTrace_611703 : CollatzResearch.WordTrace tailWord_611703 prefixEnd_611703 314097656797325442899335 := by
  unfold tailWord_611703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22310641302911976400183763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14873760868607984266789175 22310641302911976400183763)
  ·
    refine ⟨33465961954367964600275645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22310641302911976400183763 33465961954367964600275645)
    ·
      refine ⟨12549735732887986725103367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33465961954367964600275645 12549735732887986725103367)
      ·
        refine ⟨18824603599331980087655051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12549735732887986725103367 18824603599331980087655051)
        ·
          refine ⟨28236905398997970131482577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18824603599331980087655051 28236905398997970131482577)
          ·
            refine ⟨21177679049248477598611933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28236905398997970131482577 21177679049248477598611933)
            ·
              refine ⟨7941629643468179099479475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21177679049248477598611933 7941629643468179099479475)
              ·
                refine ⟨11912444465202268649219213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7941629643468179099479475 11912444465202268649219213)
                ·
                  refine ⟨4467166674450850743457205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11912444465202268649219213 4467166674450850743457205)
                  ·
                    refine ⟨418796875729767257199113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467166674450850743457205 418796875729767257199113)
                    ·
                      refine ⟨314097656797325442899335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418796875729767257199113 314097656797325442899335)
                      ·
                        rfl

theorem cell23_611703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_611703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611703 prefixEnd_611703 := by exact prefixLift 611703
  have htrace : WordTrace (prefixWord ++ tailWord_611703) baseStart_611703 baseEnd_611703 := by
    simpa [prefixWord, tailWord_611703, baseEnd_611703] using wordTrace_append hprefix tailTrace_611703
  have hstable : (prefixWord ++ tailWord_611703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611703).length < 2 ^ (prefixWord ++ tailWord_611703).sum := by decide
  have hdescent : baseEnd_611703 < baseStart_611703 := by decide
  rcases family_descends (prefixWord ++ tailWord_611703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611720 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_611720 : Nat := 118140960795 + 611720 * 2 ^ 59
def prefixEnd_611720 : Nat := 4983230072969 + 3 ^ 40 * 611720 * 2
def baseEnd_611720 : Nat := 314106385968451876386757

theorem tailTrace_611720 : CollatzResearch.WordTrace tailWord_611720 prefixEnd_611720 314106385968451876386757 := by
  unfold tailWord_611720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155630671925194151776307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14874174229233592202368409 11155630671925194151776307)
  ·
    refine ⟨16733446007887791227664461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11155630671925194151776307 16733446007887791227664461)
    ·
      refine ⟨6275042252957921710374173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16733446007887791227664461 6275042252957921710374173)
      ·
        refine ⟨2353140844859220641390315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6275042252957921710374173 2353140844859220641390315)
        ·
          refine ⟨3529711267288830962085473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353140844859220641390315 3529711267288830962085473)
          ·
            refine ⟨2647283450466623221564105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529711267288830962085473 2647283450466623221564105)
            ·
              refine ⟨1985462587849967416173079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647283450466623221564105 1985462587849967416173079)
              ·
                refine ⟨2978193881774951124259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985462587849967416173079 2978193881774951124259619)
                ·
                  refine ⟨4467290822662426686389429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978193881774951124259619 4467290822662426686389429)
                  ·
                    refine ⟨418808514624602501849009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467290822662426686389429 418808514624602501849009)
                    ·
                      refine ⟨314106385968451876386757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418808514624602501849009 314106385968451876386757)
                      ·
                        rfl

theorem cell23_611720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_611720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611720 prefixEnd_611720 := by exact prefixLift 611720
  have htrace : WordTrace (prefixWord ++ tailWord_611720) baseStart_611720 baseEnd_611720 := by
    simpa [prefixWord, tailWord_611720, baseEnd_611720] using wordTrace_append hprefix tailTrace_611720
  have hstable : (prefixWord ++ tailWord_611720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611720).length < 2 ^ (prefixWord ++ tailWord_611720).sum := by decide
  have hdescent : baseEnd_611720 < baseStart_611720 := by decide
  rcases family_descends (prefixWord ++ tailWord_611720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611744 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 1, 1, 3]
def baseStart_611744 : Nat := 118140960795 + 611744 * 2 ^ 59
def prefixEnd_611744 : Nat := 4983230072969 + 3 ^ 40 * 611744 * 2
def baseEnd_611744 : Nat := 314118709504159782486647

theorem tailTrace_611744 : CollatzResearch.WordTrace tailWord_611744 prefixEnd_611744 314118709504159782486647 := by
  unfold tailWord_611744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156068347881720201213143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14874757797175626934950857 11156068347881720201213143)
  ·
    refine ⟨16734102521822580301819715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156068347881720201213143 16734102521822580301819715)
    ·
      refine ⟨25101153782733870452729573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16734102521822580301819715 25101153782733870452729573)
      ·
        refine ⟨4706466334262600709886795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25101153782733870452729573 4706466334262600709886795)
        ·
          refine ⟨7059699501393901064830193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706466334262600709886795 7059699501393901064830193)
          ·
            refine ⟨5294774626045425798622645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059699501393901064830193 5294774626045425798622645)
            ·
              refine ⟨496385121191758668620873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5294774626045425798622645 496385121191758668620873)
              ·
                refine ⟨372288840893819001465655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496385121191758668620873 372288840893819001465655)
                ·
                  refine ⟨558433261340728502198483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372288840893819001465655 558433261340728502198483)
                  ·
                    refine ⟨837649892011092753297725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558433261340728502198483 837649892011092753297725)
                    ·
                      refine ⟨314118709504159782486647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837649892011092753297725 314118709504159782486647)
                      ·
                        rfl

theorem cell23_611744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_611744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611744 prefixEnd_611744 := by exact prefixLift 611744
  have htrace : WordTrace (prefixWord ++ tailWord_611744) baseStart_611744 baseEnd_611744 := by
    simpa [prefixWord, tailWord_611744, baseEnd_611744] using wordTrace_append hprefix tailTrace_611744
  have hstable : (prefixWord ++ tailWord_611744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611744).length < 2 ^ (prefixWord ++ tailWord_611744).sum := by decide
  have hdescent : baseEnd_611744 < baseStart_611744 := by decide
  rcases family_descends (prefixWord ++ tailWord_611744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611756 : List Nat := [2, 2, 1, 1, 1, 1, 5, 10]
def baseStart_611756 : Nat := 118140960795 + 611756 * 2 ^ 59
def prefixEnd_611756 : Nat := 4983230072969 + 3 ^ 40 * 611756 * 2
def baseEnd_611756 : Nat := 11634254491556064279133

theorem tailTrace_611756 : CollatzResearch.WordTrace tailWord_611756 prefixEnd_611756 11634254491556064279133 := by
  unfold tailWord_611756
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156287185859983225931561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14875049581146644301242081 11156287185859983225931561)
  ·
    refine ⟨8367215389394987419448671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11156287185859983225931561 8367215389394987419448671)
    ·
      refine ⟨12550823084092481129173007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367215389394987419448671 12550823084092481129173007)
      ·
        refine ⟨18826234626138721693759511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12550823084092481129173007 18826234626138721693759511)
        ·
          refine ⟨28239351939208082540639267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18826234626138721693759511 28239351939208082540639267)
          ·
            refine ⟨42359027908812123810958901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28239351939208082540639267 42359027908812123810958901)
            ·
              refine ⟨3971158866451136607277397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42359027908812123810958901 3971158866451136607277397)
              ·
                refine ⟨11634254491556064279133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3971158866451136607277397 11634254491556064279133)
                ·
                  rfl

theorem cell23_611756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 10].length) (baseStart_611756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611756 prefixEnd_611756 := by exact prefixLift 611756
  have htrace : WordTrace (prefixWord ++ tailWord_611756) baseStart_611756 baseEnd_611756 := by
    simpa [prefixWord, tailWord_611756, baseEnd_611756] using wordTrace_append hprefix tailTrace_611756
  have hstable : (prefixWord ++ tailWord_611756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611756).length < 2 ^ (prefixWord ++ tailWord_611756).sum := by decide
  have hdescent : baseEnd_611756 < baseStart_611756 := by decide
  rcases family_descends (prefixWord ++ tailWord_611756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611780 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_611780 : Nat := 118140960795 + 611780 * 2 ^ 59
def prefixEnd_611780 : Nat := 4983230072969 + 3 ^ 40 * 611780 * 2
def baseEnd_611780 : Nat := 314137194807721641636481

theorem tailTrace_611780 : CollatzResearch.WordTrace tailWord_611780 prefixEnd_611780 314137194807721641636481 := by
  unfold tailWord_611780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156724861816509275368397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14875633149088679033824529 11156724861816509275368397)
  ·
    refine ⟨4183771823181190978263149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11156724861816509275368397 4183771823181190978263149)
    ·
      refine ⟨1568914433692946616848681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4183771823181190978263149 1568914433692946616848681)
      ·
        refine ⟨1176685825269709962636511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568914433692946616848681 1176685825269709962636511)
        ·
          refine ⟨1765028737904564943954767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176685825269709962636511 1765028737904564943954767)
          ·
            refine ⟨2647543106856847415932151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765028737904564943954767 2647543106856847415932151)
            ·
              refine ⟨3971314660285271123898227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647543106856847415932151 3971314660285271123898227)
              ·
                refine ⟨5956971990427906685847341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971314660285271123898227 5956971990427906685847341)
                ·
                  refine ⟨2233864496410465007192753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5956971990427906685847341 2233864496410465007192753)
                  ·
                    refine ⟨1675398372307848755394565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2233864496410465007192753 1675398372307848755394565)
                    ·
                      refine ⟨314137194807721641636481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1675398372307848755394565 314137194807721641636481)
                      ·
                        rfl

theorem cell23_611780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_611780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611780 prefixEnd_611780 := by exact prefixLift 611780
  have htrace : WordTrace (prefixWord ++ tailWord_611780) baseStart_611780 baseEnd_611780 := by
    simpa [prefixWord, tailWord_611780, baseEnd_611780] using wordTrace_append hprefix tailTrace_611780
  have hstable : (prefixWord ++ tailWord_611780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611780).length < 2 ^ (prefixWord ++ tailWord_611780).sum := by decide
  have hdescent : baseEnd_611780 < baseStart_611780 := by decide
  rcases family_descends (prefixWord ++ tailWord_611780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611784 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_611784 : Nat := 118140960795 + 611784 * 2 ^ 59
def prefixEnd_611784 : Nat := 4983230072969 + 3 ^ 40 * 611784 * 2
def baseEnd_611784 : Nat := 314139248730339625986463

theorem tailTrace_611784 : CollatzResearch.WordTrace tailWord_611784 prefixEnd_611784 314139248730339625986463 := by
  unfold tailWord_611784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156797807809263616941203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14875730410412351489254937 11156797807809263616941203)
  ·
    refine ⟨16735196711713895425411805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156797807809263616941203 16735196711713895425411805)
    ·
      refine ⟨6275698766892710784529427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16735196711713895425411805 6275698766892710784529427)
      ·
        refine ⟨9413548150339066176794141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6275698766892710784529427 9413548150339066176794141)
        ·
          refine ⟨3530080556377149816297803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9413548150339066176794141 3530080556377149816297803)
          ·
            refine ⟨5295120834565724724446705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530080556377149816297803 5295120834565724724446705)
            ·
              refine ⟨3971340625924293543335029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295120834565724724446705 3971340625924293543335029)
              ·
                refine ⟨372313183680402519687659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3971340625924293543335029 372313183680402519687659)
                ·
                  refine ⟨558469775520603779531489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372313183680402519687659 558469775520603779531489)
                  ·
                    refine ⟨418852331640452834648617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558469775520603779531489 418852331640452834648617)
                    ·
                      refine ⟨314139248730339625986463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418852331640452834648617 314139248730339625986463)
                      ·
                        rfl

theorem cell23_611784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_611784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611784 prefixEnd_611784 := by exact prefixLift 611784
  have htrace : WordTrace (prefixWord ++ tailWord_611784) baseStart_611784 baseEnd_611784 := by
    simpa [prefixWord, tailWord_611784, baseEnd_611784] using wordTrace_append hprefix tailTrace_611784
  have hstable : (prefixWord ++ tailWord_611784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611784).length < 2 ^ (prefixWord ++ tailWord_611784).sum := by decide
  have hdescent : baseEnd_611784 < baseStart_611784 := by decide
  rcases family_descends (prefixWord ++ tailWord_611784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611800 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_611800 : Nat := 118140960795 + 611800 * 2 ^ 59
def prefixEnd_611800 : Nat := 4983230072969 + 3 ^ 40 * 611800 * 2
def baseEnd_611800 : Nat := 314147464420811563386389

theorem tailTrace_611800 : CollatzResearch.WordTrace tailWord_611800 prefixEnd_611800 314147464420811563386389 := by
  unfold tailWord_611800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11157089591780280983232427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14876119455707041310976569 11157089591780280983232427)
  ·
    refine ⟨16735634387670421474848641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11157089591780280983232427 16735634387670421474848641)
    ·
      refine ⟨12551725790752816106136481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16735634387670421474848641 12551725790752816106136481)
      ·
        refine ⟨9413794343064612079602361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12551725790752816106136481 9413794343064612079602361)
        ·
          refine ⟨7060345757298459059701771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9413794343064612079602361 7060345757298459059701771)
          ·
            refine ⟨10590518635947688589552657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7060345757298459059701771 10590518635947688589552657)
            ·
              refine ⟨7942888976960766442164493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10590518635947688589552657 7942888976960766442164493)
              ·
                refine ⟨2978583366360287415811685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7942888976960766442164493 2978583366360287415811685)
                ·
                  refine ⟨558484381192553890464691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2978583366360287415811685 558484381192553890464691)
                  ·
                    refine ⟨837726571788830835697037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558484381192553890464691 837726571788830835697037)
                    ·
                      refine ⟨314147464420811563386389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837726571788830835697037 314147464420811563386389)
                      ·
                        rfl

theorem cell23_611800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_611800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611800 prefixEnd_611800 := by exact prefixLift 611800
  have htrace : WordTrace (prefixWord ++ tailWord_611800) baseStart_611800 baseEnd_611800 := by
    simpa [prefixWord, tailWord_611800, baseEnd_611800] using wordTrace_append hprefix tailTrace_611800
  have hstable : (prefixWord ++ tailWord_611800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611800).length < 2 ^ (prefixWord ++ tailWord_611800).sum := by decide
  have hdescent : baseEnd_611800 < baseStart_611800 := by decide
  rcases family_descends (prefixWord ++ tailWord_611800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611801 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 1, 2, 2]
def baseStart_611801 : Nat := 118140960795 + 611801 * 2 ^ 59
def prefixEnd_611801 : Nat := 4983230072969 + 3 ^ 40 * 611801 * 2
def baseEnd_611801 : Nat := 314147977901466059473885

theorem tailTrace_611801 : CollatzResearch.WordTrace tailWord_611801 prefixEnd_611801 314147977901466059473885 := by
  unfold tailWord_611801
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314215656556939137251257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14876143771037959424834171 22314215656556939137251257)
  ·
    refine ⟨16735661742417704352938443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22314215656556939137251257 16735661742417704352938443)
    ·
      refine ⟨25103492613626556529407665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16735661742417704352938443 25103492613626556529407665)
      ·
        refine ⟨18827619460219917397055749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25103492613626556529407665 18827619460219917397055749)
        ·
          refine ⟨3530178648791234511947953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18827619460219917397055749 3530178648791234511947953)
          ·
            refine ⟨2647633986593425883960965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530178648791234511947953 2647633986593425883960965)
            ·
              refine ⟨496431372486267353242681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2647633986593425883960965 496431372486267353242681)
              ·
                refine ⟨372323529364700514932011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496431372486267353242681 372323529364700514932011)
                ·
                  refine ⟨558485294047050772398017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372323529364700514932011 558485294047050772398017)
                  ·
                    refine ⟨418863970535288079298513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558485294047050772398017 418863970535288079298513)
                    ·
                      refine ⟨314147977901466059473885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418863970535288079298513 314147977901466059473885)
                      ·
                        rfl

theorem cell23_611801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_611801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611801 prefixEnd_611801 := by exact prefixLift 611801
  have htrace : WordTrace (prefixWord ++ tailWord_611801) baseStart_611801 baseEnd_611801 := by
    simpa [prefixWord, tailWord_611801, baseEnd_611801] using wordTrace_append hprefix tailTrace_611801
  have hstable : (prefixWord ++ tailWord_611801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611801).length < 2 ^ (prefixWord ++ tailWord_611801).sum := by decide
  have hdescent : baseEnd_611801 < baseStart_611801 := by decide
  rcases family_descends (prefixWord ++ tailWord_611801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611838 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_611838 : Nat := 118140960795 + 611838 * 2 ^ 59
def prefixEnd_611838 : Nat := 4983230072969 + 3 ^ 40 * 611838 * 2
def baseEnd_611838 : Nat := 314166976685682414711215

theorem tailTrace_611838 : CollatzResearch.WordTrace tailWord_611838 prefixEnd_611838 314166976685682414711215 := by
  unfold tailWord_611838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789445644677861807043521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14877043438281929637565445 2789445644677861807043521)
  ·
    refine ⟨2092084233508396355282641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789445644677861807043521 2092084233508396355282641)
    ·
      refine ⟨1569063175131297266461981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2092084233508396355282641 1569063175131297266461981)
      ·
        refine ⟨588398690674236474923243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1569063175131297266461981 588398690674236474923243)
        ·
          refine ⟨882598036011354712384865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588398690674236474923243 882598036011354712384865)
          ·
            refine ⟨661948527008516034288649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882598036011354712384865 661948527008516034288649)
            ·
              refine ⟨496461395256387025716487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661948527008516034288649 496461395256387025716487)
              ·
                refine ⟨744692092884580538574731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496461395256387025716487 744692092884580538574731)
                ·
                  refine ⟨1117038139326870807862097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744692092884580538574731 1117038139326870807862097)
                  ·
                    refine ⟨837778604495153105896573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117038139326870807862097 837778604495153105896573)
                    ·
                      refine ⟨314166976685682414711215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837778604495153105896573 314166976685682414711215)
                      ·
                        rfl

theorem cell23_611838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_611838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611838 prefixEnd_611838 := by exact prefixLift 611838
  have htrace : WordTrace (prefixWord ++ tailWord_611838) baseStart_611838 baseEnd_611838 := by
    simpa [prefixWord, tailWord_611838, baseEnd_611838] using wordTrace_append hprefix tailTrace_611838
  have hstable : (prefixWord ++ tailWord_611838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611838).length < 2 ^ (prefixWord ++ tailWord_611838).sum := by decide
  have hdescent : baseEnd_611838 < baseStart_611838 := by decide
  rcases family_descends (prefixWord ++ tailWord_611838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611843 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3]
def baseStart_611843 : Nat := 118140960795 + 611843 * 2 ^ 59
def prefixEnd_611843 : Nat := 4983230072969 + 3 ^ 40 * 611843 * 2
def baseEnd_611843 : Nat := 314169544088954895148691

theorem tailTrace_611843 : CollatzResearch.WordTrace tailWord_611843 prefixEnd_611843 314169544088954895148691 := by
  unfold tailWord_611843
  simp only [CollatzResearch.WordTrace]
  refine ⟨22315747522404780310280183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14877165014936520206853455 22315747522404780310280183)
  ·
    refine ⟨33473621283607170465420275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22315747522404780310280183 33473621283607170465420275)
    ·
      refine ⟨50210431925410755698130413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33473621283607170465420275 50210431925410755698130413)
      ·
        refine ⟨18828911972029033386798905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50210431925410755698130413 18828911972029033386798905)
        ·
          refine ⟨14121683979021775040099179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18828911972029033386798905 14121683979021775040099179)
          ·
            refine ⟨21182525968532662560148769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14121683979021775040099179 21182525968532662560148769)
            ·
              refine ⟨15886894476399496920111577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21182525968532662560148769 15886894476399496920111577)
              ·
                refine ⟨11915170857299622690083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15886894476399496920111577 11915170857299622690083683)
                ·
                  refine ⟨17872756285949434035125525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11915170857299622690083683 17872756285949434035125525)
                  ·
                    refine ⟨837785450903879720396509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17872756285949434035125525 837785450903879720396509)
                    ·
                      refine ⟨314169544088954895148691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837785450903879720396509 314169544088954895148691)
                      ·
                        rfl

theorem cell23_611843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_611843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611843 prefixEnd_611843 := by exact prefixLift 611843
  have htrace : WordTrace (prefixWord ++ tailWord_611843) baseStart_611843 baseEnd_611843 := by
    simpa [prefixWord, tailWord_611843, baseEnd_611843] using wordTrace_append hprefix tailTrace_611843
  have hstable : (prefixWord ++ tailWord_611843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611843).length < 2 ^ (prefixWord ++ tailWord_611843).sum := by decide
  have hdescent : baseEnd_611843 < baseStart_611843 := by decide
  rcases family_descends (prefixWord ++ tailWord_611843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611851 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 2, 1, 3]
def baseStart_611851 : Nat := 118140960795 + 611851 * 2 ^ 59
def prefixEnd_611851 : Nat := 4983230072969 + 3 ^ 40 * 611851 * 2
def baseEnd_611851 : Nat := 314173651934190863848655

theorem tailTrace_611851 : CollatzResearch.WordTrace tailWord_611851 prefixEnd_611851 314173651934190863848655 := by
  unfold tailWord_611851
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316039306375797676571407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14877359537583865117714271 22316039306375797676571407)
  ·
    refine ⟨33474058959563696514857111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22316039306375797676571407 33474058959563696514857111)
    ·
      refine ⟨50211088439345544772285667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33474058959563696514857111 50211088439345544772285667)
      ·
        refine ⟨75316632659018317158428501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50211088439345544772285667 75316632659018317158428501)
        ·
          refine ⟨441308394486435452100167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 75316632659018317158428501 441308394486435452100167)
          ·
            refine ⟨661962591729653178150251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441308394486435452100167 661962591729653178150251)
            ·
              refine ⟨992943887594479767225377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661962591729653178150251 992943887594479767225377)
              ·
                refine ⟨744707915695859825419033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992943887594479767225377 744707915695859825419033)
                ·
                  refine ⟨558530936771894869064275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744707915695859825419033 558530936771894869064275)
                  ·
                    refine ⟨837796405157842303596413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558530936771894869064275 837796405157842303596413)
                    ·
                      refine ⟨314173651934190863848655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 837796405157842303596413 314173651934190863848655)
                      ·
                        rfl

theorem cell23_611851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 1, 3].length) (baseStart_611851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611851 prefixEnd_611851 := by exact prefixLift 611851
  have htrace : WordTrace (prefixWord ++ tailWord_611851) baseStart_611851 baseEnd_611851 := by
    simpa [prefixWord, tailWord_611851, baseEnd_611851] using wordTrace_append hprefix tailTrace_611851
  have hstable : (prefixWord ++ tailWord_611851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611851).length < 2 ^ (prefixWord ++ tailWord_611851).sum := by decide
  have hdescent : baseEnd_611851 < baseStart_611851 := by decide
  rcases family_descends (prefixWord ++ tailWord_611851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611857 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_611857 : Nat := 118140960795 + 611857 * 2 ^ 59
def prefixEnd_611857 : Nat := 4983230072969 + 3 ^ 40 * 611857 * 2
def baseEnd_611857 : Nat := 314176732818117840373627

theorem tailTrace_611857 : CollatzResearch.WordTrace tailWord_611857 prefixEnd_611857 314176732818117840373627 := by
  unfold tailWord_611857
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316258144354060701289825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14877505429569373800859883 22316258144354060701289825)
  ·
    refine ⟨16737193608265545525967369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22316258144354060701289825 16737193608265545525967369)
    ·
      refine ⟨12552895206199159144475527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16737193608265545525967369 12552895206199159144475527)
      ·
        refine ⟨18829342809298738716713291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12552895206199159144475527 18829342809298738716713291)
        ·
          refine ⟨28244014213948108075069937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18829342809298738716713291 28244014213948108075069937)
          ·
            refine ⟨21183010660461081056302453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28244014213948108075069937 21183010660461081056302453)
            ·
              refine ⟨1985907249418226349028355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21183010660461081056302453 1985907249418226349028355)
              ·
                refine ⟨2978860874127339523542533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985907249418226349028355 2978860874127339523542533)
                ·
                  refine ⟨558536413898876160664225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2978860874127339523542533 558536413898876160664225)
                  ·
                    refine ⟨418902310424157120498169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558536413898876160664225 418902310424157120498169)
                    ·
                      refine ⟨314176732818117840373627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418902310424157120498169 314176732818117840373627)
                      ·
                        rfl

theorem cell23_611857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_611857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611857 prefixEnd_611857 := by exact prefixLift 611857
  have htrace : WordTrace (prefixWord ++ tailWord_611857) baseStart_611857 baseEnd_611857 := by
    simpa [prefixWord, tailWord_611857, baseEnd_611857] using wordTrace_append hprefix tailTrace_611857
  have hstable : (prefixWord ++ tailWord_611857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611857).length < 2 ^ (prefixWord ++ tailWord_611857).sum := by decide
  have hdescent : baseEnd_611857 < baseStart_611857 := by decide
  rcases family_descends (prefixWord ++ tailWord_611857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611874 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_611874 : Nat := 118140960795 + 611874 * 2 ^ 59
def prefixEnd_611874 : Nat := 4983230072969 + 3 ^ 40 * 611874 * 2
def baseEnd_611874 : Nat := 314185461989244273861049

theorem tailTrace_611874 : CollatzResearch.WordTrace tailWord_611874 prefixEnd_611874 314185461989244273861049 := by
  unfold tailWord_611874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5579219546323118151164669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14877918790194981736439117 5579219546323118151164669)
  ·
    refine ⟨2092207329871169306686751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5579219546323118151164669 2092207329871169306686751)
    ·
      refine ⟨3138310994806753960030127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092207329871169306686751 3138310994806753960030127)
      ·
        refine ⟨4707466492210130940045191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138310994806753960030127 4707466492210130940045191)
        ·
          refine ⟨7061199738315196410067787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707466492210130940045191 7061199738315196410067787)
          ·
            refine ⟨10591799607472794615101681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7061199738315196410067787 10591799607472794615101681)
            ·
              refine ⟨7943849705604595961326261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10591799607472794615101681 7943849705604595961326261)
              ·
                refine ⟨744735909900430871374337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7943849705604595961326261 744735909900430871374337)
                ·
                  refine ⟨558551932425323153530753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744735909900430871374337 558551932425323153530753)
                  ·
                    refine ⟨418913949318992365148065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558551932425323153530753 418913949318992365148065)
                    ·
                      refine ⟨314185461989244273861049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 418913949318992365148065 314185461989244273861049)
                      ·
                        rfl

theorem cell23_611874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_611874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611874 prefixEnd_611874 := by exact prefixLift 611874
  have htrace : WordTrace (prefixWord ++ tailWord_611874) baseStart_611874 baseEnd_611874 := by
    simpa [prefixWord, tailWord_611874, baseEnd_611874] using wordTrace_append hprefix tailTrace_611874
  have hstable : (prefixWord ++ tailWord_611874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611874).length < 2 ^ (prefixWord ++ tailWord_611874).sum := by decide
  have hdescent : baseEnd_611874 < baseStart_611874 := by decide
  rcases family_descends (prefixWord ++ tailWord_611874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611897 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 5]
def baseStart_611897 : Nat := 118140960795 + 611897 * 2 ^ 59
def prefixEnd_611897 : Nat := 4983230072969 + 3 ^ 40 * 611897 * 2
def baseEnd_611897 : Nat := 34910808004921964874827

theorem tailTrace_611897 : CollatzResearch.WordTrace tailWord_611897 prefixEnd_611897 34910808004921964874827 := by
  unfold tailWord_611897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22317717064209147532745945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14878478042806098355163963 22317717064209147532745945)
  ·
    refine ⟨16738287798156860649559459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22317717064209147532745945 16738287798156860649559459)
    ·
      refine ⟨25107431697235290974339189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16738287798156860649559459 25107431697235290974339189)
      ·
        refine ⟨2353821721615808528844299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25107431697235290974339189 2353821721615808528844299)
        ·
          refine ⟨3530732582423712793266449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353821721615808528844299 3530732582423712793266449)
          ·
            refine ⟨2648049436817784594949837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530732582423712793266449 2648049436817784594949837)
            ·
              refine ⟨993018538806669223106189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648049436817784594949837 993018538806669223106189)
              ·
                refine ⟨372381952052500958664821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993018538806669223106189 372381952052500958664821)
                ·
                  refine ⟨34910808004921964874827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372381952052500958664821 34910808004921964874827)
                  ·
                    rfl

theorem cell23_611897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 5].length) (baseStart_611897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611897 prefixEnd_611897 := by exact prefixLift 611897
  have htrace : WordTrace (prefixWord ++ tailWord_611897) baseStart_611897 baseEnd_611897 := by
    simpa [prefixWord, tailWord_611897, baseEnd_611897] using wordTrace_append hprefix tailTrace_611897
  have hstable : (prefixWord ++ tailWord_611897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611897).length < 2 ^ (prefixWord ++ tailWord_611897).sum := by decide
  have hdescent : baseEnd_611897 < baseStart_611897 := by decide
  rcases family_descends (prefixWord ++ tailWord_611897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611953 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 10]
def baseStart_611953 : Nat := 118140960795 + 611953 * 2 ^ 59
def prefixEnd_611953 : Nat := 4983230072969 + 3 ^ 40 * 611953 * 2
def baseEnd_611953 : Nat := 34914002995661051641465

theorem tailTrace_611953 : CollatzResearch.WordTrace tailWord_611953 prefixEnd_611953 34914002995661051641465 := by
  unfold tailWord_611953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22319759552006269096784513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14879839701337512731189675 22319759552006269096784513)
  ·
    refine ⟨16739819664004701822588385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22319759552006269096784513 16739819664004701822588385)
    ·
      refine ⟨12554864748003526366941289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16739819664004701822588385 12554864748003526366941289)
      ·
        refine ⟨9416148561002644775205967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12554864748003526366941289 9416148561002644775205967)
        ·
          refine ⟨14124222841503967162808951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9416148561002644775205967 14124222841503967162808951)
          ·
            refine ⟨21186334262255950744213427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14124222841503967162808951 21186334262255950744213427)
            ·
              refine ⟨31779501393383926116320141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186334262255950744213427 31779501393383926116320141)
              ·
                refine ⟨11917313022518972293620053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31779501393383926116320141 11917313022518972293620053)
                ·
                  refine ⟨34914002995661051641465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 11917313022518972293620053 34914002995661051641465)
                  ·
                    rfl

theorem cell23_611953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_611953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611953 prefixEnd_611953 := by exact prefixLift 611953
  have htrace : WordTrace (prefixWord ++ tailWord_611953) baseStart_611953 baseEnd_611953 := by
    simpa [prefixWord, tailWord_611953, baseEnd_611953] using wordTrace_append hprefix tailTrace_611953
  have hstable : (prefixWord ++ tailWord_611953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611953).length < 2 ^ (prefixWord ++ tailWord_611953).sum := by decide
  have hdescent : baseEnd_611953 < baseStart_611953 := by decide
  rcases family_descends (prefixWord ++ tailWord_611953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611983 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 11]
def baseStart_611983 : Nat := 118140960795 + 611983 * 2 ^ 59
def prefixEnd_611983 : Nat := 4983230072969 + 3 ^ 40 * 611983 * 2
def baseEnd_611983 : Nat := 104747143793528115799349

theorem tailTrace_611983 : CollatzResearch.WordTrace tailWord_611983 prefixEnd_611983 104747143793528115799349 := by
  unfold tailWord_611983
  simp only [CollatzResearch.WordTrace]
  refine ⟨22320853741897584220376603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14880569161265056146917735 22320853741897584220376603)
  ·
    refine ⟨33481280612846376330564905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22320853741897584220376603 33481280612846376330564905)
    ·
      refine ⟨25110960459634782247923679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33481280612846376330564905 25110960459634782247923679)
      ·
        refine ⟨37666440689452173371885519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25110960459634782247923679 37666440689452173371885519)
        ·
          refine ⟨56499661034178260057828279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37666440689452173371885519 56499661034178260057828279)
          ·
            refine ⟨84749491551267390086742419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56499661034178260057828279 84749491551267390086742419)
            ·
              refine ⟨127124237326901085130113629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84749491551267390086742419 127124237326901085130113629)
              ·
                refine ⟨47671588997587906923792611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127124237326901085130113629 47671588997587906923792611)
                ·
                  refine ⟨71507383496381860385688917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47671588997587906923792611 71507383496381860385688917)
                  ·
                    refine ⟨104747143793528115799349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 71507383496381860385688917 104747143793528115799349)
                    ·
                      rfl

theorem cell23_611983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_611983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_611983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_611983 prefixEnd_611983 := by exact prefixLift 611983
  have htrace : WordTrace (prefixWord ++ tailWord_611983) baseStart_611983 baseEnd_611983 := by
    simpa [prefixWord, tailWord_611983, baseEnd_611983] using wordTrace_append hprefix tailTrace_611983
  have hstable : (prefixWord ++ tailWord_611983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611983).length < 2 ^ (prefixWord ++ tailWord_611983).sum := by decide
  have hdescent : baseEnd_611983 < baseStart_611983 := by decide
  rcases family_descends (prefixWord ++ tailWord_611983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612021 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 6]
def baseStart_612021 : Nat := 118140960795 + 612021 * 2 ^ 59
def prefixEnd_612021 : Nat := 4983230072969 + 3 ^ 40 * 612021 * 2
def baseEnd_612021 : Nat := 34917882627272799858097

theorem tailTrace_612021 : CollatzResearch.WordTrace tailWord_612021 prefixEnd_612021 34917882627272799858097 := by
  unfold tailWord_612021
  simp only [CollatzResearch.WordTrace]
  refine ⟨22322239715759916710259917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14881493143839944473506611 22322239715759916710259917)
  ·
    refine ⟨8370839893409968766347469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22322239715759916710259917 8370839893409968766347469)
    ·
      refine ⟨3139064960028738287380301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8370839893409968766347469 3139064960028738287380301)
      ·
        refine ⟨1177149360010776857767613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3139064960028738287380301 1177149360010776857767613)
        ·
          refine ⟨441431010004041321662855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1177149360010776857767613 441431010004041321662855)
          ·
            refine ⟨662146515006061982494283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441431010004041321662855 662146515006061982494283)
            ·
              refine ⟨993219772509092973741425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662146515006061982494283 993219772509092973741425)
              ·
                refine ⟨744914829381819730306069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993219772509092973741425 744914829381819730306069)
                ·
                  refine ⟨34917882627272799858097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 744914829381819730306069 34917882627272799858097)
                  ·
                    rfl

theorem cell23_612021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_612021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612021 prefixEnd_612021 := by exact prefixLift 612021
  have htrace : WordTrace (prefixWord ++ tailWord_612021) baseStart_612021 baseEnd_612021 := by
    simpa [prefixWord, tailWord_612021, baseEnd_612021] using wordTrace_append hprefix tailTrace_612021
  have hstable : (prefixWord ++ tailWord_612021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612021).length < 2 ^ (prefixWord ++ tailWord_612021).sum := by decide
  have hdescent : baseEnd_612021 < baseStart_612021 := by decide
  rcases family_descends (prefixWord ++ tailWord_612021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612038 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_612038 : Nat := 118140960795 + 612038 * 2 ^ 59
def prefixEnd_612038 : Nat := 4983230072969 + 3 ^ 40 * 612038 * 2
def baseEnd_612038 : Nat := 34918852535175736912255

theorem tailTrace_612038 : CollatzResearch.WordTrace tailWord_612038 prefixEnd_612038 34918852535175736912255 := by
  unfold tailWord_612038
  simp only [CollatzResearch.WordTrace]
  refine ⟨697589367396822769175899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14881906504465552409085845 697589367396822769175899)
  ·
    refine ⟨1046384051095234153763849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697589367396822769175899 1046384051095234153763849)
    ·
      refine ⟨784788038321425615322887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1046384051095234153763849 784788038321425615322887)
      ·
        refine ⟨1177182057482138422984331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784788038321425615322887 1177182057482138422984331)
        ·
          refine ⟨1765773086223207634476497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177182057482138422984331 1765773086223207634476497)
          ·
            refine ⟨1324329814667405725857373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1765773086223207634476497 1324329814667405725857373)
            ·
              refine ⟨496623680500277147196515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1324329814667405725857373 496623680500277147196515)
              ·
                refine ⟨744935520750415720794773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496623680500277147196515 744935520750415720794773)
                ·
                  refine ⟨34918852535175736912255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 744935520750415720794773 34918852535175736912255)
                  ·
                    rfl

theorem cell23_612038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_612038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612038 prefixEnd_612038 := by exact prefixLift 612038
  have htrace : WordTrace (prefixWord ++ tailWord_612038) baseStart_612038 baseEnd_612038 := by
    simpa [prefixWord, tailWord_612038, baseEnd_612038] using wordTrace_append hprefix tailTrace_612038
  have hstable : (prefixWord ++ tailWord_612038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612038).length < 2 ^ (prefixWord ++ tailWord_612038).sum := by decide
  have hdescent : baseEnd_612038 < baseStart_612038 := by decide
  rcases family_descends (prefixWord ++ tailWord_612038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612047 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 2, 4]
def baseStart_612047 : Nat := 118140960795 + 612047 * 2 ^ 59
def prefixEnd_612047 : Nat := 4983230072969 + 3 ^ 40 * 612047 * 2
def baseEnd_612047 : Nat := 104758098047490698999251

theorem tailTrace_612047 : CollatzResearch.WordTrace tailWord_612047 prefixEnd_612047 104758098047490698999251 := by
  unfold tailWord_612047
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323188013665723150706395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14882125342443815433804263 22323188013665723150706395)
  ·
    refine ⟨33484782020498584726059593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22323188013665723150706395 33484782020498584726059593)
    ·
      refine ⟨25113586515373938544544695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33484782020498584726059593 25113586515373938544544695)
      ·
        refine ⟨37670379773060907816817043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25113586515373938544544695 37670379773060907816817043)
        ·
          refine ⟨56505569659591361725225565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37670379773060907816817043 56505569659591361725225565)
          ·
            refine ⟨21189588622346760646959587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56505569659591361725225565 21189588622346760646959587)
            ·
              refine ⟨31784382933520140970439381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21189588622346760646959587 31784382933520140970439381)
              ·
                refine ⟨744946475004378303994673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31784382933520140970439381 744946475004378303994673)
                ·
                  refine ⟨558709856253283727996005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744946475004378303994673 558709856253283727996005)
                  ·
                    refine ⟨104758098047490698999251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 558709856253283727996005 104758098047490698999251)
                    ·
                      rfl

theorem cell23_612047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_612047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612047 prefixEnd_612047 := by exact prefixLift 612047
  have htrace : WordTrace (prefixWord ++ tailWord_612047) baseStart_612047 baseEnd_612047 := by
    simpa [prefixWord, tailWord_612047, baseEnd_612047] using wordTrace_append hprefix tailTrace_612047
  have hstable : (prefixWord ++ tailWord_612047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612047).length < 2 ^ (prefixWord ++ tailWord_612047).sum := by decide
  have hdescent : baseEnd_612047 < baseStart_612047 := by decide
  rcases family_descends (prefixWord ++ tailWord_612047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612065 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_612065 : Nat := 118140960795 + 612065 * 2 ^ 59
def prefixEnd_612065 : Nat := 4983230072969 + 3 ^ 40 * 612065 * 2
def baseEnd_612065 : Nat := 314283536794253026572671

theorem tailTrace_612065 : CollatzResearch.WordTrace tailWord_612065 prefixEnd_612065 314283536794253026572671 := by
  unfold tailWord_612065
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323844527600512224861649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14882563018400341483241099 22323844527600512224861649)
  ·
    refine ⟨16742883395700384168646237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22323844527600512224861649 16742883395700384168646237)
    ·
      refine ⟨6278581273387644063242339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16742883395700384168646237 6278581273387644063242339)
      ·
        refine ⟨9417871910081466094863509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278581273387644063242339 9417871910081466094863509)
        ·
          refine ⟨441462745785068723196727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9417871910081466094863509 441462745785068723196727)
          ·
            refine ⟨662194118677603084795091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441462745785068723196727 662194118677603084795091)
            ·
              refine ⟨993291178016404627192637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662194118677603084795091 993291178016404627192637)
              ·
                refine ⟨372484191756151735197239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993291178016404627192637 372484191756151735197239)
                ·
                  refine ⟨558726287634227602795859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372484191756151735197239 558726287634227602795859)
                  ·
                    refine ⟨838089431451341404193789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558726287634227602795859 838089431451341404193789)
                    ·
                      refine ⟨314283536794253026572671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838089431451341404193789 314283536794253026572671)
                      ·
                        rfl

theorem cell23_612065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_612065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612065 prefixEnd_612065 := by exact prefixLift 612065
  have htrace : WordTrace (prefixWord ++ tailWord_612065) baseStart_612065 baseEnd_612065 := by
    simpa [prefixWord, tailWord_612065, baseEnd_612065] using wordTrace_append hprefix tailTrace_612065
  have hstable : (prefixWord ++ tailWord_612065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612065).length < 2 ^ (prefixWord ++ tailWord_612065).sum := by decide
  have hdescent : baseEnd_612065 < baseStart_612065 := by decide
  rcases family_descends (prefixWord ++ tailWord_612065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612074 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_612074 : Nat := 118140960795 + 612074 * 2 ^ 59
def prefixEnd_612074 : Nat := 4983230072969 + 3 ^ 40 * 612074 * 2
def baseEnd_612074 : Nat := 314288158120143491360129

theorem tailTrace_612074 : CollatzResearch.WordTrace tailWord_612074 prefixEnd_612074 314288158120143491360129 := by
  unfold tailWord_612074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5581043196141976690484819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14882781856378604507959517 5581043196141976690484819)
  ·
    refine ⟨8371564794212965035727229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5581043196141976690484819 8371564794212965035727229)
    ·
      refine ⟨3139336797829861888397711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8371564794212965035727229 3139336797829861888397711)
      ·
        refine ⟨4709005196744792832596567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139336797829861888397711 4709005196744792832596567)
        ·
          refine ⟨7063507795117189248894851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709005196744792832596567 7063507795117189248894851)
          ·
            refine ⟨10595261692675783873342277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063507795117189248894851 10595261692675783873342277)
            ·
              refine ⟨1986611567376709476251677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10595261692675783873342277 1986611567376709476251677)
              ·
                refine ⟨744979337766266053594379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1986611567376709476251677 744979337766266053594379)
                ·
                  refine ⟨1117469006649399080391569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744979337766266053594379 1117469006649399080391569)
                  ·
                    refine ⟨838101754987049310293677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1117469006649399080391569 838101754987049310293677)
                    ·
                      refine ⟨314288158120143491360129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838101754987049310293677 314288158120143491360129)
                      ·
                        rfl

theorem cell23_612074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_612074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612074 prefixEnd_612074 := by exact prefixLift 612074
  have htrace : WordTrace (prefixWord ++ tailWord_612074) baseStart_612074 baseEnd_612074 := by
    simpa [prefixWord, tailWord_612074, baseEnd_612074] using wordTrace_append hprefix tailTrace_612074
  have hstable : (prefixWord ++ tailWord_612074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612074).length < 2 ^ (prefixWord ++ tailWord_612074).sum := by decide
  have hdescent : baseEnd_612074 < baseStart_612074 := by decide
  rcases family_descends (prefixWord ++ tailWord_612074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612077 : List Nat := [1, 5, 1, 2, 1, 4, 9]
def baseStart_612077 : Nat := 118140960795 + 612077 * 2 ^ 59
def prefixEnd_612077 : Nat := 4983230072969 + 3 ^ 40 * 612077 * 2
def baseEnd_612077 : Nat := 3880119735334654069415

theorem tailTrace_612077 : CollatzResearch.WordTrace tailWord_612077 prefixEnd_612077 3880119735334654069415 := by
  unfold tailWord_612077
  simp only [CollatzResearch.WordTrace]
  refine ⟨22324282203557038274298485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14882854802371358849532323 22324282203557038274298485)
  ·
    refine ⟨2092901456583472338215483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22324282203557038274298485 2092901456583472338215483)
    ·
      refine ⟨3139352184875208507323225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092901456583472338215483 3139352184875208507323225)
      ·
        refine ⟨2354514138656406380492419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139352184875208507323225 2354514138656406380492419)
        ·
          refine ⟨3531771207984609570738629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354514138656406380492419 3531771207984609570738629)
          ·
            refine ⟨662207101497114294513493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3531771207984609570738629 662207101497114294513493)
            ·
              refine ⟨3880119735334654069415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 662207101497114294513493 3880119735334654069415)
              ·
                rfl

theorem cell23_612077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 9].length) (baseStart_612077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612077 prefixEnd_612077 := by exact prefixLift 612077
  have htrace : WordTrace (prefixWord ++ tailWord_612077) baseStart_612077 baseEnd_612077 := by
    simpa [prefixWord, tailWord_612077, baseEnd_612077] using wordTrace_append hprefix tailTrace_612077
  have hstable : (prefixWord ++ tailWord_612077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612077).length < 2 ^ (prefixWord ++ tailWord_612077).sum := by decide
  have hdescent : baseEnd_612077 < baseStart_612077 := by decide
  rcases family_descends (prefixWord ++ tailWord_612077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612090 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_612090 : Nat := 118140960795 + 612090 * 2 ^ 59
def prefixEnd_612090 : Nat := 4983230072969 + 3 ^ 40 * 612090 * 2
def baseEnd_612090 : Nat := 104765457936871809586685

theorem tailTrace_612090 : CollatzResearch.WordTrace tailWord_612090 prefixEnd_612090 104765457936871809586685 := by
  unfold tailWord_612090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5581189088127485373630431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14883170901673294329681149 5581189088127485373630431)
  ·
    refine ⟨8371783632191228060445647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5581189088127485373630431 8371783632191228060445647)
    ·
      refine ⟨12557675448286842090668471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371783632191228060445647 12557675448286842090668471)
      ·
        refine ⟨18836513172430263136002707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557675448286842090668471 18836513172430263136002707)
        ·
          refine ⟨28254769758645394704004061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18836513172430263136002707 28254769758645394704004061)
          ·
            refine ⟨10595538659492023014001523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28254769758645394704004061 10595538659492023014001523)
            ·
              refine ⟨15893307989238034521002285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595538659492023014001523 15893307989238034521002285)
              ·
                refine ⟨5959990495964262945375857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15893307989238034521002285 5959990495964262945375857)
                ·
                  refine ⟨4469992871973197209031893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5959990495964262945375857 4469992871973197209031893)
                  ·
                    refine ⟨104765457936871809586685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4469992871973197209031893 104765457936871809586685)
                    ·
                      rfl

theorem cell23_612090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_612090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612090 prefixEnd_612090 := by exact prefixLift 612090
  have htrace : WordTrace (prefixWord ++ tailWord_612090) baseStart_612090 baseEnd_612090 := by
    simpa [prefixWord, tailWord_612090, baseEnd_612090] using wordTrace_append hprefix tailTrace_612090
  have hstable : (prefixWord ++ tailWord_612090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612090).length < 2 ^ (prefixWord ++ tailWord_612090).sum := by decide
  have hdescent : baseEnd_612090 < baseStart_612090 := by decide
  rcases family_descends (prefixWord ++ tailWord_612090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612094 : List Nat := [4, 2, 2, 1, 3, 1, 2, 8]
def baseStart_612094 : Nat := 118140960795 + 612094 * 2 ^ 59
def prefixEnd_612094 : Nat := 4983230072969 + 3 ^ 40 * 612094 * 2
def baseEnd_612094 : Nat := 11640682508638274559631

theorem tailTrace_612094 : CollatzResearch.WordTrace tailWord_612094 prefixEnd_612094 11640682508638274559631 := by
  unfold tailWord_612094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790612780561931272208417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14883268162996966785111557 2790612780561931272208417)
  ·
    refine ⟨2092959585421448454156313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790612780561931272208417 2092959585421448454156313)
    ·
      refine ⟨1569719689066086340617235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2092959585421448454156313 1569719689066086340617235)
      ·
        refine ⟨2354579533599129510925853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569719689066086340617235 2354579533599129510925853)
        ·
          refine ⟨882967325099673566597195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2354579533599129510925853 882967325099673566597195)
          ·
            refine ⟨1324450987649510349895793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882967325099673566597195 1324450987649510349895793)
            ·
              refine ⟨993338240737132762421845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324450987649510349895793 993338240737132762421845)
              ·
                refine ⟨11640682508638274559631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 993338240737132762421845 11640682508638274559631)
                ·
                  rfl

theorem cell23_612094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_612094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612094 prefixEnd_612094 := by exact prefixLift 612094
  have htrace : WordTrace (prefixWord ++ tailWord_612094) baseStart_612094 baseEnd_612094 := by
    simpa [prefixWord, tailWord_612094, baseEnd_612094] using wordTrace_append hprefix tailTrace_612094
  have hstable : (prefixWord ++ tailWord_612094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612094).length < 2 ^ (prefixWord ++ tailWord_612094).sum := by decide
  have hdescent : baseEnd_612094 < baseStart_612094 := by decide
  rcases family_descends (prefixWord ++ tailWord_612094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612195 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 2, 2, 2]
def baseStart_612195 : Nat := 118140960795 + 612195 * 2 ^ 59
def prefixEnd_612195 : Nat := 4983230072969 + 3 ^ 40 * 612195 * 2
def baseEnd_612195 : Nat := 314350289279337517947073

theorem tailTrace_612195 : CollatzResearch.WordTrace tailWord_612195 prefixEnd_612195 314350289279337517947073 := by
  unfold tailWord_612195
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328586017129544427094039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14885724011419696284729359 22328586017129544427094039)
  ·
    refine ⟨33492879025694316640641059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22328586017129544427094039 33492879025694316640641059)
    ·
      refine ⟨50239318538541474960961589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33492879025694316640641059 50239318538541474960961589)
      ·
        refine ⟨4709936112988263277590149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50239318538541474960961589 4709936112988263277590149)
        ·
          refine ⟨883113021185299364548153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4709936112988263277590149 883113021185299364548153)
          ·
            refine ⟨662334765888974523411115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883113021185299364548153 662334765888974523411115)
            ·
              refine ⟨993502148833461785116673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662334765888974523411115 993502148833461785116673)
              ·
                refine ⟨745126611625096338837505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993502148833461785116673 745126611625096338837505)
                ·
                  refine ⟨558844958718822254128129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745126611625096338837505 558844958718822254128129)
                  ·
                    refine ⟨419133719039116690596097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558844958718822254128129 419133719039116690596097)
                    ·
                      refine ⟨314350289279337517947073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419133719039116690596097 314350289279337517947073)
                      ·
                        rfl

theorem cell23_612195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_612195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612195 prefixEnd_612195 := by exact prefixLift 612195
  have htrace : WordTrace (prefixWord ++ tailWord_612195) baseStart_612195 baseEnd_612195 := by
    simpa [prefixWord, tailWord_612195, baseEnd_612195] using wordTrace_append hprefix tailTrace_612195
  have hstable : (prefixWord ++ tailWord_612195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612195).length < 2 ^ (prefixWord ++ tailWord_612195).sum := by decide
  have hdescent : baseEnd_612195 < baseStart_612195 := by decide
  rcases family_descends (prefixWord ++ tailWord_612195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612197 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_612197 : Nat := 118140960795 + 612197 * 2 ^ 59
def prefixEnd_612197 : Nat := 4983230072969 + 3 ^ 40 * 612197 * 2
def baseEnd_612197 : Nat := 104783772080215503374021

theorem tailTrace_612197 : CollatzResearch.WordTrace tailWord_612197 prefixEnd_612197 104783772080215503374021 := by
  unfold tailWord_612197
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328658963122298768666845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14885772642081532512444563 22328658963122298768666845)
  ·
    refine ⟨8373247111170862038250067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22328658963122298768666845 8373247111170862038250067)
    ·
      refine ⟨12559870666756293057375101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373247111170862038250067 12559870666756293057375101)
      ·
        refine ⟨4709951500033609896515663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12559870666756293057375101 4709951500033609896515663)
        ·
          refine ⟨7064927250050414844773495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709951500033609896515663 7064927250050414844773495)
          ·
            refine ⟨10597390875075622267160243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064927250050414844773495 10597390875075622267160243)
            ·
              refine ⟨15896086312613433400740365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597390875075622267160243 15896086312613433400740365)
              ·
                refine ⟨5961032367230037525277637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15896086312613433400740365 5961032367230037525277637)
                ·
                  refine ⟨1117693568855632035989557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5961032367230037525277637 1117693568855632035989557)
                  ·
                    refine ⟨104783772080215503374021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1117693568855632035989557 104783772080215503374021)
                    ·
                      rfl

theorem cell23_612197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_612197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612197 prefixEnd_612197 := by exact prefixLift 612197
  have htrace : WordTrace (prefixWord ++ tailWord_612197) baseStart_612197 baseEnd_612197 := by
    simpa [prefixWord, tailWord_612197, baseEnd_612197] using wordTrace_append hprefix tailTrace_612197
  have hstable : (prefixWord ++ tailWord_612197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612197).length < 2 ^ (prefixWord ++ tailWord_612197).sum := by decide
  have hdescent : baseEnd_612197 < baseStart_612197 := by decide
  rcases family_descends (prefixWord ++ tailWord_612197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612217 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_612217 : Nat := 118140960795 + 612217 * 2 ^ 59
def prefixEnd_612217 : Nat := 4983230072969 + 3 ^ 40 * 612217 * 2
def baseEnd_612217 : Nat := 314361585853736431871971

theorem tailTrace_612217 : CollatzResearch.WordTrace tailWord_612217 prefixEnd_612217 314361585853736431871971 := by
  unfold tailWord_612217
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329388423049842184394905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14886258948699894789596603 22329388423049842184394905)
  ·
    refine ⟨16747041317287381638296179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22329388423049842184394905 16747041317287381638296179)
    ·
      refine ⟨25120561975931072457444269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16747041317287381638296179 25120561975931072457444269)
      ·
        refine ⟨9420210740974152171541601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25120561975931072457444269 9420210740974152171541601)
        ·
          refine ⟨7065158055730614128656201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9420210740974152171541601 7065158055730614128656201)
          ·
            refine ⟨5298868541797960596492151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7065158055730614128656201 5298868541797960596492151)
            ·
              refine ⟨7948302812696940894738227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298868541797960596492151 7948302812696940894738227)
              ·
                refine ⟨11922454219045411342107341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948302812696940894738227 11922454219045411342107341)
                ·
                  refine ⟨4470920332142029253290253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11922454219045411342107341 4470920332142029253290253)
                  ·
                    refine ⟨1676595124553260969983845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4470920332142029253290253 1676595124553260969983845)
                    ·
                      refine ⟨314361585853736431871971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1676595124553260969983845 314361585853736431871971)
                      ·
                        rfl

theorem cell23_612217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_612217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612217 prefixEnd_612217 := by exact prefixLift 612217
  have htrace : WordTrace (prefixWord ++ tailWord_612217) baseStart_612217 baseEnd_612217 := by
    simpa [prefixWord, tailWord_612217, baseEnd_612217] using wordTrace_append hprefix tailTrace_612217
  have hstable : (prefixWord ++ tailWord_612217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612217).length < 2 ^ (prefixWord ++ tailWord_612217).sum := by decide
  have hdescent : baseEnd_612217 < baseStart_612217 := by decide
  rcases family_descends (prefixWord ++ tailWord_612217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612261 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_612261 : Nat := 118140960795 + 612261 * 2 ^ 59
def prefixEnd_612261 : Nat := 4983230072969 + 3 ^ 40 * 612261 * 2
def baseEnd_612261 : Nat := 104794726334178086573923

theorem tailTrace_612261 : CollatzResearch.WordTrace tailWord_612261 prefixEnd_612261 104794726334178086573923 := by
  unfold tailWord_612261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330993234890437698996637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14887328823260291799331091 22330993234890437698996637)
  ·
    refine ⟨8374122463083914137123739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22330993234890437698996637 8374122463083914137123739)
    ·
      refine ⟨12561183694625871205685609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8374122463083914137123739 12561183694625871205685609)
      ·
        refine ⟨9420887770969403404264207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12561183694625871205685609 9420887770969403404264207)
        ·
          refine ⟨14131331656454105106396311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420887770969403404264207 14131331656454105106396311)
          ·
            refine ⟨21196997484681157659594467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14131331656454105106396311 21196997484681157659594467)
            ·
              refine ⟨31795496227021736489391701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21196997484681157659594467 31795496227021736489391701)
              ·
                refine ⟨372603471410410974485059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 31795496227021736489391701 372603471410410974485059)
                ·
                  refine ⟨558905207115616461727589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372603471410410974485059 558905207115616461727589)
                  ·
                    refine ⟨104794726334178086573923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 558905207115616461727589 104794726334178086573923)
                    ·
                      rfl

theorem cell23_612261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_612261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612261 prefixEnd_612261 := by exact prefixLift 612261
  have htrace : WordTrace (prefixWord ++ tailWord_612261) baseStart_612261 baseEnd_612261 := by
    simpa [prefixWord, tailWord_612261, baseEnd_612261] using wordTrace_append hprefix tailTrace_612261
  have hstable : (prefixWord ++ tailWord_612261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612261).length < 2 ^ (prefixWord ++ tailWord_612261).sum := by decide
  have hdescent : baseEnd_612261 < baseStart_612261 := by decide
  rcases family_descends (prefixWord ++ tailWord_612261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612304 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_612304 : Nat := 118140960795 + 612304 * 2 ^ 59
def prefixEnd_612304 : Nat := 4983230072969 + 3 ^ 40 * 612304 * 2
def baseEnd_612304 : Nat := 104802086223559197161357

theorem tailTrace_612304 : CollatzResearch.WordTrace tailWord_612304 prefixEnd_612304 104802086223559197161357 := by
  unfold tailWord_612304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166280786867328021405983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14888374382489770695207977 11166280786867328021405983)
  ·
    refine ⟨16749421180300992032108975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11166280786867328021405983 16749421180300992032108975)
    ·
      refine ⟨25124131770451488048163463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16749421180300992032108975 25124131770451488048163463)
      ·
        refine ⟨37686197655677232072245195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25124131770451488048163463 37686197655677232072245195)
        ·
          refine ⟨56529296483515848108367793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37686197655677232072245195 56529296483515848108367793)
          ·
            refine ⟨42396972362636886081275845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56529296483515848108367793 42396972362636886081275845)
            ·
              refine ⟨7949432317994416140239221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42396972362636886081275845 7949432317994416140239221)
              ·
                refine ⟨745259279811976513147427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7949432317994416140239221 745259279811976513147427)
                ·
                  refine ⟨1117888919717964769721141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745259279811976513147427 1117888919717964769721141)
                  ·
                    refine ⟨104802086223559197161357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1117888919717964769721141 104802086223559197161357)
                    ·
                      rfl

theorem cell23_612304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_612304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612304 prefixEnd_612304 := by exact prefixLift 612304
  have htrace : WordTrace (prefixWord ++ tailWord_612304) baseStart_612304 baseEnd_612304 := by
    simpa [prefixWord, tailWord_612304, baseEnd_612304] using wordTrace_append hprefix tailTrace_612304
  have hstable : (prefixWord ++ tailWord_612304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612304).length < 2 ^ (prefixWord ++ tailWord_612304).sum := by decide
  have hdescent : baseEnd_612304 < baseStart_612304 := by decide
  rcases family_descends (prefixWord ++ tailWord_612304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612311 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_612311 : Nat := 118140960795 + 612311 * 2 ^ 59
def prefixEnd_612311 : Nat := 4983230072969 + 3 ^ 40 * 612311 * 2
def baseEnd_612311 : Nat := 314409853035259064096539

theorem tailTrace_612311 : CollatzResearch.WordTrace tailWord_612311 prefixEnd_612311 314409853035259064096539 := by
  unfold tailWord_612311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332816884709296238316787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14888544589806197492211191 22332816884709296238316787)
  ·
    refine ⟨33499225327063944357475181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22332816884709296238316787 33499225327063944357475181)
    ·
      refine ⟨12562209497648979134053193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33499225327063944357475181 12562209497648979134053193)
      ·
        refine ⟨9421657123236734350539895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12562209497648979134053193 9421657123236734350539895)
        ·
          refine ⟨14132485684855101525809843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421657123236734350539895 14132485684855101525809843)
          ·
            refine ⟨21198728527282652288714765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132485684855101525809843 21198728527282652288714765)
            ·
              refine ⟨7949523197730994608268037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21198728527282652288714765 7949523197730994608268037)
              ·
                refine ⟨1490535599574561489050257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7949523197730994608268037 1490535599574561489050257)
                ·
                  refine ⟨1117901699680921116787693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490535599574561489050257 1117901699680921116787693)
                  ·
                    refine ⟨419213137380345418795385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117901699680921116787693 419213137380345418795385)
                    ·
                      refine ⟨314409853035259064096539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419213137380345418795385 314409853035259064096539)
                      ·
                        rfl

theorem cell23_612311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_612311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612311 prefixEnd_612311 := by exact prefixLift 612311
  have htrace : WordTrace (prefixWord ++ tailWord_612311) baseStart_612311 baseEnd_612311 := by
    simpa [prefixWord, tailWord_612311, baseEnd_612311] using wordTrace_append hprefix tailTrace_612311
  have hstable : (prefixWord ++ tailWord_612311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612311).length < 2 ^ (prefixWord ++ tailWord_612311).sum := by decide
  have hdescent : baseEnd_612311 < baseStart_612311 := by decide
  rcases family_descends (prefixWord ++ tailWord_612311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612324 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_612324 : Nat := 118140960795 + 612324 * 2 ^ 59
def prefixEnd_612324 : Nat := 4983230072969 + 3 ^ 40 * 612324 * 2
def baseEnd_612324 : Nat := 314416528283767513233979

theorem tailTrace_612324 : CollatzResearch.WordTrace tailWord_612324 prefixEnd_612324 314416528283767513233979 := by
  unfold tailWord_612324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166645516831099729270013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14888860689108132972360017 11166645516831099729270013)
  ·
    refine ⟨4187492068811662398476255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11166645516831099729270013 4187492068811662398476255)
    ·
      refine ⟨6281238103217493597714383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4187492068811662398476255 6281238103217493597714383)
      ·
        refine ⟨9421857154826240396571575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281238103217493597714383 9421857154826240396571575)
        ·
          refine ⟨14132785732239360594857363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421857154826240396571575 14132785732239360594857363)
          ·
            refine ⟨21199178598359040892286045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132785732239360594857363 21199178598359040892286045)
            ·
              refine ⟨7949691974384640334607267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21199178598359040892286045 7949691974384640334607267)
              ·
                refine ⟨11924537961576960501910901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949691974384640334607267 11924537961576960501910901)
                ·
                  refine ⟨1117925433897840047054147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11924537961576960501910901 1117925433897840047054147)
                  ·
                    refine ⟨1676888150846760070581221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1117925433897840047054147 1676888150846760070581221)
                    ·
                      refine ⟨314416528283767513233979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1676888150846760070581221 314416528283767513233979)
                      ·
                        rfl

theorem cell23_612324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_612324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612324 prefixEnd_612324 := by exact prefixLift 612324
  have htrace : WordTrace (prefixWord ++ tailWord_612324) baseStart_612324 baseEnd_612324 := by
    simpa [prefixWord, tailWord_612324, baseEnd_612324] using wordTrace_append hprefix tailTrace_612324
  have hstable : (prefixWord ++ tailWord_612324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612324).length < 2 ^ (prefixWord ++ tailWord_612324).sum := by decide
  have hdescent : baseEnd_612324 < baseStart_612324 := by decide
  rcases family_descends (prefixWord ++ tailWord_612324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612347 : List Nat := [1, 1, 1, 1, 1, 3, 4, 11]
def baseStart_612347 : Nat := 118140960795 + 612347 * 2 ^ 59
def prefixEnd_612347 : Nat := 4983230072969 + 3 ^ 40 * 612347 * 2
def baseEnd_612347 : Nat := 11645494012548923083199

theorem tailTrace_612347 : CollatzResearch.WordTrace tailWord_612347 prefixEnd_612347 11645494012548923083199 := by
  unfold tailWord_612347
  simp only [CollatzResearch.WordTrace]
  refine ⟨22334129912578874386627295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14889419941719249591084863 22334129912578874386627295)
  ·
    refine ⟨33501194868868311579940943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22334129912578874386627295 33501194868868311579940943)
    ·
      refine ⟨50251792303302467369911415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33501194868868311579940943 50251792303302467369911415)
      ·
        refine ⟨75377688454953701054867123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50251792303302467369911415 75377688454953701054867123)
        ·
          refine ⟨113066532682430551582300685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75377688454953701054867123 113066532682430551582300685)
          ·
            refine ⟨42399949755911456843362757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113066532682430551582300685 42399949755911456843362757)
            ·
              refine ⟨7949990579233398158130517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42399949755911456843362757 7949990579233398158130517)
              ·
                refine ⟨11645494012548923083199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7949990579233398158130517 11645494012548923083199)
                ·
                  rfl

theorem cell23_612347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 11].length) (baseStart_612347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612347 prefixEnd_612347 := by exact prefixLift 612347
  have htrace : WordTrace (prefixWord ++ tailWord_612347) baseStart_612347 baseEnd_612347 := by
    simpa [prefixWord, tailWord_612347, baseEnd_612347] using wordTrace_append hprefix tailTrace_612347
  have hstable : (prefixWord ++ tailWord_612347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612347).length < 2 ^ (prefixWord ++ tailWord_612347).sum := by decide
  have hdescent : baseEnd_612347 < baseStart_612347 := by decide
  rcases family_descends (prefixWord ++ tailWord_612347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612385 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_612385 : Nat := 118140960795 + 612385 * 2 ^ 59
def prefixEnd_612385 : Nat := 4983230072969 + 3 ^ 40 * 612385 * 2
def baseEnd_612385 : Nat := 104815950201230591523733

theorem tailTrace_612385 : CollatzResearch.WordTrace tailWord_612385 prefixEnd_612385 104815950201230591523733 := by
  unfold tailWord_612385
  simp only [CollatzResearch.WordTrace]
  refine ⟨22335515886441206876510609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14890343924294137917673739 22335515886441206876510609)
  ·
    refine ⟨16751636914830905157382957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22335515886441206876510609 16751636914830905157382957)
    ·
      refine ⟨6281863843061589434018609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16751636914830905157382957 6281863843061589434018609)
      ·
        refine ⟨4711397882296192075513957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6281863843061589434018609 4711397882296192075513957)
        ·
          refine ⟨883387102930536014158867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4711397882296192075513957 883387102930536014158867)
          ·
            refine ⟨1325080654395804021238301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883387102930536014158867 1325080654395804021238301)
            ·
              refine ⟨496905245398426507964363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1325080654395804021238301 496905245398426507964363)
              ·
                refine ⟨745357868097639761946545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496905245398426507964363 745357868097639761946545)
                ·
                  refine ⟨559018401073229821459909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745357868097639761946545 559018401073229821459909)
                  ·
                    refine ⟨104815950201230591523733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559018401073229821459909 104815950201230591523733)
                    ·
                      rfl

theorem cell23_612385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_612385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612385 prefixEnd_612385 := by exact prefixLift 612385
  have htrace : WordTrace (prefixWord ++ tailWord_612385) baseStart_612385 baseEnd_612385 := by
    simpa [prefixWord, tailWord_612385, baseEnd_612385] using wordTrace_append hprefix tailTrace_612385
  have hstable : (prefixWord ++ tailWord_612385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612385).length < 2 ^ (prefixWord ++ tailWord_612385).sum := by decide
  have hdescent : baseEnd_612385 < baseStart_612385 := by decide
  rcases family_descends (prefixWord ++ tailWord_612385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612398 : List Nat := [4, 1, 3, 1, 1, 4, 2, 7]
def baseStart_612398 : Nat := 118140960795 + 612398 * 2 ^ 59
def prefixEnd_612398 : Nat := 4983230072969 + 3 ^ 40 * 612398 * 2
def baseEnd_612398 : Nat := 11646463920451860137357

theorem tailTrace_612398 : CollatzResearch.WordTrace tailWord_612398 prefixEnd_612398 11646463920451860137357 := by
  unfold tailWord_612398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2791998754424263762091731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14890660023596073397822565 2791998754424263762091731)
  ·
    refine ⟨4187998131636395643137597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2791998754424263762091731 4187998131636395643137597)
    ·
      refine ⟨1570499299363648366176599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4187998131636395643137597 1570499299363648366176599)
      ·
        refine ⟨2355748949045472549264899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570499299363648366176599 2355748949045472549264899)
        ·
          refine ⟨3533623423568208823897349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355748949045472549264899 3533623423568208823897349)
          ·
            refine ⟨662554391919039154480753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3533623423568208823897349 662554391919039154480753)
            ·
              refine ⟨496915793939279365860565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662554391919039154480753 496915793939279365860565)
              ·
                refine ⟨11646463920451860137357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 496915793939279365860565 11646463920451860137357)
                ·
                  rfl

theorem cell23_612398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_612398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612398 prefixEnd_612398 := by exact prefixLift 612398
  have htrace : WordTrace (prefixWord ++ tailWord_612398) baseStart_612398 baseEnd_612398 := by
    simpa [prefixWord, tailWord_612398, baseEnd_612398] using wordTrace_append hprefix tailTrace_612398
  have hstable : (prefixWord ++ tailWord_612398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612398).length < 2 ^ (prefixWord ++ tailWord_612398).sum := by decide
  have hdescent : baseEnd_612398 < baseStart_612398 := by decide
  rcases family_descends (prefixWord ++ tailWord_612398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612409 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 1, 2, 2]
def baseStart_612409 : Nat := 118140960795 + 612409 * 2 ^ 59
def prefixEnd_612409 : Nat := 4983230072969 + 3 ^ 40 * 612409 * 2
def baseEnd_612409 : Nat := 314460174139399680671089

theorem tailTrace_612409 : CollatzResearch.WordTrace tailWord_612409 prefixEnd_612409 314460174139399680671089 := by
  unfold tailWord_612409
  simp only [CollatzResearch.WordTrace]
  refine ⟨22336391238354258975384281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14890927492236172650256187 22336391238354258975384281)
  ·
    refine ⟨16752293428765694231538211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22336391238354258975384281 16752293428765694231538211)
    ·
      refine ⟨25128440143148541347307317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16752293428765694231538211 25128440143148541347307317)
      ·
        refine ⟨2355791263420175751310061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25128440143148541347307317 2355791263420175751310061)
        ·
          refine ⟨883421723782565906741273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2355791263420175751310061 883421723782565906741273)
          ·
            refine ⟨662566292836924430055955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883421723782565906741273 662566292836924430055955)
            ·
              refine ⟨993849439255386645083933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662566292836924430055955 993849439255386645083933)
              ·
                refine ⟨372693539720769991906475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993849439255386645083933 372693539720769991906475)
                ·
                  refine ⟨559040309581154987859713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372693539720769991906475 559040309581154987859713)
                  ·
                    refine ⟨419280232185866240894785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559040309581154987859713 419280232185866240894785)
                    ·
                      refine ⟨314460174139399680671089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419280232185866240894785 314460174139399680671089)
                      ·
                        rfl

theorem cell23_612409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_612409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612409 prefixEnd_612409 := by exact prefixLift 612409
  have htrace : WordTrace (prefixWord ++ tailWord_612409) baseStart_612409 baseEnd_612409 := by
    simpa [prefixWord, tailWord_612409, baseEnd_612409] using wordTrace_append hprefix tailTrace_612409
  have hstable : (prefixWord ++ tailWord_612409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612409).length < 2 ^ (prefixWord ++ tailWord_612409).sum := by decide
  have hdescent : baseEnd_612409 < baseStart_612409 := by decide
  rcases family_descends (prefixWord ++ tailWord_612409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612424 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_612424 : Nat := 118140960795 + 612424 * 2 ^ 59
def prefixEnd_612424 : Nat := 4983230072969 + 3 ^ 40 * 612424 * 2
def baseEnd_612424 : Nat := 104822625449739040661173

theorem tailTrace_612424 : CollatzResearch.WordTrace tailWord_612424 prefixEnd_612424 104822625449739040661173 := by
  unfold tailWord_612424
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168469166649958268590163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14891292222199944358120217 11168469166649958268590163)
  ·
    refine ⟨16752703749974937402885245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168469166649958268590163 16752703749974937402885245)
    ·
      refine ⟨6282263906240601526081967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16752703749974937402885245 6282263906240601526081967)
      ·
        refine ⟨9423395859360902289122951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282263906240601526081967 9423395859360902289122951)
        ·
          refine ⟨14135093789041353433684427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423395859360902289122951 14135093789041353433684427)
          ·
            refine ⟨21202640683562030150526641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14135093789041353433684427 21202640683562030150526641)
            ·
              refine ⟨15901980512671522612894981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21202640683562030150526641 15901980512671522612894981)
              ·
                refine ⟨2981621346125910489917809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15901980512671522612894981 2981621346125910489917809)
                ·
                  refine ⟨2236216009594432867438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981621346125910489917809 2236216009594432867438357)
                  ·
                    refine ⟨104822625449739040661173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2236216009594432867438357 104822625449739040661173)
                    ·
                      rfl

theorem cell23_612424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_612424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612424 prefixEnd_612424 := by exact prefixLift 612424
  have htrace : WordTrace (prefixWord ++ tailWord_612424) baseStart_612424 baseEnd_612424 := by
    simpa [prefixWord, tailWord_612424, baseEnd_612424] using wordTrace_append hprefix tailTrace_612424
  have hstable : (prefixWord ++ tailWord_612424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612424).length < 2 ^ (prefixWord ++ tailWord_612424).sum := by decide
  have hdescent : baseEnd_612424 < baseStart_612424 := by decide
  rcases family_descends (prefixWord ++ tailWord_612424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 4, 2]
def baseStart_612431 : Nat := 118140960795 + 612431 * 2 ^ 59
def prefixEnd_612431 : Nat := 4983230072969 + 3 ^ 40 * 612431 * 2
def baseEnd_612431 : Nat := 314471470713798594595987

theorem tailTrace_612431 : CollatzResearch.WordTrace tailWord_612431 prefixEnd_612431 314471470713798594595987 := by
  unfold tailWord_612431
  simp only [CollatzResearch.WordTrace]
  refine ⟨22337193644274556732685147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14891462429516371155123431 22337193644274556732685147)
  ·
    refine ⟨33505790466411835099027721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22337193644274556732685147 33505790466411835099027721)
    ·
      refine ⟨25129342849808876324270791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33505790466411835099027721 25129342849808876324270791)
      ·
        refine ⟨37694014274713314486406187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25129342849808876324270791 37694014274713314486406187)
        ·
          refine ⟨56541021412069971729609281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37694014274713314486406187 56541021412069971729609281)
          ·
            refine ⟨42405766059052478797206961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56541021412069971729609281 42405766059052478797206961)
            ·
              refine ⟨31804324544289359097905221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42405766059052478797206961 31804324544289359097905221)
              ·
                refine ⟨5963310852054254830857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31804324544289359097905221 5963310852054254830857229)
                ·
                  refine ⟨2236241569520345561571461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963310852054254830857229 2236241569520345561571461)
                  ·
                    refine ⟨419295294285064792794649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236241569520345561571461 419295294285064792794649)
                    ·
                      refine ⟨314471470713798594595987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419295294285064792794649 314471470713798594595987)
                      ·
                        rfl

theorem cell23_612431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4, 2].length) (baseStart_612431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612431 prefixEnd_612431 := by exact prefixLift 612431
  have htrace : WordTrace (prefixWord ++ tailWord_612431) baseStart_612431 baseEnd_612431 := by
    simpa [prefixWord, tailWord_612431, baseEnd_612431] using wordTrace_append hprefix tailTrace_612431
  have hstable : (prefixWord ++ tailWord_612431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612431).length < 2 ^ (prefixWord ++ tailWord_612431).sum := by decide
  have hdescent : baseEnd_612431 < baseStart_612431 := by decide
  rcases family_descends (prefixWord ++ tailWord_612431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612446 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_612446 : Nat := 118140960795 + 612446 * 2 ^ 59
def prefixEnd_612446 : Nat := 4983230072969 + 3 ^ 40 * 612446 * 2
def baseEnd_612446 : Nat := 314479172923616035908419

theorem tailTrace_612446 : CollatzResearch.WordTrace tailWord_612446 prefixEnd_612446 314479172923616035908419 := by
  unfold tailWord_612446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792217592402526786810149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14891827159480142862987461 2792217592402526786810149)
  ·
    refine ⟨523540798575473772526903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2792217592402526786810149 523540798575473772526903)
    ·
      refine ⟨785311197863210658790355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523540798575473772526903 785311197863210658790355)
      ·
        refine ⟨1177966796794815988185533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785311197863210658790355 1177966796794815988185533)
        ·
          refine ⟨441737548798055995569575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1177966796794815988185533 441737548798055995569575)
          ·
            refine ⟨662606323197083993354363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441737548798055995569575 662606323197083993354363)
            ·
              refine ⟨993909484795625990031545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662606323197083993354363 993909484795625990031545)
              ·
                refine ⟨745432113596719492523659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993909484795625990031545 745432113596719492523659)
                ·
                  refine ⟨1118148170395079238785489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745432113596719492523659 1118148170395079238785489)
                  ·
                    refine ⟨838611127796309429089117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1118148170395079238785489 838611127796309429089117)
                    ·
                      refine ⟨314479172923616035908419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838611127796309429089117 314479172923616035908419)
                      ·
                        rfl

theorem cell23_612446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_612446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612446 prefixEnd_612446 := by exact prefixLift 612446
  have htrace : WordTrace (prefixWord ++ tailWord_612446) baseStart_612446 baseEnd_612446 := by
    simpa [prefixWord, tailWord_612446, baseEnd_612446] using wordTrace_append hprefix tailTrace_612446
  have hstable : (prefixWord ++ tailWord_612446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612446).length < 2 ^ (prefixWord ++ tailWord_612446).sum := by decide
  have hdescent : baseEnd_612446 < baseStart_612446 := by decide
  rcases family_descends (prefixWord ++ tailWord_612446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612498 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_612498 : Nat := 118140960795 + 612498 * 2 ^ 59
def prefixEnd_612498 : Nat := 4983230072969 + 3 ^ 40 * 612498 * 2
def baseEnd_612498 : Nat := 314505873917649832458179

theorem tailTrace_612498 : CollatzResearch.WordTrace tailWord_612498 prefixEnd_612498 314505873917649832458179 := by
  unfold tailWord_612498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584909333757956793843537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14893091556687884783582765 5584909333757956793843537)
  ·
    refine ⟨4188682000318467595382653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5584909333757956793843537 4188682000318467595382653)
    ·
      refine ⟨1570755750119425348268495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4188682000318467595382653 1570755750119425348268495)
      ·
        refine ⟨2356133625179138022402743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570755750119425348268495 2356133625179138022402743)
        ·
          refine ⟨3534200437768707033604115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356133625179138022402743 3534200437768707033604115)
          ·
            refine ⟨5301300656653060550406173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534200437768707033604115 5301300656653060550406173)
            ·
              refine ⟨1987987746244897706402315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5301300656653060550406173 1987987746244897706402315)
              ·
                refine ⟨2981981619367346559603473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987987746244897706402315 2981981619367346559603473)
                ·
                  refine ⟨2236486214525509919702605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981981619367346559603473 2236486214525509919702605)
                  ·
                    refine ⟨838682330447066219888477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236486214525509919702605 838682330447066219888477)
                    ·
                      refine ⟨314505873917649832458179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838682330447066219888477 314505873917649832458179)
                      ·
                        rfl

theorem cell23_612498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_612498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612498 prefixEnd_612498 := by exact prefixLift 612498
  have htrace : WordTrace (prefixWord ++ tailWord_612498) baseStart_612498 baseEnd_612498 := by
    simpa [prefixWord, tailWord_612498, baseEnd_612498] using wordTrace_append hprefix tailTrace_612498
  have hstable : (prefixWord ++ tailWord_612498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612498).length < 2 ^ (prefixWord ++ tailWord_612498).sum := by decide
  have hdescent : baseEnd_612498 < baseStart_612498 := by decide
  rcases family_descends (prefixWord ++ tailWord_612498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612508 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_612508 : Nat := 118140960795 + 612508 * 2 ^ 59
def prefixEnd_612508 : Nat := 4983230072969 + 3 ^ 40 * 612508 * 2
def baseEnd_612508 : Nat := 314511008724194793333133

theorem tailTrace_612508 : CollatzResearch.WordTrace tailWord_612508 prefixEnd_612508 314511008724194793333133 := by
  unfold tailWord_612508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170001032497799441619089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14893334709997065922158785 11170001032497799441619089)
  ·
    refine ⟨8377500774373349581214317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11170001032497799441619089 8377500774373349581214317)
    ·
      refine ⟨3141562790390006092955369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8377500774373349581214317 3141562790390006092955369)
      ·
        refine ⟨2356172092792504569716527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141562790390006092955369 2356172092792504569716527)
        ·
          refine ⟨3534258139188756854574791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356172092792504569716527 3534258139188756854574791)
          ·
            refine ⟨5301387208783135281862187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534258139188756854574791 5301387208783135281862187)
            ·
              refine ⟨7952080813174702922793281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301387208783135281862187 7952080813174702922793281)
              ·
                refine ⟨5964060609881027192094961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7952080813174702922793281 5964060609881027192094961)
                ·
                  refine ⟨4473045457410770394071221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5964060609881027192094961 4473045457410770394071221)
                  ·
                    refine ⟨419348011632259724444177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4473045457410770394071221 419348011632259724444177)
                    ·
                      refine ⟨314511008724194793333133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419348011632259724444177 314511008724194793333133)
                      ·
                        rfl

theorem cell23_612508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_612508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612508 prefixEnd_612508 := by exact prefixLift 612508
  have htrace : WordTrace (prefixWord ++ tailWord_612508) baseStart_612508 baseEnd_612508 := by
    simpa [prefixWord, tailWord_612508, baseEnd_612508] using wordTrace_append hprefix tailTrace_612508
  have hstable : (prefixWord ++ tailWord_612508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612508).length < 2 ^ (prefixWord ++ tailWord_612508).sum := by decide
  have hdescent : baseEnd_612508 < baseStart_612508 := by decide
  rcases family_descends (prefixWord ++ tailWord_612508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612522 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_612522 : Nat := 118140960795 + 612522 * 2 ^ 59
def prefixEnd_612522 : Nat := 4983230072969 + 3 ^ 40 * 612522 * 2
def baseEnd_612522 : Nat := 34946466383706415395341

theorem tailTrace_612522 : CollatzResearch.WordTrace tailWord_612522 prefixEnd_612522 34946466383706415395341 := by
  unfold tailWord_612522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585128171736219818561955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14893675124629919516165213 5585128171736219818561955)
  ·
    refine ⟨8377692257604329727842933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5585128171736219818561955 8377692257604329727842933)
    ·
      refine ⟨785408649150405911985275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8377692257604329727842933 785408649150405911985275)
      ·
        refine ⟨1178112973725608867977913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785408649150405911985275 1178112973725608867977913)
        ·
          refine ⟨883584730294206650983435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178112973725608867977913 883584730294206650983435)
          ·
            refine ⟨1325377095441309976475153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883584730294206650983435 1325377095441309976475153)
            ·
              refine ⟨994032821580982482356365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325377095441309976475153 994032821580982482356365)
              ·
                refine ⟨372762308092868430883637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 994032821580982482356365 372762308092868430883637)
                ·
                  refine ⟨34946466383706415395341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372762308092868430883637 34946466383706415395341)
                  ·
                    rfl

theorem cell23_612522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_612522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612522 prefixEnd_612522 := by exact prefixLift 612522
  have htrace : WordTrace (prefixWord ++ tailWord_612522) baseStart_612522 baseEnd_612522 := by
    simpa [prefixWord, tailWord_612522, baseEnd_612522] using wordTrace_append hprefix tailTrace_612522
  have hstable : (prefixWord ++ tailWord_612522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612522).length < 2 ^ (prefixWord ++ tailWord_612522).sum := by decide
  have hdescent : baseEnd_612522 < baseStart_612522 := by decide
  rcases family_descends (prefixWord ++ tailWord_612522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612531 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 7, 4]
def baseStart_612531 : Nat := 118140960795 + 612531 * 2 ^ 59
def prefixEnd_612531 : Nat := 4983230072969 + 3 ^ 40 * 612531 * 2
def baseEnd_612531 : Nat := 104840939593082734448509

theorem tailTrace_612531 : CollatzResearch.WordTrace tailWord_612531 prefixEnd_612531 104840939593082734448509 := by
  unfold tailWord_612531
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340840943912273811325447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14893893962608182540883631 22340840943912273811325447)
  ·
    refine ⟨33511261415868410716988171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22340840943912273811325447 33511261415868410716988171)
    ·
      refine ⟨50266892123802616075482257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33511261415868410716988171 50266892123802616075482257)
      ·
        refine ⟨37700169092851962056611693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50266892123802616075482257 37700169092851962056611693)
        ·
          refine ⟨14137563409819485771229385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37700169092851962056611693 14137563409819485771229385)
          ·
            refine ⟨10603172557364614328422039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14137563409819485771229385 10603172557364614328422039)
            ·
              refine ⟨15904758836046921492633059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603172557364614328422039 15904758836046921492633059)
              ·
                refine ⟨23857138254070382238949589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15904758836046921492633059 23857138254070382238949589)
                ·
                  refine ⟨559151677829774583725381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23857138254070382238949589 559151677829774583725381)
                  ·
                    refine ⟨104840939593082734448509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559151677829774583725381 104840939593082734448509)
                    ·
                      rfl

theorem cell23_612531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 4].length) (baseStart_612531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612531 prefixEnd_612531 := by exact prefixLift 612531
  have htrace : WordTrace (prefixWord ++ tailWord_612531) baseStart_612531 baseEnd_612531 := by
    simpa [prefixWord, tailWord_612531, baseEnd_612531] using wordTrace_append hprefix tailTrace_612531
  have hstable : (prefixWord ++ tailWord_612531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612531).length < 2 ^ (prefixWord ++ tailWord_612531).sum := by decide
  have hdescent : baseEnd_612531 < baseStart_612531 := by decide
  rcases family_descends (prefixWord ++ tailWord_612531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612538 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_612538 : Nat := 118140960795 + 612538 * 2 ^ 59
def prefixEnd_612538 : Nat := 4983230072969 + 3 ^ 40 * 612538 * 2
def baseEnd_612538 : Nat := 314526413143829675957995

theorem tailTrace_612538 : CollatzResearch.WordTrace tailWord_612538 prefixEnd_612538 314526413143829675957995 := by
  unfold tailWord_612538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585274063721728501707567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14894064169924609337886845 5585274063721728501707567)
  ·
    refine ⟨8377911095582592752561351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5585274063721728501707567 8377911095582592752561351)
    ·
      refine ⟨12566866643373889128842027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377911095582592752561351 12566866643373889128842027)
      ·
        refine ⟨18850299965060833693263041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12566866643373889128842027 18850299965060833693263041)
        ·
          refine ⟨14137724973795625269947281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18850299965060833693263041 14137724973795625269947281)
          ·
            refine ⟨10603293730346718952460461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14137724973795625269947281 10603293730346718952460461)
            ·
              refine ⟨3976235148880019607172673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10603293730346718952460461 3976235148880019607172673)
              ·
                refine ⟨2982176361660014705379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976235148880019607172673 2982176361660014705379505)
                ·
                  refine ⟨2236632271245011029034629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982176361660014705379505 2236632271245011029034629)
                  ·
                    refine ⟨419368550858439567943993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236632271245011029034629 419368550858439567943993)
                    ·
                      refine ⟨314526413143829675957995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419368550858439567943993 314526413143829675957995)
                      ·
                        rfl

theorem cell23_612538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_612538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612538 prefixEnd_612538 := by exact prefixLift 612538
  have htrace : WordTrace (prefixWord ++ tailWord_612538) baseStart_612538 baseEnd_612538 := by
    simpa [prefixWord, tailWord_612538, baseEnd_612538] using wordTrace_append hprefix tailTrace_612538
  have hstable : (prefixWord ++ tailWord_612538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612538).length < 2 ^ (prefixWord ++ tailWord_612538).sum := by decide
  have hdescent : baseEnd_612538 < baseStart_612538 := by decide
  rcases family_descends (prefixWord ++ tailWord_612538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612558 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_612558 : Nat := 118140960795 + 612558 * 2 ^ 59
def prefixEnd_612558 : Nat := 4983230072969 + 3 ^ 40 * 612558 * 2
def baseEnd_612558 : Nat := 314536682756919597707903

theorem tailTrace_612558 : CollatzResearch.WordTrace tailWord_612558 prefixEnd_612558 314536682756919597707903 := by
  unfold tailWord_612558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792728214351807177819791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14894550476542971615038885 2792728214351807177819791)
  ·
    refine ⟨4189092321527710766729687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2792728214351807177819791 4189092321527710766729687)
    ·
      refine ⟨6283638482291566150094531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189092321527710766729687 6283638482291566150094531)
      ·
        refine ⟨9425457723437349225141797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283638482291566150094531 9425457723437349225141797)
        ·
          refine ⟨1767273323144502979714087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9425457723437349225141797 1767273323144502979714087)
          ·
            refine ⟨2650909984716754469571131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767273323144502979714087 2650909984716754469571131)
            ·
              refine ⟨3976364977075131704356697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650909984716754469571131 3976364977075131704356697)
              ·
                refine ⟨2982273732806348778267523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976364977075131704356697 2982273732806348778267523)
                ·
                  refine ⟨4473410599209523167401285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982273732806348778267523 4473410599209523167401285)
                  ·
                    refine ⟨838764487351785593887741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4473410599209523167401285 838764487351785593887741)
                    ·
                      refine ⟨314536682756919597707903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838764487351785593887741 314536682756919597707903)
                      ·
                        rfl

theorem cell23_612558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_612558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612558 prefixEnd_612558 := by exact prefixLift 612558
  have htrace : WordTrace (prefixWord ++ tailWord_612558) baseStart_612558 baseEnd_612558 := by
    simpa [prefixWord, tailWord_612558, baseEnd_612558] using wordTrace_append hprefix tailTrace_612558
  have hstable : (prefixWord ++ tailWord_612558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612558).length < 2 ^ (prefixWord ++ tailWord_612558).sum := by decide
  have hdescent : baseEnd_612558 < baseStart_612558 := by decide
  rcases family_descends (prefixWord ++ tailWord_612558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612561 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 6]
def baseStart_612561 : Nat := 118140960795 + 612561 * 2 ^ 59
def prefixEnd_612561 : Nat := 4983230072969 + 3 ^ 40 * 612561 * 2
def baseEnd_612561 : Nat := 34948691466542565107821

theorem tailTrace_612561 : CollatzResearch.WordTrace tailWord_612561 prefixEnd_612561 34948691466542565107821 := by
  unfold tailWord_612561
  simp only [CollatzResearch.WordTrace]
  refine ⟨22341935133803588934917537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14894623422535725956611691 22341935133803588934917537)
  ·
    refine ⟨16756451350352691701188153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22341935133803588934917537 16756451350352691701188153)
    ·
      refine ⟨12567338512764518775891115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16756451350352691701188153 12567338512764518775891115)
      ·
        refine ⟨18851007769146778163836673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12567338512764518775891115 18851007769146778163836673)
        ·
          refine ⟨14138255826860083622877505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18851007769146778163836673 14138255826860083622877505)
          ·
            refine ⟨10603691870145062717158129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14138255826860083622877505 10603691870145062717158129)
            ·
              refine ⟨7952768902608797037868597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10603691870145062717158129 7952768902608797037868597)
              ·
                refine ⟨745572084619574722300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7952768902608797037868597 745572084619574722300181)
                ·
                  refine ⟨34948691466542565107821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 745572084619574722300181 34948691466542565107821)
                  ·
                    rfl

theorem cell23_612561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_612561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612561 prefixEnd_612561 := by exact prefixLift 612561
  have htrace : WordTrace (prefixWord ++ tailWord_612561) baseStart_612561 baseEnd_612561 := by
    simpa [prefixWord, tailWord_612561, baseEnd_612561] using wordTrace_append hprefix tailTrace_612561
  have hstable : (prefixWord ++ tailWord_612561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612561).length < 2 ^ (prefixWord ++ tailWord_612561).sum := by decide
  have hdescent : baseEnd_612561 < baseStart_612561 := by decide
  rcases family_descends (prefixWord ++ tailWord_612561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612612 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 6]
def baseStart_612612 : Nat := 118140960795 + 612612 * 2 ^ 59
def prefixEnd_612612 : Nat := 4983230072969 + 3 ^ 40 * 612612 * 2
def baseEnd_612612 : Nat := 34951601190251376270295

theorem tailTrace_612612 : CollatzResearch.WordTrace tailWord_612612 prefixEnd_612612 34951601190251376270295 := by
  unfold tailWord_612612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11171897628309412322512045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14895863504412549763349393 11171897628309412322512045)
  ·
    refine ⟨4189461610616029620942017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11171897628309412322512045 4189461610616029620942017)
    ·
      refine ⟨3142096207962022215706513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4189461610616029620942017 3142096207962022215706513)
      ·
        refine ⟨2356572155971516661779885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142096207962022215706513 2356572155971516661779885)
        ·
          refine ⟨883714558489318748167457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2356572155971516661779885 883714558489318748167457)
          ·
            refine ⟨662785918866989061125593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883714558489318748167457 662785918866989061125593)
            ·
              refine ⟨497089439150241795844195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662785918866989061125593 497089439150241795844195)
              ·
                refine ⟨745634158725362693766293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497089439150241795844195 745634158725362693766293)
                ·
                  refine ⟨34951601190251376270295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 745634158725362693766293 34951601190251376270295)
                  ·
                    rfl

theorem cell23_612612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_612612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612612 prefixEnd_612612 := by exact prefixLift 612612
  have htrace : WordTrace (prefixWord ++ tailWord_612612) baseStart_612612 baseEnd_612612 := by
    simpa [prefixWord, tailWord_612612, baseEnd_612612] using wordTrace_append hprefix tailTrace_612612
  have hstable : (prefixWord ++ tailWord_612612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612612).length < 2 ^ (prefixWord ++ tailWord_612612).sum := by decide
  have hdescent : baseEnd_612612 < baseStart_612612 := by decide
  rcases family_descends (prefixWord ++ tailWord_612612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612625 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_612625 : Nat := 118140960795 + 612625 * 2 ^ 59
def prefixEnd_612625 : Nat := 4983230072969 + 3 ^ 40 * 612625 * 2
def baseEnd_612625 : Nat := 104857028653590278523365

theorem tailTrace_612625 : CollatzResearch.WordTrace tailWord_612625 prefixEnd_612625 104857028653590278523365 := by
  unfold tailWord_612625
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344269405571727865247329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14896179603714485243498219 22344269405571727865247329)
  ·
    refine ⟨16758202054178795898935497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22344269405571727865247329 16758202054178795898935497)
    ·
      refine ⟨12568651540634096924201623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16758202054178795898935497 12568651540634096924201623)
      ·
        refine ⟨18852977310951145386302435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12568651540634096924201623 18852977310951145386302435)
        ·
          refine ⟨28279465966426718079453653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18852977310951145386302435 28279465966426718079453653)
          ·
            refine ⟨662799983588126204987195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28279465966426718079453653 662799983588126204987195)
            ·
              refine ⟨994199975382189307480793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662799983588126204987195 994199975382189307480793)
              ·
                refine ⟨745649981536641980610595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994199975382189307480793 745649981536641980610595)
                ·
                  refine ⟨1118474972304962970915893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745649981536641980610595 1118474972304962970915893)
                  ·
                    refine ⟨104857028653590278523365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1118474972304962970915893 104857028653590278523365)
                    ·
                      rfl

theorem cell23_612625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_612625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612625 prefixEnd_612625 := by exact prefixLift 612625
  have htrace : WordTrace (prefixWord ++ tailWord_612625) baseStart_612625 baseEnd_612625 := by
    simpa [prefixWord, tailWord_612625, baseEnd_612625] using wordTrace_append hprefix tailTrace_612625
  have hstable : (prefixWord ++ tailWord_612625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612625).length < 2 ^ (prefixWord ++ tailWord_612625).sum := by decide
  have hdescent : baseEnd_612625 < baseStart_612625 := by decide
  rcases family_descends (prefixWord ++ tailWord_612625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612642 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_612642 : Nat := 118140960795 + 612642 * 2 ^ 59
def prefixEnd_612642 : Nat := 4983230072969 + 3 ^ 40 * 612642 * 2
def baseEnd_612642 : Nat := 104859938377299089685839

theorem tailTrace_612642 : CollatzResearch.WordTrace tailWord_612642 prefixEnd_612642 104859938377299089685839 := by
  unfold tailWord_612642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586222361627534942154045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14896592964340093179077453 5586222361627534942154045)
  ·
    refine ⟨2094833385610325603307767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5586222361627534942154045 2094833385610325603307767)
    ·
      refine ⟨3142250078415488404961651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094833385610325603307767 3142250078415488404961651)
      ·
        refine ⟨4713375117623232607442477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142250078415488404961651 4713375117623232607442477)
        ·
          refine ⟨1767515669108712227790929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713375117623232607442477 1767515669108712227790929)
          ·
            refine ⟨1325636751831534170843197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767515669108712227790929 1325636751831534170843197)
            ·
              refine ⟨497113781936825314066199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1325636751831534170843197 497113781936825314066199)
              ·
                refine ⟨745670672905237971099299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497113781936825314066199 745670672905237971099299)
                ·
                  refine ⟨1118506009357856956648949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745670672905237971099299 1118506009357856956648949)
                  ·
                    refine ⟨104859938377299089685839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1118506009357856956648949 104859938377299089685839)
                    ·
                      rfl

theorem cell23_612642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_612642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612642 prefixEnd_612642 := by exact prefixLift 612642
  have htrace : WordTrace (prefixWord ++ tailWord_612642) baseStart_612642 baseEnd_612642 := by
    simpa [prefixWord, tailWord_612642, baseEnd_612642] using wordTrace_append hprefix tailTrace_612642
  have hstable : (prefixWord ++ tailWord_612642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612642).length < 2 ^ (prefixWord ++ tailWord_612642).sum := by decide
  have hdescent : baseEnd_612642 < baseStart_612642 := by decide
  rcases family_descends (prefixWord ++ tailWord_612642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612665 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_612665 : Nat := 118140960795 + 612665 * 2 ^ 59
def prefixEnd_612665 : Nat := 4983230072969 + 3 ^ 40 * 612665 * 2
def baseEnd_612665 : Nat := 314591625186950679069911

theorem tailTrace_612665 : CollatzResearch.WordTrace tailWord_612665 prefixEnd_612665 314591625186950679069911 := by
  unfold tailWord_612665
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345728325426814696703449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14897152216951209797802299 22345728325426814696703449)
  ·
    refine ⟨16759296244070111022527587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22345728325426814696703449 16759296244070111022527587)
    ·
      refine ⟨25138944366105166533791381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16759296244070111022527587 25138944366105166533791381)
      ·
        refine ⟨1178388017161179681271471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25138944366105166533791381 1178388017161179681271471)
        ·
          refine ⟨1767582025741769521907207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178388017161179681271471 1767582025741769521907207)
          ·
            refine ⟨2651373038612654282860811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767582025741769521907207 2651373038612654282860811)
            ·
              refine ⟨3977059557918981424291217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651373038612654282860811 3977059557918981424291217)
              ·
                refine ⟨2982794668439236068218413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977059557918981424291217 2982794668439236068218413)
                ·
                  refine ⟨1118548000664713525581905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2982794668439236068218413 1118548000664713525581905)
                  ·
                    refine ⟨838911000498535144186429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1118548000664713525581905 838911000498535144186429)
                    ·
                      refine ⟨314591625186950679069911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838911000498535144186429 314591625186950679069911)
                      ·
                        rfl

theorem cell23_612665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_612665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612665 prefixEnd_612665 := by exact prefixLift 612665
  have htrace : WordTrace (prefixWord ++ tailWord_612665) baseStart_612665 baseEnd_612665 := by
    simpa [prefixWord, tailWord_612665, baseEnd_612665] using wordTrace_append hprefix tailTrace_612665
  have hstable : (prefixWord ++ tailWord_612665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612665).length < 2 ^ (prefixWord ++ tailWord_612665).sum := by decide
  have hdescent : baseEnd_612665 < baseStart_612665 := by decide
  rcases family_descends (prefixWord ++ tailWord_612665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612681 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_612681 : Nat := 118140960795 + 612681 * 2 ^ 59
def prefixEnd_612681 : Nat := 4983230072969 + 3 ^ 40 * 612681 * 2
def baseEnd_612681 : Nat := 104866613625807538823279

theorem tailTrace_612681 : CollatzResearch.WordTrace tailWord_612681 prefixEnd_612681 104866613625807538823279 := by
  unfold tailWord_612681
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346311893368849429285897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14897541262245899619523931 22346311893368849429285897)
  ·
    refine ⟨16759733920026637071964423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22346311893368849429285897 16759733920026637071964423)
    ·
      refine ⟨25139600880039955607946635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16759733920026637071964423 25139600880039955607946635)
      ·
        refine ⟨37709401320059933411919953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25139600880039955607946635 37709401320059933411919953)
        ·
          refine ⟨28282050990044950058939965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37709401320059933411919953 28282050990044950058939965)
          ·
            refine ⟨10605769121266856272102487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28282050990044950058939965 10605769121266856272102487)
            ·
              refine ⟨15908653681900284408153731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605769121266856272102487 15908653681900284408153731)
              ·
                refine ⟨23862980522850426612230597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15908653681900284408153731 23862980522850426612230597)
                ·
                  refine ⟨4474308848034454989793237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23862980522850426612230597 4474308848034454989793237)
                  ·
                    refine ⟨104866613625807538823279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4474308848034454989793237 104866613625807538823279)
                    ·
                      rfl

theorem cell23_612681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_612681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612681 prefixEnd_612681 := by exact prefixLift 612681
  have htrace : WordTrace (prefixWord ++ tailWord_612681) baseStart_612681 baseEnd_612681 := by
    simpa [prefixWord, tailWord_612681, baseEnd_612681] using wordTrace_append hprefix tailTrace_612681
  have hstable : (prefixWord ++ tailWord_612681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612681).length < 2 ^ (prefixWord ++ tailWord_612681).sum := by decide
  have hdescent : baseEnd_612681 < baseStart_612681 := by decide
  rcases family_descends (prefixWord ++ tailWord_612681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612695 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_612695 : Nat := 118140960795 + 612695 * 2 ^ 59
def prefixEnd_612695 : Nat := 4983230072969 + 3 ^ 40 * 612695 * 2
def baseEnd_612695 : Nat := 314607029606585561694773

theorem tailTrace_612695 : CollatzResearch.WordTrace tailWord_612695 prefixEnd_612695 314607029606585561694773 := by
  unfold tailWord_612695
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346822515318129820295539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14897881676878753213530359 22346822515318129820295539)
  ·
    refine ⟨33520233772977194730443309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22346822515318129820295539 33520233772977194730443309)
    ·
      refine ⟨12570087664866448023916241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33520233772977194730443309 12570087664866448023916241)
      ·
        refine ⟨9427565748649836017937181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12570087664866448023916241 9427565748649836017937181)
        ·
          refine ⟨3535337155743688506726443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9427565748649836017937181 3535337155743688506726443)
          ·
            refine ⟨5303005733615532760089665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535337155743688506726443 5303005733615532760089665)
            ·
              refine ⟨3977254300211649570067249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303005733615532760089665 3977254300211649570067249)
              ·
                refine ⟨2982940725158737177550437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977254300211649570067249 2982940725158737177550437)
                ·
                  refine ⟨559301385967263220790707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2982940725158737177550437 559301385967263220790707)
                  ·
                    refine ⟨838952078950894831186061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559301385967263220790707 838952078950894831186061)
                    ·
                      refine ⟨314607029606585561694773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838952078950894831186061 314607029606585561694773)
                      ·
                        rfl

theorem cell23_612695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_612695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612695 prefixEnd_612695 := by exact prefixLift 612695
  have htrace : WordTrace (prefixWord ++ tailWord_612695) baseStart_612695 baseEnd_612695 := by
    simpa [prefixWord, tailWord_612695, baseEnd_612695] using wordTrace_append hprefix tailTrace_612695
  have hstable : (prefixWord ++ tailWord_612695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612695).length < 2 ^ (prefixWord ++ tailWord_612695).sum := by decide
  have hdescent : baseEnd_612695 < baseStart_612695 := by decide
  rcases family_descends (prefixWord ++ tailWord_612695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612712 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_612712 : Nat := 118140960795 + 612712 * 2 ^ 59
def prefixEnd_612712 : Nat := 4983230072969 + 3 ^ 40 * 612712 * 2
def baseEnd_612712 : Nat := 314615758777711995182195

theorem tailTrace_612712 : CollatzResearch.WordTrace tailWord_612712 prefixEnd_612712 314615758777711995182195 := by
  unfold tailWord_612712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173721278128270861832195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14898295037504361149109593 11173721278128270861832195)
  ·
    refine ⟨16760581917192406292748293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11173721278128270861832195 16760581917192406292748293)
    ·
      refine ⟨3142609109473576179890305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16760581917192406292748293 3142609109473576179890305)
      ·
        refine ⟨2356956832105182134917729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142609109473576179890305 2356956832105182134917729)
        ·
          refine ⟨1767717624078886601188297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356956832105182134917729 1767717624078886601188297)
          ·
            refine ⟨1325788218059164950891223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767717624078886601188297 1325788218059164950891223)
            ·
              refine ⟨1988682327088747426336835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325788218059164950891223 1988682327088747426336835)
              ·
                refine ⟨2983023490633121139505253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988682327088747426336835 2983023490633121139505253)
                ·
                  refine ⟨559316904493710213657235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2983023490633121139505253 559316904493710213657235)
                  ·
                    refine ⟨838975356740565320485853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559316904493710213657235 838975356740565320485853)
                    ·
                      refine ⟨314615758777711995182195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 838975356740565320485853 314615758777711995182195)
                      ·
                        rfl

theorem cell23_612712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_612712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612712 prefixEnd_612712 := by exact prefixLift 612712
  have htrace : WordTrace (prefixWord ++ tailWord_612712) baseStart_612712 baseEnd_612712 := by
    simpa [prefixWord, tailWord_612712, baseEnd_612712] using wordTrace_append hprefix tailTrace_612712
  have hstable : (prefixWord ++ tailWord_612712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612712).length < 2 ^ (prefixWord ++ tailWord_612712).sum := by decide
  have hdescent : baseEnd_612712 < baseStart_612712 := by decide
  rcases family_descends (prefixWord ++ tailWord_612712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612726 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_612726 : Nat := 118140960795 + 612726 * 2 ^ 59
def prefixEnd_612726 : Nat := 4983230072969 + 3 ^ 40 * 612726 * 2
def baseEnd_612726 : Nat := 314622947506874940407131

theorem tailTrace_612726 : CollatzResearch.WordTrace tailWord_612726 prefixEnd_612726 314622947506874940407131 := by
  unfold tailWord_612726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396747073637863882167127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14898635452137214743116021 1396747073637863882167127)
  ·
    refine ⟨2095120610456795823250691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396747073637863882167127 2095120610456795823250691)
    ·
      refine ⟨3142680915685193734876037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095120610456795823250691 3142680915685193734876037)
      ·
        refine ⟨589252671690973825289257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3142680915685193734876037 589252671690973825289257)
        ·
          refine ⟨441939503768230368966943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589252671690973825289257 441939503768230368966943)
          ·
            refine ⟨662909255652345553450415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441939503768230368966943 662909255652345553450415)
            ·
              refine ⟨994363883478518330175623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662909255652345553450415 994363883478518330175623)
              ·
                refine ⟨1491545825217777495263435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994363883478518330175623 1491545825217777495263435)
                ·
                  refine ⟨2237318737826666242895153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491545825217777495263435 2237318737826666242895153)
                  ·
                    refine ⟨1677989053369999682171365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237318737826666242895153 1677989053369999682171365)
                    ·
                      refine ⟨314622947506874940407131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1677989053369999682171365 314622947506874940407131)
                      ·
                        rfl

theorem cell23_612726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_612726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612726 prefixEnd_612726 := by exact prefixLift 612726
  have htrace : WordTrace (prefixWord ++ tailWord_612726) baseStart_612726 baseEnd_612726 := by
    simpa [prefixWord, tailWord_612726, baseEnd_612726] using wordTrace_append hprefix tailTrace_612726
  have hstable : (prefixWord ++ tailWord_612726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612726).length < 2 ^ (prefixWord ++ tailWord_612726).sum := by decide
  have hdescent : baseEnd_612726 < baseStart_612726 := by decide
  rcases family_descends (prefixWord ++ tailWord_612726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612739 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 1, 3, 2]
def baseStart_612739 : Nat := 118140960795 + 612739 * 2 ^ 59
def prefixEnd_612739 : Nat := 4983230072969 + 3 ^ 40 * 612739 * 2
def baseEnd_612739 : Nat := 314629622755383389544571

theorem tailTrace_612739 : CollatzResearch.WordTrace tailWord_612739 prefixEnd_612739 314629622755383389544571 := by
  unfold tailWord_612739
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348427327158725334897271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14898951551439150223264847 22348427327158725334897271)
  ·
    refine ⟨33522640990738088002345907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22348427327158725334897271 33522640990738088002345907)
    ·
      refine ⟨50283961486107132003518861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33522640990738088002345907 50283961486107132003518861)
      ·
        refine ⟨18856485557290174501319573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50283961486107132003518861 18856485557290174501319573)
        ·
          refine ⟨883897760497976929749355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18856485557290174501319573 883897760497976929749355)
          ·
            refine ⟨1325846640746965394624033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883897760497976929749355 1325846640746965394624033)
            ·
              refine ⟨994384980560224045968025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325846640746965394624033 994384980560224045968025)
              ·
                refine ⟨745788735420168034476019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994384980560224045968025 745788735420168034476019)
                ·
                  refine ⟨1118683103130252051714029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745788735420168034476019 1118683103130252051714029)
                  ·
                    refine ⟨419506163673844519392761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118683103130252051714029 419506163673844519392761)
                    ·
                      refine ⟨314629622755383389544571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419506163673844519392761 314629622755383389544571)
                      ·
                        rfl

theorem cell23_612739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_612739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612739 prefixEnd_612739 := by exact prefixLift 612739
  have htrace : WordTrace (prefixWord ++ tailWord_612739) baseStart_612739 baseEnd_612739 := by
    simpa [prefixWord, tailWord_612739, baseEnd_612739] using wordTrace_append hprefix tailTrace_612739
  have hstable : (prefixWord ++ tailWord_612739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612739).length < 2 ^ (prefixWord ++ tailWord_612739).sum := by decide
  have hdescent : baseEnd_612739 < baseStart_612739 := by decide
  rcases family_descends (prefixWord ++ tailWord_612739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612775 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 7]
def baseStart_612775 : Nat := 118140960795 + 612775 * 2 ^ 59
def prefixEnd_612775 : Nat := 4983230072969 + 3 ^ 40 * 612775 * 2
def baseEnd_612775 : Nat := 34960900895438360966045

theorem tailTrace_612775 : CollatzResearch.WordTrace tailWord_612775 prefixEnd_612775 34960900895438360966045 := by
  unfold tailWord_612775
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349740355028303483207779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14899826903352202322138519 22349740355028303483207779)
  ·
    refine ⟨33524610532542455224811669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22349740355028303483207779 33524610532542455224811669)
    ·
      refine ⟨1571466118712927588663047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33524610532542455224811669 1571466118712927588663047)
      ·
        refine ⟨2357199178069391382994571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571466118712927588663047 2357199178069391382994571)
        ·
          refine ⟨3535798767104087074491857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357199178069391382994571 3535798767104087074491857)
          ·
            refine ⟨2651849075328065305868893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3535798767104087074491857 2651849075328065305868893)
            ·
              refine ⟨994443403248024489700835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2651849075328065305868893 994443403248024489700835)
              ·
                refine ⟨1491665104872036734551253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994443403248024489700835 1491665104872036734551253)
                ·
                  refine ⟨34960900895438360966045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1491665104872036734551253 34960900895438360966045)
                  ·
                    rfl

theorem cell23_612775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 7].length) (baseStart_612775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612775 prefixEnd_612775 := by exact prefixLift 612775
  have htrace : WordTrace (prefixWord ++ tailWord_612775) baseStart_612775 baseEnd_612775 := by
    simpa [prefixWord, tailWord_612775, baseEnd_612775] using wordTrace_append hprefix tailTrace_612775
  have hstable : (prefixWord ++ tailWord_612775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612775).length < 2 ^ (prefixWord ++ tailWord_612775).sum := by decide
  have hdescent : baseEnd_612775 < baseStart_612775 := by decide
  rcases family_descends (prefixWord ++ tailWord_612775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612822 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_612822 : Nat := 118140960795 + 612822 * 2 ^ 59
def prefixEnd_612822 : Nat := 4983230072969 + 3 ^ 40 * 612822 * 2
def baseEnd_612822 : Nat := 104890747216568854935563

theorem tailTrace_612822 : CollatzResearch.WordTrace tailWord_612822 prefixEnd_612822 104890747216568854935563 := by
  unfold tailWord_612822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396965911616126906885545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14900969723905353673445813 1396965911616126906885545)
  ·
    refine ⟨1047724433712095180164159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396965911616126906885545 1047724433712095180164159)
    ·
      refine ⟨1571586650568142770246239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047724433712095180164159 1571586650568142770246239)
      ·
        refine ⟨2357379975852214155369359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571586650568142770246239 2357379975852214155369359)
        ·
          refine ⟨3536069963778321233054039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357379975852214155369359 3536069963778321233054039)
          ·
            refine ⟨5304104945667481849581059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536069963778321233054039 5304104945667481849581059)
            ·
              refine ⟨7956157418501222774371589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304104945667481849581059 7956157418501222774371589)
              ·
                refine ⟨1491779515968979270194673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7956157418501222774371589 1491779515968979270194673)
                ·
                  refine ⟨1118834636976734452646005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491779515968979270194673 1118834636976734452646005)
                  ·
                    refine ⟨104890747216568854935563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1118834636976734452646005 104890747216568854935563)
                    ·
                      rfl

theorem cell23_612822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_612822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612822 prefixEnd_612822 := by exact prefixLift 612822
  have htrace : WordTrace (prefixWord ++ tailWord_612822) baseStart_612822 baseEnd_612822 := by
    simpa [prefixWord, tailWord_612822, baseEnd_612822] using wordTrace_append hprefix tailTrace_612822
  have hstable : (prefixWord ++ tailWord_612822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612822).length < 2 ^ (prefixWord ++ tailWord_612822).sum := by decide
  have hdescent : baseEnd_612822 < baseStart_612822 := by decide
  rcases family_descends (prefixWord ++ tailWord_612822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612825 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_612825 : Nat := 118140960795 + 612825 * 2 ^ 59
def prefixEnd_612825 : Nat := 4983230072969 + 3 ^ 40 * 612825 * 2
def baseEnd_612825 : Nat := 314673782091670053069175

theorem tailTrace_612825 : CollatzResearch.WordTrace tailWord_612825 prefixEnd_612825 314673782091670053069175 := by
  unfold tailWord_612825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22351564004847162022527929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14901042669898108015018619 22351564004847162022527929)
  ·
    refine ⟨16763673003635371516895947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22351564004847162022527929 16763673003635371516895947)
    ·
      refine ⟨25145509505453057275343921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16763673003635371516895947 25145509505453057275343921)
      ·
        refine ⟨18859132129089792956507941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25145509505453057275343921 18859132129089792956507941)
        ·
          refine ⟨3536087274204336179345239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18859132129089792956507941 3536087274204336179345239)
          ·
            refine ⟨5304130911306504269017859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536087274204336179345239 5304130911306504269017859)
            ·
              refine ⟨7956196366959756403526789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304130911306504269017859 7956196366959756403526789)
              ·
                refine ⟨1491786818804954325661273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7956196366959756403526789 1491786818804954325661273)
                ·
                  refine ⟨1118840114103715744245955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491786818804954325661273 1118840114103715744245955)
                  ·
                    refine ⟨1678260171155573616368933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1118840114103715744245955 1678260171155573616368933)
                    ·
                      refine ⟨314673782091670053069175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1678260171155573616368933 314673782091670053069175)
                      ·
                        rfl

theorem cell23_612825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_612825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612825 prefixEnd_612825 := by exact prefixLift 612825
  have htrace : WordTrace (prefixWord ++ tailWord_612825) baseStart_612825 baseEnd_612825 := by
    simpa [prefixWord, tailWord_612825, baseEnd_612825] using wordTrace_append hprefix tailTrace_612825
  have hstable : (prefixWord ++ tailWord_612825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612825).length < 2 ^ (prefixWord ++ tailWord_612825).sum := by decide
  have hdescent : baseEnd_612825 < baseStart_612825 := by decide
  rcases family_descends (prefixWord ++ tailWord_612825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612842 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_612842 : Nat := 118140960795 + 612842 * 2 ^ 59
def prefixEnd_612842 : Nat := 4983230072969 + 3 ^ 40 * 612842 * 2
def baseEnd_612842 : Nat := 314682511262796486556597

theorem tailTrace_612842 : CollatzResearch.WordTrace tailWord_612842 prefixEnd_612842 314682511262796486556597 := by
  unfold tailWord_612842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588046011446393481474195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14901456030523715950597853 5588046011446393481474195)
  ·
    refine ⟨8382069017169590222211293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5588046011446393481474195 8382069017169590222211293)
    ·
      refine ⟨3143275881438596333329235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8382069017169590222211293 3143275881438596333329235)
      ·
        refine ⟨4714913822157894499993853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143275881438596333329235 4714913822157894499993853)
        ·
          refine ⟨1768092683309210437497695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4714913822157894499993853 1768092683309210437497695)
          ·
            refine ⟨2652139024963815656246543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768092683309210437497695 2652139024963815656246543)
            ·
              refine ⟨3978208537445723484369815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652139024963815656246543 3978208537445723484369815)
              ·
                refine ⟨5967312806168585226554723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978208537445723484369815 5967312806168585226554723)
                ·
                  refine ⟨8950969209252877839832085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5967312806168585226554723 8950969209252877839832085)
                  ·
                    refine ⟨419576681683728648742129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8950969209252877839832085 419576681683728648742129)
                    ·
                      refine ⟨314682511262796486556597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419576681683728648742129 314682511262796486556597)
                      ·
                        rfl

theorem cell23_612842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_612842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612842 prefixEnd_612842 := by exact prefixLift 612842
  have htrace : WordTrace (prefixWord ++ tailWord_612842) baseStart_612842 baseEnd_612842 := by
    simpa [prefixWord, tailWord_612842, baseEnd_612842] using wordTrace_append hprefix tailTrace_612842
  have hstable : (prefixWord ++ tailWord_612842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612842).length < 2 ^ (prefixWord ++ tailWord_612842).sum := by decide
  have hdescent : baseEnd_612842 < baseStart_612842 := by decide
  rcases family_descends (prefixWord ++ tailWord_612842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612942 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_612942 : Nat := 118140960795 + 612942 * 2 ^ 59
def prefixEnd_612942 : Nat := 4983230072969 + 3 ^ 40 * 612942 * 2
def baseEnd_612942 : Nat := 104911286442748698435379

theorem tailTrace_612942 : CollatzResearch.WordTrace tailWord_612942 prefixEnd_612942 104911286442748698435379 := by
  unfold tailWord_612942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794478918177911375567135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14903887563615527336358053 2794478918177911375567135)
  ·
    refine ⟨4191718377266867063350703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794478918177911375567135 4191718377266867063350703)
    ·
      refine ⟨6287577565900300595026055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191718377266867063350703 6287577565900300595026055)
      ·
        refine ⟨9431366348850450892539083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287577565900300595026055 9431366348850450892539083)
        ·
          refine ⟨14147049523275676338808625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431366348850450892539083 14147049523275676338808625)
          ·
            refine ⟨10610287142456757254106469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14147049523275676338808625 10610287142456757254106469)
            ·
              refine ⟨1989428839210641985144963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10610287142456757254106469 1989428839210641985144963)
              ·
                refine ⟨2984143258815962977717445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989428839210641985144963 2984143258815962977717445)
                ·
                  refine ⟨559526861027993058322021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2984143258815962977717445 559526861027993058322021)
                  ·
                    refine ⟨104911286442748698435379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559526861027993058322021 104911286442748698435379)
                    ·
                      rfl

theorem cell23_612942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_612942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612942 prefixEnd_612942 := by exact prefixLift 612942
  have htrace : WordTrace (prefixWord ++ tailWord_612942) baseStart_612942 baseEnd_612942 := by
    simpa [prefixWord, tailWord_612942, baseEnd_612942] using wordTrace_append hprefix tailTrace_612942
  have hstable : (prefixWord ++ tailWord_612942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612942).length < 2 ^ (prefixWord ++ tailWord_612942).sum := by decide
  have hdescent : baseEnd_612942 < baseStart_612942 := by decide
  rcases family_descends (prefixWord ++ tailWord_612942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612945 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_612945 : Nat := 118140960795 + 612945 * 2 ^ 59
def prefixEnd_612945 : Nat := 4983230072969 + 3 ^ 40 * 612945 * 2
def baseEnd_612945 : Nat := 314735399770209583568623

theorem tailTrace_612945 : CollatzResearch.WordTrace tailWord_612945 prefixEnd_612945 314735399770209583568623 := by
  unfold tailWord_612945
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355940764412422516896289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903960509608281677930859 22355940764412422516896289)
  ·
    refine ⟨16766955573309316887672217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22355940764412422516896289 16766955573309316887672217)
    ·
      refine ⟨12575216679981987665754163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16766955573309316887672217 12575216679981987665754163)
      ·
        refine ⟨18862825019972981498631245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12575216679981987665754163 18862825019972981498631245)
        ·
          refine ⟨7073559382489868061986717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18862825019972981498631245 7073559382489868061986717)
          ·
            refine ⟨2652584768433700523245019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7073559382489868061986717 2652584768433700523245019)
            ·
              refine ⟨3978877152650550784867529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652584768433700523245019 3978877152650550784867529)
              ·
                refine ⟨2984157864487913088650647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978877152650550784867529 2984157864487913088650647)
                ·
                  refine ⟨4476236796731869632975971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984157864487913088650647 4476236796731869632975971)
                  ·
                    refine ⟨6714355195097804449463957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476236796731869632975971 6714355195097804449463957)
                    ·
                      refine ⟨314735399770209583568623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6714355195097804449463957 314735399770209583568623)
                      ·
                        rfl

theorem cell23_612945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_612945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612945 prefixEnd_612945 := by exact prefixLift 612945
  have htrace : WordTrace (prefixWord ++ tailWord_612945) baseStart_612945 baseEnd_612945 := by
    simpa [prefixWord, tailWord_612945, baseEnd_612945] using wordTrace_append hprefix tailTrace_612945
  have hstable : (prefixWord ++ tailWord_612945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612945).length < 2 ^ (prefixWord ++ tailWord_612945).sum := by decide
  have hdescent : baseEnd_612945 < baseStart_612945 := by decide
  rcases family_descends (prefixWord ++ tailWord_612945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612995 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_612995 : Nat := 118140960795 + 612995 * 2 ^ 59
def prefixEnd_612995 : Nat := 4983230072969 + 3 ^ 40 * 612995 * 2
def baseEnd_612995 : Nat := 314761073802934387943393

theorem tailTrace_612995 : CollatzResearch.WordTrace tailWord_612995 prefixEnd_612995 314761073802934387943393 := by
  unfold tailWord_612995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22357764414231281056216439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14905176276154187370810959 22357764414231281056216439)
  ·
    refine ⟨33536646621346921584324659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22357764414231281056216439 33536646621346921584324659)
    ·
      refine ⟨50304969932020382376486989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33536646621346921584324659 50304969932020382376486989)
      ·
        refine ⟨18864363724507643391182621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50304969932020382376486989 18864363724507643391182621)
        ·
          refine ⟨7074136396690366271693483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18864363724507643391182621 7074136396690366271693483)
          ·
            refine ⟨10611204595035549407540225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074136396690366271693483 10611204595035549407540225)
            ·
              refine ⟨7958403446276662055655169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10611204595035549407540225 7958403446276662055655169)
              ·
                refine ⟨5968802584707496541741377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958403446276662055655169 5968802584707496541741377)
                ·
                  refine ⟨4476601938530622406306033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5968802584707496541741377 4476601938530622406306033)
                  ·
                    refine ⟨3357451453897966804729525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4476601938530622406306033 3357451453897966804729525)
                    ·
                      refine ⟨314761073802934387943393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3357451453897966804729525 314761073802934387943393)
                      ·
                        rfl

theorem cell23_612995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_612995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_612995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_612995 prefixEnd_612995 := by exact prefixLift 612995
  have htrace : WordTrace (prefixWord ++ tailWord_612995) baseStart_612995 baseEnd_612995 := by
    simpa [prefixWord, tailWord_612995, baseEnd_612995] using wordTrace_append hprefix tailTrace_612995
  have hstable : (prefixWord ++ tailWord_612995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612995).length < 2 ^ (prefixWord ++ tailWord_612995).sum := by decide
  have hdescent : baseEnd_612995 < baseStart_612995 := by decide
  rcases family_descends (prefixWord ++ tailWord_612995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613039 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 4, 2]
def baseStart_613039 : Nat := 118140960795 + 613039 * 2 ^ 59
def prefixEnd_613039 : Nat := 4983230072969 + 3 ^ 40 * 613039 * 2
def baseEnd_613039 : Nat := 314783666951732215793191

theorem tailTrace_613039 : CollatzResearch.WordTrace tailWord_613039 prefixEnd_613039 314783666951732215793191 := by
  unfold tailWord_613039
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359369226071876570818171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14906246150714584380545447 22359369226071876570818171)
  ·
    refine ⟨33539053839107814856227257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359369226071876570818171 33539053839107814856227257)
    ·
      refine ⟨25154290379330861142170443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33539053839107814856227257 25154290379330861142170443)
      ·
        refine ⟨37731435568996291713255665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25154290379330861142170443 37731435568996291713255665)
        ·
          refine ⟨28298576676747218784941749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37731435568996291713255665 28298576676747218784941749)
          ·
            refine ⟨2652991563445051761088289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28298576676747218784941749 2652991563445051761088289)
            ·
              refine ⟨1989743672583788820816217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652991563445051761088289 1989743672583788820816217)
              ·
                refine ⟨1492307754437841615612163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989743672583788820816217 1492307754437841615612163)
                ·
                  refine ⟨2238461631656762423418245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492307754437841615612163 2238461631656762423418245)
                  ·
                    refine ⟨419711555935642954390921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238461631656762423418245 419711555935642954390921)
                    ·
                      refine ⟨314783666951732215793191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419711555935642954390921 314783666951732215793191)
                      ·
                        rfl

theorem cell23_613039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4, 2].length) (baseStart_613039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613039 prefixEnd_613039 := by exact prefixLift 613039
  have htrace : WordTrace (prefixWord ++ tailWord_613039) baseStart_613039 baseEnd_613039 := by
    simpa [prefixWord, tailWord_613039, baseEnd_613039] using wordTrace_append hprefix tailTrace_613039
  have hstable : (prefixWord ++ tailWord_613039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613039).length < 2 ^ (prefixWord ++ tailWord_613039).sum := by decide
  have hdescent : baseEnd_613039 < baseStart_613039 := by decide
  rcases family_descends (prefixWord ++ tailWord_613039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613043 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 1, 3, 2]
def baseStart_613043 : Nat := 118140960795 + 613043 * 2 ^ 59
def prefixEnd_613043 : Nat := 4983230072969 + 3 ^ 40 * 613043 * 2
def baseEnd_613043 : Nat := 314785720874350200143173

theorem tailTrace_613043 : CollatzResearch.WordTrace tailWord_613043 prefixEnd_613043 314785720874350200143173 := by
  unfold tailWord_613043
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359515118057385253963783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14906343412038256835975855 22359515118057385253963783)
  ·
    refine ⟨33539272677086077880945675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359515118057385253963783 33539272677086077880945675)
    ·
      refine ⟨50308909015629116821418513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33539272677086077880945675 50308909015629116821418513)
      ·
        refine ⟨37731681761721837616063885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50308909015629116821418513 37731681761721837616063885)
        ·
          refine ⟨14149380660645689106023957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37731681761721837616063885 14149380660645689106023957)
          ·
            refine ⟨663252218467766676844873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14149380660645689106023957 663252218467766676844873)
            ·
              refine ⟨497439163850825007633655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663252218467766676844873 497439163850825007633655)
              ·
                refine ⟨746158745776237511450483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497439163850825007633655 746158745776237511450483)
                ·
                  refine ⟨1119238118664356267175725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746158745776237511450483 1119238118664356267175725)
                  ·
                    refine ⟨419714294499133600190897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119238118664356267175725 419714294499133600190897)
                    ·
                      refine ⟨314785720874350200143173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419714294499133600190897 314785720874350200143173)
                      ·
                        rfl

theorem cell23_613043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 3, 2].length) (baseStart_613043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613043 prefixEnd_613043 := by exact prefixLift 613043
  have htrace : WordTrace (prefixWord ++ tailWord_613043) baseStart_613043 baseEnd_613043 := by
    simpa [prefixWord, tailWord_613043, baseEnd_613043] using wordTrace_append hprefix tailTrace_613043
  have hstable : (prefixWord ++ tailWord_613043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613043).length < 2 ^ (prefixWord ++ tailWord_613043).sum := by decide
  have hdescent : baseEnd_613043 < baseStart_613043 := by decide
  rcases family_descends (prefixWord ++ tailWord_613043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613052 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_613052 : Nat := 118140960795 + 613052 * 2 ^ 59
def prefixEnd_613052 : Nat := 4983230072969 + 3 ^ 40 * 613052 * 2
def baseEnd_613052 : Nat := 314790342200240664930631

theorem tailTrace_613052 : CollatzResearch.WordTrace tailWord_613052 prefixEnd_613052 314790342200240664930631 := by
  unfold tailWord_613052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179921687512389895520705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14906562250016519860694273 11179921687512389895520705)
  ·
    refine ⟨8384941265634292421640529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11179921687512389895520705 8384941265634292421640529)
    ·
      refine ⟨6288705949225719316230397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8384941265634292421640529 6288705949225719316230397)
      ·
        refine ⟨2358264730959644743586399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6288705949225719316230397 2358264730959644743586399)
        ·
          refine ⟨3537397096439467115379599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358264730959644743586399 3537397096439467115379599)
          ·
            refine ⟨5306095644659200673069399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537397096439467115379599 5306095644659200673069399)
            ·
              refine ⟨7959143466988801009604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306095644659200673069399 7959143466988801009604099)
              ·
                refine ⟨11938715200483201514406149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7959143466988801009604099 11938715200483201514406149)
                ·
                  refine ⟨2238509100090600283951153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11938715200483201514406149 2238509100090600283951153)
                  ·
                    refine ⟨1678881825067950212963365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2238509100090600283951153 1678881825067950212963365)
                    ·
                      refine ⟨314790342200240664930631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1678881825067950212963365 314790342200240664930631)
                      ·
                        rfl

theorem cell23_613052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_613052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613052 prefixEnd_613052 := by exact prefixLift 613052
  have htrace : WordTrace (prefixWord ++ tailWord_613052) baseStart_613052 baseEnd_613052 := by
    simpa [prefixWord, tailWord_613052, baseEnd_613052] using wordTrace_append hprefix tailTrace_613052
  have hstable : (prefixWord ++ tailWord_613052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613052).length < 2 ^ (prefixWord ++ tailWord_613052).sum := by decide
  have hdescent : baseEnd_613052 < baseStart_613052 := by decide
  rcases family_descends (prefixWord ++ tailWord_613052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613056 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2]
def baseStart_613056 : Nat := 118140960795 + 613056 * 2 ^ 59
def prefixEnd_613056 : Nat := 4983230072969 + 3 ^ 40 * 613056 * 2
def baseEnd_613056 : Nat := 314792396122858649280613

theorem tailTrace_613056 : CollatzResearch.WordTrace tailWord_613056 prefixEnd_613056 314792396122858649280613 := by
  unfold tailWord_613056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179994633505144237093511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14906659511340192316124681 11179994633505144237093511)
  ·
    refine ⟨16769991950257716355640267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11179994633505144237093511 16769991950257716355640267)
    ·
      refine ⟨25154987925386574533460401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16769991950257716355640267 25154987925386574533460401)
      ·
        refine ⟨18866240944039930900095301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25154987925386574533460401 18866240944039930900095301)
        ·
          refine ⟨3537420177007487043767869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18866240944039930900095301 3537420177007487043767869)
          ·
            refine ⟨1326532566377807641412951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3537420177007487043767869 1326532566377807641412951)
            ·
              refine ⟨1989798849566711462119427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326532566377807641412951 1989798849566711462119427)
              ·
                refine ⟨2984698274350067193179141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989798849566711462119427 2984698274350067193179141)
                ·
                  refine ⟨559630926440637598721089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2984698274350067193179141 559630926440637598721089)
                  ·
                    refine ⟨419723194830478199040817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559630926440637598721089 419723194830478199040817)
                    ·
                      refine ⟨314792396122858649280613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419723194830478199040817 314792396122858649280613)
                      ·
                        rfl

theorem cell23_613056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_613056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613056 prefixEnd_613056 := by exact prefixLift 613056
  have htrace : WordTrace (prefixWord ++ tailWord_613056) baseStart_613056 baseEnd_613056 := by
    simpa [prefixWord, tailWord_613056, baseEnd_613056] using wordTrace_append hprefix tailTrace_613056
  have hstable : (prefixWord ++ tailWord_613056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613056).length < 2 ^ (prefixWord ++ tailWord_613056).sum := by decide
  have hdescent : baseEnd_613056 < baseStart_613056 := by decide
  rcases family_descends (prefixWord ++ tailWord_613056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613073 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_613073 : Nat := 118140960795 + 613073 * 2 ^ 59
def prefixEnd_613073 : Nat := 4983230072969 + 3 ^ 40 * 613073 * 2
def baseEnd_613073 : Nat := 314801125293985082768035

theorem tailTrace_613073 : CollatzResearch.WordTrace tailWord_613073 prefixEnd_613073 314801125293985082768035 := by
  unfold tailWord_613073
  simp only [CollatzResearch.WordTrace]
  refine ⟨22360609307948700377555873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14907072871965800251703915 22360609307948700377555873)
  ·
    refine ⟨16770456980961525283166905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22360609307948700377555873 16770456980961525283166905)
    ·
      refine ⟨12577842735721143962375179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16770456980961525283166905 12577842735721143962375179)
      ·
        refine ⟨18866764103581715943562769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12577842735721143962375179 18866764103581715943562769)
        ·
          refine ⟨14150073077686286957672077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18866764103581715943562769 14150073077686286957672077)
          ·
            refine ⟨5306277404132357609127029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14150073077686286957672077 5306277404132357609127029)
            ·
              refine ⟨497463506637408525855659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5306277404132357609127029 497463506637408525855659)
              ·
                refine ⟨746195259956112788783489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497463506637408525855659 746195259956112788783489)
                ·
                  refine ⟨559646444967084591587617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746195259956112788783489 559646444967084591587617)
                  ·
                    refine ⟨419734833725313443690713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559646444967084591587617 419734833725313443690713)
                    ·
                      refine ⟨314801125293985082768035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419734833725313443690713 314801125293985082768035)
                      ·
                        rfl

theorem cell23_613073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_613073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613073 prefixEnd_613073 := by exact prefixLift 613073
  have htrace : WordTrace (prefixWord ++ tailWord_613073) baseStart_613073 baseEnd_613073 := by
    simpa [prefixWord, tailWord_613073, baseEnd_613073] using wordTrace_append hprefix tailTrace_613073
  have hstable : (prefixWord ++ tailWord_613073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613073).length < 2 ^ (prefixWord ++ tailWord_613073).sum := by decide
  have hdescent : baseEnd_613073 < baseStart_613073 := by decide
  rcases family_descends (prefixWord ++ tailWord_613073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613092 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_613092 : Nat := 118140960795 + 613092 * 2 ^ 59
def prefixEnd_613092 : Nat := 4983230072969 + 3 ^ 40 * 613092 * 2
def baseEnd_613092 : Nat := 104936960475473502810149

theorem tailTrace_613092 : CollatzResearch.WordTrace tailWord_613092 prefixEnd_613092 104936960475473502810149 := by
  unfold tailWord_613092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180651147439933311248765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14907534863253244414998353 11180651147439933311248765)
  ·
    refine ⟨4192744180289974991718287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11180651147439933311248765 4192744180289974991718287)
    ·
      refine ⟨6289116270434962487577431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192744180289974991718287 6289116270434962487577431)
      ·
        refine ⟨9433674405652443731366147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289116270434962487577431 9433674405652443731366147)
        ·
          refine ⟨14150511608478665597049221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9433674405652443731366147 14150511608478665597049221)
          ·
            refine ⟨2653220926589749799446729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14150511608478665597049221 2653220926589749799446729)
            ·
              refine ⟨1989915694942312349585047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653220926589749799446729 1989915694942312349585047)
              ·
                refine ⟨2984873542413468524377571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989915694942312349585047 2984873542413468524377571)
                ·
                  refine ⟨4477310313620202786566357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984873542413468524377571 4477310313620202786566357)
                  ·
                    refine ⟨104936960475473502810149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4477310313620202786566357 104936960475473502810149)
                    ·
                      rfl

theorem cell23_613092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_613092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613092 prefixEnd_613092 := by exact prefixLift 613092
  have htrace : WordTrace (prefixWord ++ tailWord_613092) baseStart_613092 baseEnd_613092 := by
    simpa [prefixWord, tailWord_613092, baseEnd_613092] using wordTrace_append hprefix tailTrace_613092
  have hstable : (prefixWord ++ tailWord_613092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613092).length < 2 ^ (prefixWord ++ tailWord_613092).sum := by decide
  have hdescent : baseEnd_613092 < baseStart_613092 := by decide
  rcases family_descends (prefixWord ++ tailWord_613092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613129 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 4, 2]
def baseStart_613129 : Nat := 118140960795 + 613129 * 2 ^ 59
def prefixEnd_613129 : Nat := 4983230072969 + 3 ^ 40 * 613129 * 2
def baseEnd_613129 : Nat := 314829880210636863667777

theorem tailTrace_613129 : CollatzResearch.WordTrace tailWord_613129 prefixEnd_613129 314829880210636863667777 := by
  unfold tailWord_613129
  simp only [CollatzResearch.WordTrace]
  refine ⟨22362651795745821941594441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14908434530497214627729627 22362651795745821941594441)
  ·
    refine ⟨16771988846809366456195831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22362651795745821941594441 16771988846809366456195831)
    ·
      refine ⟨25157983270214049684293747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16771988846809366456195831 25157983270214049684293747)
      ·
        refine ⟨37736974905321074526440621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25157983270214049684293747 37736974905321074526440621)
        ·
          refine ⟨14151365589495402947415233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37736974905321074526440621 14151365589495402947415233)
          ·
            refine ⟨10613524192121552210561425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14151365589495402947415233 10613524192121552210561425)
            ·
              refine ⟨7960143144091164157921069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10613524192121552210561425 7960143144091164157921069)
              ·
                refine ⟨2985053679034186559220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7960143144091164157921069 2985053679034186559220401)
                ·
                  refine ⟨2238790259275639919415301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985053679034186559220401 2238790259275639919415301)
                  ·
                    refine ⟨419773173614182484890369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238790259275639919415301 419773173614182484890369)
                    ·
                      refine ⟨314829880210636863667777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419773173614182484890369 314829880210636863667777)
                      ·
                        rfl

theorem cell23_613129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4, 2].length) (baseStart_613129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613129 prefixEnd_613129 := by exact prefixLift 613129
  have htrace : WordTrace (prefixWord ++ tailWord_613129) baseStart_613129 baseEnd_613129 := by
    simpa [prefixWord, tailWord_613129, baseEnd_613129] using wordTrace_append hprefix tailTrace_613129
  have hstable : (prefixWord ++ tailWord_613129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613129).length < 2 ^ (prefixWord ++ tailWord_613129).sum := by decide
  have hdescent : baseEnd_613129 < baseStart_613129 := by decide
  rcases family_descends (prefixWord ++ tailWord_613129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613169 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 6]
def baseStart_613169 : Nat := 118140960795 + 613169 * 2 ^ 59
def prefixEnd_613169 : Nat := 4983230072969 + 3 ^ 40 * 613169 * 2
def baseEnd_613169 : Nat := 34983379937424078574177

theorem tailTrace_613169 : CollatzResearch.WordTrace tailWord_613169 prefixEnd_613169 34983379937424078574177 := by
  unfold tailWord_613169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22364110715600908773050561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14909407143733939182033707 22364110715600908773050561)
  ·
    refine ⟨16773083036700681579787921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22364110715600908773050561 16773083036700681579787921)
    ·
      refine ⟨12579812277525511184840941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16773083036700681579787921 12579812277525511184840941)
      ·
        refine ⟨4717429604072066694315353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12579812277525511184840941 4717429604072066694315353)
        ·
          refine ⟨3538072203054050020736515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4717429604072066694315353 3538072203054050020736515)
          ·
            refine ⟨5307108304581075031104773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538072203054050020736515 5307108304581075031104773)
            ·
              refine ⟨995082807108951568332145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5307108304581075031104773 995082807108951568332145)
              ·
                refine ⟨746312105331713676249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995082807108951568332145 746312105331713676249109)
                ·
                  refine ⟨34983379937424078574177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 746312105331713676249109 34983379937424078574177)
                  ·
                    rfl

theorem cell23_613169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_613169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613169 prefixEnd_613169 := by exact prefixLift 613169
  have htrace : WordTrace (prefixWord ++ tailWord_613169) baseStart_613169 baseEnd_613169 := by
    simpa [prefixWord, tailWord_613169, baseEnd_613169] using wordTrace_append hprefix tailTrace_613169
  have hstable : (prefixWord ++ tailWord_613169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613169).length < 2 ^ (prefixWord ++ tailWord_613169).sum := by decide
  have hdescent : baseEnd_613169 < baseStart_613169 := by decide
  rcases family_descends (prefixWord ++ tailWord_613169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613173 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_613173 : Nat := 118140960795 + 613173 * 2 ^ 59
def prefixEnd_613173 : Nat := 4983230072969 + 3 ^ 40 * 613173 * 2
def baseEnd_613173 : Nat := 104950824453144897172525

theorem tailTrace_613173 : CollatzResearch.WordTrace tailWord_613173 prefixEnd_613173 104950824453144897172525 := by
  unfold tailWord_613173
  simp only [CollatzResearch.WordTrace]
  refine ⟨22364256607586417456196173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14909504405057611637464115 22364256607586417456196173)
  ·
    refine ⟨8386596227844906546073565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22364256607586417456196173 8386596227844906546073565)
    ·
      refine ⟨3144973585441839954777587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8386596227844906546073565 3144973585441839954777587)
      ·
        refine ⟨4717460378162759932166381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144973585441839954777587 4717460378162759932166381)
        ·
          refine ⟨1769047641811034974562393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4717460378162759932166381 1769047641811034974562393)
          ·
            refine ⟨1326785731358276230921795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769047641811034974562393 1326785731358276230921795)
            ·
              refine ⟨1990178597037414346382693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326785731358276230921795 1990178597037414346382693)
              ·
                refine ⟨373158486944515189946755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1990178597037414346382693 373158486944515189946755)
                ·
                  refine ⟨559737730416772784920133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373158486944515189946755 559737730416772784920133)
                  ·
                    refine ⟨104950824453144897172525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559737730416772784920133 104950824453144897172525)
                    ·
                      rfl

theorem cell23_613173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_613173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613173 prefixEnd_613173 := by exact prefixLift 613173
  have htrace : WordTrace (prefixWord ++ tailWord_613173) baseStart_613173 baseEnd_613173 := by
    simpa [prefixWord, tailWord_613173, baseEnd_613173] using wordTrace_append hprefix tailTrace_613173
  have hstable : (prefixWord ++ tailWord_613173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613173).length < 2 ^ (prefixWord ++ tailWord_613173).sum := by decide
  have hdescent : baseEnd_613173 < baseStart_613173 := by decide
  rcases family_descends (prefixWord ++ tailWord_613173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613190 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_613190 : Nat := 118140960795 + 613190 * 2 ^ 59
def prefixEnd_613190 : Nat := 4983230072969 + 3 ^ 40 * 613190 * 2
def baseEnd_613190 : Nat := 104953734176853708334999

theorem tailTrace_613190 : CollatzResearch.WordTrace tailWord_613190 prefixEnd_613190 104953734176853708334999 := by
  unfold tailWord_613190
  simp only [CollatzResearch.WordTrace]
  refine ⟨698902395266400917486407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14909917765683219573043349 698902395266400917486407)
  ·
    refine ⟨1048353592899601376229611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698902395266400917486407 1048353592899601376229611)
    ·
      refine ⟨1572530389349402064344417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048353592899601376229611 1572530389349402064344417)
      ·
        refine ⟨1179397792012051548258313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1572530389349402064344417 1179397792012051548258313)
        ·
          refine ⟨884548344009038661193735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179397792012051548258313 884548344009038661193735)
          ·
            refine ⟨1326822516013557991790603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884548344009038661193735 1326822516013557991790603)
            ·
              refine ⟨1990233774020336987685905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326822516013557991790603 1990233774020336987685905)
              ·
                refine ⟨1492675330515252740764429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990233774020336987685905 1492675330515252740764429)
                ·
                  refine ⟨559753248943219777786661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1492675330515252740764429 559753248943219777786661)
                  ·
                    refine ⟨104953734176853708334999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559753248943219777786661 104953734176853708334999)
                    ·
                      rfl

theorem cell23_613190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_613190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613190 prefixEnd_613190 := by exact prefixLift 613190
  have htrace : WordTrace (prefixWord ++ tailWord_613190) baseStart_613190 baseEnd_613190 := by
    simpa [prefixWord, tailWord_613190, baseEnd_613190] using wordTrace_append hprefix tailTrace_613190
  have hstable : (prefixWord ++ tailWord_613190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613190).length < 2 ^ (prefixWord ++ tailWord_613190).sum := by decide
  have hdescent : baseEnd_613190 < baseStart_613190 := by decide
  rcases family_descends (prefixWord ++ tailWord_613190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613192 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_613192 : Nat := 118140960795 + 613192 * 2 ^ 59
def prefixEnd_613192 : Nat := 4983230072969 + 3 ^ 40 * 613192 * 2
def baseEnd_613192 : Nat := 314862229491870117179987

theorem tailTrace_613192 : CollatzResearch.WordTrace tailWord_613192 prefixEnd_613192 314862229491870117179987 := by
  unfold tailWord_613192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182474797258791850568915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14909966396345055800758553 11182474797258791850568915)
  ·
    refine ⟨16773712195888187775853373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11182474797258791850568915 16773712195888187775853373)
    ·
      refine ⟨6290142073458070415945015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16773712195888187775853373 6290142073458070415945015)
      ·
        refine ⟨9435213110187105623917523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290142073458070415945015 9435213110187105623917523)
        ·
          refine ⟨14152819665280658435876285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435213110187105623917523 14152819665280658435876285)
          ·
            refine ⟨5307307374480246913453607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14152819665280658435876285 5307307374480246913453607)
            ·
              refine ⟨7960961061720370370180411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307307374480246913453607 7960961061720370370180411)
              ·
                refine ⟨11941441592580555555270617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7960961061720370370180411 11941441592580555555270617)
                ·
                  refine ⟨8956081194435416666452963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941441592580555555270617 8956081194435416666452963)
                  ·
                    refine ⟨13434121791653124999679445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8956081194435416666452963 13434121791653124999679445)
                    ·
                      refine ⟨314862229491870117179987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13434121791653124999679445 314862229491870117179987)
                      ·
                        rfl

theorem cell23_613192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_613192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613192 prefixEnd_613192 := by exact prefixLift 613192
  have htrace : WordTrace (prefixWord ++ tailWord_613192) baseStart_613192 baseEnd_613192 := by
    simpa [prefixWord, tailWord_613192, baseEnd_613192] using wordTrace_append hprefix tailTrace_613192
  have hstable : (prefixWord ++ tailWord_613192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613192).length < 2 ^ (prefixWord ++ tailWord_613192).sum := by decide
  have hdescent : baseEnd_613192 < baseStart_613192 := by decide
  rcases family_descends (prefixWord ++ tailWord_613192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613196 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_613196 : Nat := 118140960795 + 613196 * 2 ^ 59
def prefixEnd_613196 : Nat := 4983230072969 + 3 ^ 40 * 613196 * 2
def baseEnd_613196 : Nat := 314864283414488101529969

theorem tailTrace_613196 : CollatzResearch.WordTrace tailWord_613196 prefixEnd_613196 314864283414488101529969 := by
  unfold tailWord_613196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182547743251546192141721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14910063657668728256188961 11182547743251546192141721)
  ·
    refine ⟨8386910807438659644106291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11182547743251546192141721 8386910807438659644106291)
    ·
      refine ⟨12580366211157989466159437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8386910807438659644106291 12580366211157989466159437)
      ·
        refine ⟨4717637329184246049809789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12580366211157989466159437 4717637329184246049809789)
        ·
          refine ⟨1769113998444092268678671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4717637329184246049809789 1769113998444092268678671)
          ·
            refine ⟨2653670997666138403018007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769113998444092268678671 2653670997666138403018007)
            ·
              refine ⟨3980506496499207604527011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653670997666138403018007 3980506496499207604527011)
              ·
                refine ⟨5970759744748811406790517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980506496499207604527011 5970759744748811406790517)
                ·
                  refine ⟨559758726070201069386611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5970759744748811406790517 559758726070201069386611)
                  ·
                    refine ⟨839638089105301604079917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559758726070201069386611 839638089105301604079917)
                    ·
                      refine ⟨314864283414488101529969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 839638089105301604079917 314864283414488101529969)
                      ·
                        rfl

theorem cell23_613196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_613196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613196 prefixEnd_613196 := by exact prefixLift 613196
  have htrace : WordTrace (prefixWord ++ tailWord_613196) baseStart_613196 baseEnd_613196 := by
    simpa [prefixWord, tailWord_613196, baseEnd_613196] using wordTrace_append hprefix tailTrace_613196
  have hstable : (prefixWord ++ tailWord_613196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613196).length < 2 ^ (prefixWord ++ tailWord_613196).sum := by decide
  have hdescent : baseEnd_613196 < baseStart_613196 := by decide
  rcases family_descends (prefixWord ++ tailWord_613196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613230 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_613230 : Nat := 118140960795 + 613230 * 2 ^ 59
def prefixEnd_613230 : Nat := 4983230072969 + 3 ^ 40 * 613230 * 2
def baseEnd_613230 : Nat := 314881741756740968504813

theorem tailTrace_613230 : CollatzResearch.WordTrace tailWord_613230 prefixEnd_613230 314881741756740968504813 := by
  unfold tailWord_613230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795791946047489523877643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14910890378919944127347429 2795791946047489523877643)
  ·
    refine ⟨4193687919071234285816465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2795791946047489523877643 4193687919071234285816465)
    ·
      refine ⟨3145265939303425714362349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193687919071234285816465 3145265939303425714362349)
      ·
        refine ⟨1179474727238784642885881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3145265939303425714362349 1179474727238784642885881)
        ·
          refine ⟨884606045429088482164411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179474727238784642885881 884606045429088482164411)
          ·
            refine ⟨1326909068143632723246617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884606045429088482164411 1326909068143632723246617)
            ·
              refine ⟨995181801107724542434963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326909068143632723246617 995181801107724542434963)
              ·
                refine ⟨1492772701661586813652445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995181801107724542434963 1492772701661586813652445)
                ·
                  refine ⟨559789763123095055119667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1492772701661586813652445 559789763123095055119667)
                  ·
                    refine ⟨839684644684642582679501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559789763123095055119667 839684644684642582679501)
                    ·
                      refine ⟨314881741756740968504813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 839684644684642582679501 314881741756740968504813)
                      ·
                        rfl

theorem cell23_613230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_613230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613230 prefixEnd_613230 := by exact prefixLift 613230
  have htrace : WordTrace (prefixWord ++ tailWord_613230) baseStart_613230 baseEnd_613230 := by
    simpa [prefixWord, tailWord_613230, baseEnd_613230] using wordTrace_append hprefix tailTrace_613230
  have hstable : (prefixWord ++ tailWord_613230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613230).length < 2 ^ (prefixWord ++ tailWord_613230).sum := by decide
  have hdescent : baseEnd_613230 < baseStart_613230 := by decide
  rcases family_descends (prefixWord ++ tailWord_613230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613239 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_613239 : Nat := 118140960795 + 613239 * 2 ^ 59
def prefixEnd_613239 : Nat := 4983230072969 + 3 ^ 40 * 613239 * 2
def baseEnd_613239 : Nat := 314886363082631433292271

theorem tailTrace_613239 : CollatzResearch.WordTrace tailWord_613239 prefixEnd_613239 314886363082631433292271 := by
  unfold tailWord_613239
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366663825347310728098771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911109216898207152065847 22366663825347310728098771)
  ·
    refine ⟨33549995738020966092148157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22366663825347310728098771 33549995738020966092148157)
    ·
      refine ⟨12581248401757862284555559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33549995738020966092148157 12581248401757862284555559)
      ·
        refine ⟨18871872602636793426833339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581248401757862284555559 18871872602636793426833339)
        ·
          refine ⟨28307808903955190140250009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18871872602636793426833339 28307808903955190140250009)
          ·
            refine ⟨21230856677966392605187507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28307808903955190140250009 21230856677966392605187507)
            ·
              refine ⟨31846285016949588907781261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21230856677966392605187507 31846285016949588907781261)
              ·
                refine ⟨11942356881356095840417973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31846285016949588907781261 11942356881356095840417973)
                ·
                  refine ⟨1119595957627133985039185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11942356881356095840417973 1119595957627133985039185)
                  ·
                    refine ⟨839696968220350488779389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1119595957627133985039185 839696968220350488779389)
                    ·
                      refine ⟨314886363082631433292271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 839696968220350488779389 314886363082631433292271)
                      ·
                        rfl

theorem cell23_613239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_613239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613239 prefixEnd_613239 := by exact prefixLift 613239
  have htrace : WordTrace (prefixWord ++ tailWord_613239) baseStart_613239 baseEnd_613239 := by
    simpa [prefixWord, tailWord_613239, baseEnd_613239] using wordTrace_append hprefix tailTrace_613239
  have hstable : (prefixWord ++ tailWord_613239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613239).length < 2 ^ (prefixWord ++ tailWord_613239).sum := by decide
  have hdescent : baseEnd_613239 < baseStart_613239 := by decide
  rcases family_descends (prefixWord ++ tailWord_613239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613242 : List Nat := [3, 1, 1, 1, 1, 1, 3, 12]
def baseStart_613242 : Nat := 118140960795 + 613242 * 2 ^ 59
def prefixEnd_613242 : Nat := 4983230072969 + 3 ^ 40 * 613242 * 2
def baseEnd_613242 : Nat := 11662514945355367464991

theorem tailTrace_613242 : CollatzResearch.WordTrace tailWord_613242 prefixEnd_613242 11662514945355367464991 := by
  unfold tailWord_613242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591693311084110560114495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14911182162890961493638653 5591693311084110560114495)
  ·
    refine ⟨8387539966626165840171743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591693311084110560114495 8387539966626165840171743)
    ·
      refine ⟨12581309949939248760257615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387539966626165840171743 12581309949939248760257615)
      ·
        refine ⟨18871964924908873140386423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581309949939248760257615 18871964924908873140386423)
        ·
          refine ⟨28307947387363309710579635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18871964924908873140386423 28307947387363309710579635)
          ·
            refine ⟨42461921081044964565869453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28307947387363309710579635 42461921081044964565869453)
            ·
              refine ⟨15923220405391861712201045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42461921081044964565869453 15923220405391861712201045)
              ·
                refine ⟨11662514945355367464991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 15923220405391861712201045 11662514945355367464991)
                ·
                  rfl

theorem cell23_613242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_613242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613242 prefixEnd_613242 := by exact prefixLift 613242
  have htrace : WordTrace (prefixWord ++ tailWord_613242) baseStart_613242 baseEnd_613242 := by
    simpa [prefixWord, tailWord_613242, baseEnd_613242] using wordTrace_append hprefix tailTrace_613242
  have hstable : (prefixWord ++ tailWord_613242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613242).length < 2 ^ (prefixWord ++ tailWord_613242).sum := by decide
  have hdescent : baseEnd_613242 < baseStart_613242 := by decide
  rcases family_descends (prefixWord ++ tailWord_613242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613253 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_613253 : Nat := 118140960795 + 613253 * 2 ^ 59
def prefixEnd_613253 : Nat := 4983230072969 + 3 ^ 40 * 613253 * 2
def baseEnd_613253 : Nat := 314893551811794378517207

theorem tailTrace_613253 : CollatzResearch.WordTrace tailWord_613253 prefixEnd_613253 314893551811794378517207 := by
  unfold tailWord_613253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367174447296591119108413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911449631531060746072275 22367174447296591119108413)
  ·
    refine ⟨8387690417736221669665655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22367174447296591119108413 8387690417736221669665655)
    ·
      refine ⟨12581535626604332504498483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387690417736221669665655 12581535626604332504498483)
      ·
        refine ⟨18872303439906498756747725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581535626604332504498483 18872303439906498756747725)
        ·
          refine ⟨7077113789964937033780397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18872303439906498756747725 7077113789964937033780397)
          ·
            refine ⟨2653917671236851387667649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7077113789964937033780397 2653917671236851387667649)
            ·
              refine ⟨1990438253427638540750737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653917671236851387667649 1990438253427638540750737)
              ·
                refine ⟨1492828690070728905563053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990438253427638540750737 1492828690070728905563053)
                ·
                  refine ⟨559810758776523339586145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1492828690070728905563053 559810758776523339586145)
                  ·
                    refine ⟨419858069082392504689609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559810758776523339586145 419858069082392504689609)
                    ·
                      refine ⟨314893551811794378517207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419858069082392504689609 314893551811794378517207)
                      ·
                        rfl

theorem cell23_613253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_613253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613253 prefixEnd_613253 := by exact prefixLift 613253
  have htrace : WordTrace (prefixWord ++ tailWord_613253) baseStart_613253 baseEnd_613253 := by
    simpa [prefixWord, tailWord_613253, baseEnd_613253] using wordTrace_append hprefix tailTrace_613253
  have hstable : (prefixWord ++ tailWord_613253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613253).length < 2 ^ (prefixWord ++ tailWord_613253).sum := by decide
  have hdescent : baseEnd_613253 < baseStart_613253 := by decide
  rcases family_descends (prefixWord ++ tailWord_613253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613259 : List Nat := [1, 1, 1, 1, 4, 2, 6, 7]
def baseStart_613259 : Nat := 118140960795 + 613259 * 2 ^ 59
def prefixEnd_613259 : Nat := 4983230072969 + 3 ^ 40 * 613259 * 2
def baseEnd_613259 : Nat := 11662838247989679816377

theorem tailTrace_613259 : CollatzResearch.WordTrace tailWord_613259 prefixEnd_613259 11662838247989679816377 := by
  unfold tailWord_613259
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367393285274854143826831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911595523516569429217887 22367393285274854143826831)
  ·
    refine ⟨33551089927912281215740247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22367393285274854143826831 33551089927912281215740247)
    ·
      refine ⟨50326634891868421823610371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33551089927912281215740247 50326634891868421823610371)
      ·
        refine ⟨75489952337802632735415557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50326634891868421823610371 75489952337802632735415557)
        ·
          refine ⟨14154366063337993637890417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75489952337802632735415557 14154366063337993637890417)
          ·
            refine ⟨10615774547503495228417813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14154366063337993637890417 10615774547503495228417813)
            ·
              refine ⟨497614431914226338832085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10615774547503495228417813 497614431914226338832085)
              ·
                refine ⟨11662838247989679816377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 497614431914226338832085 11662838247989679816377)
                ·
                  rfl

theorem cell23_613259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 7].length) (baseStart_613259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613259 prefixEnd_613259 := by exact prefixLift 613259
  have htrace : WordTrace (prefixWord ++ tailWord_613259) baseStart_613259 baseEnd_613259 := by
    simpa [prefixWord, tailWord_613259, baseEnd_613259] using wordTrace_append hprefix tailTrace_613259
  have hstable : (prefixWord ++ tailWord_613259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613259).length < 2 ^ (prefixWord ++ tailWord_613259).sum := by decide
  have hdescent : baseEnd_613259 < baseStart_613259 := by decide
  rcases family_descends (prefixWord ++ tailWord_613259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613276 : List Nat := [2, 2, 3, 3, 2, 2, 9]
def baseStart_613276 : Nat := 118140960795 + 613276 * 2 ^ 59
def prefixEnd_613276 : Nat := 4983230072969 + 3 ^ 40 * 613276 * 2
def baseEnd_613276 : Nat := 3887720516874664055921

theorem tailTrace_613276 : CollatzResearch.WordTrace tailWord_613276 prefixEnd_613276 3887720516874664055921 := by
  unfold tailWord_613276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184006663106633023597841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14912008884142177364797121 11184006663106633023597841)
  ·
    refine ⟨8388004997329974767698381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11184006663106633023597841 8388004997329974767698381)
    ·
      refine ⟨3145501873998740537886893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8388004997329974767698381 3145501873998740537886893)
      ·
        refine ⟨1179563202749527701707585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3145501873998740537886893 1179563202749527701707585)
        ·
          refine ⟨884672402062145776280689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179563202749527701707585 884672402062145776280689)
          ·
            refine ⟨663504301546609332210517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884672402062145776280689 663504301546609332210517)
            ·
              refine ⟨3887720516874664055921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 663504301546609332210517 3887720516874664055921)
              ·
                rfl

theorem cell23_613276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 9].length) (baseStart_613276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613276 prefixEnd_613276 := by exact prefixLift 613276
  have htrace : WordTrace (prefixWord ++ tailWord_613276) baseStart_613276 baseEnd_613276 := by
    simpa [prefixWord, tailWord_613276, baseEnd_613276] using wordTrace_append hprefix tailTrace_613276
  have hstable : (prefixWord ++ tailWord_613276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613276).length < 2 ^ (prefixWord ++ tailWord_613276).sum := by decide
  have hdescent : baseEnd_613276 < baseStart_613276 := by decide
  rcases family_descends (prefixWord ++ tailWord_613276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613287 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_613287 : Nat := 118140960795 + 613287 * 2 ^ 59
def prefixEnd_613287 : Nat := 4983230072969 + 3 ^ 40 * 613287 * 2
def baseEnd_613287 : Nat := 314911010154047245492051

theorem tailTrace_613287 : CollatzResearch.WordTrace tailWord_613287 prefixEnd_613287 314911010154047245492051 := by
  unfold tailWord_613287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22368414529173414925846115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14912276352782276617230743 22368414529173414925846115)
  ·
    refine ⟨33552621793760122388769173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22368414529173414925846115 33552621793760122388769173)
    ·
      refine ⟨1572779146582505736973555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33552621793760122388769173 1572779146582505736973555)
      ·
        refine ⟨2359168719873758605460333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572779146582505736973555 2359168719873758605460333)
        ·
          refine ⟨884688269952659477047625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2359168719873758605460333 884688269952659477047625)
          ·
            refine ⟨663516202464494607785719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884688269952659477047625 663516202464494607785719)
            ·
              refine ⟨995274303696741911678579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663516202464494607785719 995274303696741911678579)
              ·
                refine ⟨1492911455545112867517869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995274303696741911678579 1492911455545112867517869)
                ·
                  refine ⟨559841795829417325319201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1492911455545112867517869 559841795829417325319201)
                  ·
                    refine ⟨419881346872062993989401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559841795829417325319201 419881346872062993989401)
                    ·
                      refine ⟨314911010154047245492051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 419881346872062993989401 314911010154047245492051)
                      ·
                        rfl

theorem cell23_613287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_613287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613287 prefixEnd_613287 := by exact prefixLift 613287
  have htrace : WordTrace (prefixWord ++ tailWord_613287) baseStart_613287 baseEnd_613287 := by
    simpa [prefixWord, tailWord_613287, baseEnd_613287] using wordTrace_append hprefix tailTrace_613287
  have hstable : (prefixWord ++ tailWord_613287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613287).length < 2 ^ (prefixWord ++ tailWord_613287).sum := by decide
  have hdescent : baseEnd_613287 < baseStart_613287 := by decide
  rcases family_descends (prefixWord ++ tailWord_613287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613293 : List Nat := [1, 5, 2, 3, 1, 1, 2, 8]
def baseStart_613293 : Nat := 118140960795 + 613293 * 2 ^ 59
def prefixEnd_613293 : Nat := 4983230072969 + 3 ^ 40 * 613293 * 2
def baseEnd_613293 : Nat := 11663484853258304519149

theorem tailTrace_613293 : CollatzResearch.WordTrace tailWord_613293 prefixEnd_613293 11663484853258304519149 := by
  unfold tailWord_613293
  simp only [CollatzResearch.WordTrace]
  refine ⟨22368633367151677950564533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14912422244767785300376355 22368633367151677950564533)
  ·
    refine ⟨2097059378170469807865425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22368633367151677950564533 2097059378170469807865425)
    ·
      refine ⟨1572794533627852355899069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2097059378170469807865425 1572794533627852355899069)
      ·
        refine ⟨589797950110444633462151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1572794533627852355899069 589797950110444633462151)
        ·
          refine ⟨884696925165666950193227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589797950110444633462151 884696925165666950193227)
          ·
            refine ⟨1327045387748500425289841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884696925165666950193227 1327045387748500425289841)
            ·
              refine ⟨995284040811375318967381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327045387748500425289841 995284040811375318967381)
              ·
                refine ⟨11663484853258304519149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 995284040811375318967381 11663484853258304519149)
                ·
                  rfl

theorem cell23_613293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 8].length) (baseStart_613293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613293 prefixEnd_613293 := by exact prefixLift 613293
  have htrace : WordTrace (prefixWord ++ tailWord_613293) baseStart_613293 baseEnd_613293 := by
    simpa [prefixWord, tailWord_613293, baseEnd_613293] using wordTrace_append hprefix tailTrace_613293
  have hstable : (prefixWord ++ tailWord_613293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613293).length < 2 ^ (prefixWord ++ tailWord_613293).sum := by decide
  have hdescent : baseEnd_613293 < baseStart_613293 := by decide
  rcases family_descends (prefixWord ++ tailWord_613293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613297 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_613297 : Nat := 118140960795 + 613297 * 2 ^ 59
def prefixEnd_613297 : Nat := 4983230072969 + 3 ^ 40 * 613297 * 2
def baseEnd_613297 : Nat := 104972048320197402122335

theorem tailTrace_613297 : CollatzResearch.WordTrace tailWord_613297 prefixEnd_613297 104972048320197402122335 := by
  unfold tailWord_613297
  simp only [CollatzResearch.WordTrace]
  refine ⟨22368779259137186633710145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14912519506091457755806763 22368779259137186633710145)
  ·
    refine ⟨16776584444352889975282609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22368779259137186633710145 16776584444352889975282609)
    ·
      refine ⟨12582438333264667481461957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16776584444352889975282609 12582438333264667481461957)
      ·
        refine ⟨2359207187487125152774117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12582438333264667481461957 2359207187487125152774117)
        ·
          refine ⟨442351347653835966145147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2359207187487125152774117 442351347653835966145147)
          ·
            refine ⟨663527021480753949217721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442351347653835966145147 663527021480753949217721)
            ·
              refine ⟨497645266110565461913291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663527021480753949217721 497645266110565461913291)
              ·
                refine ⟨746467899165848192869937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497645266110565461913291 746467899165848192869937)
                ·
                  refine ⟨559850924374386144652453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746467899165848192869937 559850924374386144652453)
                  ·
                    refine ⟨104972048320197402122335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559850924374386144652453 104972048320197402122335)
                    ·
                      rfl

theorem cell23_613297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_613297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613297 prefixEnd_613297 := by exact prefixLift 613297
  have htrace : WordTrace (prefixWord ++ tailWord_613297) baseStart_613297 baseEnd_613297 := by
    simpa [prefixWord, tailWord_613297, baseEnd_613297] using wordTrace_append hprefix tailTrace_613297
  have hstable : (prefixWord ++ tailWord_613297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613297).length < 2 ^ (prefixWord ++ tailWord_613297).sum := by decide
  have hdescent : baseEnd_613297 < baseStart_613297 := by decide
  rcases family_descends (prefixWord ++ tailWord_613297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613329 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_613329 : Nat := 118140960795 + 613329 * 2 ^ 59
def prefixEnd_613329 : Nat := 4983230072969 + 3 ^ 40 * 613329 * 2
def baseEnd_613329 : Nat := 314932576341536081166857

theorem tailTrace_613329 : CollatzResearch.WordTrace tailWord_613329 prefixEnd_613329 314932576341536081166857 := by
  unfold tailWord_613329
  simp only [CollatzResearch.WordTrace]
  refine ⟨22369946395021256098875041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14913297596680837399250027 22369946395021256098875041)
  ·
    refine ⟨16777459796265942074156281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22369946395021256098875041 16777459796265942074156281)
    ·
      refine ⟨12583094847199456555617211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16777459796265942074156281 12583094847199456555617211)
      ·
        refine ⟨18874642270799184833425817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12583094847199456555617211 18874642270799184833425817)
        ·
          refine ⟨14155981703099388625069363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18874642270799184833425817 14155981703099388625069363)
          ·
            refine ⟨21233972554649082937604045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155981703099388625069363 21233972554649082937604045)
            ·
              refine ⟨7962739707993406101601517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21233972554649082937604045 7962739707993406101601517)
              ·
                refine ⟨2986027390497527288100569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7962739707993406101601517 2986027390497527288100569)
                ·
                  refine ⟨2239520542873145466075427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2986027390497527288100569 2239520542873145466075427)
                  ·
                    refine ⟨3359280814309718199113141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2239520542873145466075427 3359280814309718199113141)
                    ·
                      refine ⟨314932576341536081166857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3359280814309718199113141 314932576341536081166857)
                      ·
                        rfl

theorem cell23_613329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_613329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613329 prefixEnd_613329 := by exact prefixLift 613329
  have htrace : WordTrace (prefixWord ++ tailWord_613329) baseStart_613329 baseEnd_613329 := by
    simpa [prefixWord, tailWord_613329, baseEnd_613329] using wordTrace_append hprefix tailTrace_613329
  have hstable : (prefixWord ++ tailWord_613329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613329).length < 2 ^ (prefixWord ++ tailWord_613329).sum := by decide
  have hdescent : baseEnd_613329 < baseStart_613329 := by decide
  rcases family_descends (prefixWord ++ tailWord_613329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613366 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_613366 : Nat := 118140960795 + 613366 * 2 ^ 59
def prefixEnd_613366 : Nat := 4983230072969 + 3 ^ 40 * 613366 * 2
def baseEnd_613366 : Nat := 34994619458416937378243

theorem tailTrace_613366 : CollatzResearch.WordTrace tailWord_613366 prefixEnd_613366 34994619458416937378243 := by
  unfold tailWord_613366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398205993492950713623247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14914197263924807611981301 1398205993492950713623247)
  ·
    refine ⟨2097308990239426070434871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398205993492950713623247 2097308990239426070434871)
    ·
      refine ⟨3145963485359139105652307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097308990239426070434871 3145963485359139105652307)
      ·
        refine ⟨4718945228038708658478461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145963485359139105652307 4718945228038708658478461)
        ·
          refine ⟨1769604460514515746929423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4718945228038708658478461 1769604460514515746929423)
          ·
            refine ⟨2654406690771773620394135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769604460514515746929423 2654406690771773620394135)
            ·
              refine ⟨3981610036157660430591203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654406690771773620394135 3981610036157660430591203)
              ·
                refine ⟨5972415054236490645886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981610036157660430591203 5972415054236490645886805)
                ·
                  refine ⟨34994619458416937378243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5972415054236490645886805 34994619458416937378243)
                  ·
                    rfl

theorem cell23_613366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_613366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613366 prefixEnd_613366 := by exact prefixLift 613366
  have htrace : WordTrace (prefixWord ++ tailWord_613366) baseStart_613366 baseEnd_613366 := by
    simpa [prefixWord, tailWord_613366, baseEnd_613366] using wordTrace_append hprefix tailTrace_613366
  have hstable : (prefixWord ++ tailWord_613366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613366).length < 2 ^ (prefixWord ++ tailWord_613366).sum := by decide
  have hdescent : baseEnd_613366 < baseStart_613366 := by decide
  rcases family_descends (prefixWord ++ tailWord_613366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613383 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 5]
def baseStart_613383 : Nat := 118140960795 + 613383 * 2 ^ 59
def prefixEnd_613383 : Nat := 4983230072969 + 3 ^ 40 * 613383 * 2
def baseEnd_613383 : Nat := 34995589366319874432401

theorem tailTrace_613383 : CollatzResearch.WordTrace tailWord_613383 prefixEnd_613383 34995589366319874432401 := by
  unfold tailWord_613383
  simp only [CollatzResearch.WordTrace]
  refine ⟨22371915936825623321340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14914610624550415547560535 22371915936825623321340803)
  ·
    refine ⟨33557873905238434982011205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22371915936825623321340803 33557873905238434982011205)
    ·
      refine ⟨6292101357232206559127101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33557873905238434982011205 6292101357232206559127101)
      ·
        refine ⟨2359538008962077459672663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6292101357232206559127101 2359538008962077459672663)
        ·
          refine ⟨3539307013443116189508995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359538008962077459672663 3539307013443116189508995)
          ·
            refine ⟨5308960520164674284263493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539307013443116189508995 5308960520164674284263493)
            ·
              refine ⟨995430097530876428299405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5308960520164674284263493 995430097530876428299405)
              ·
                refine ⟨373286286574078660612277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995430097530876428299405 373286286574078660612277)
                ·
                  refine ⟨34995589366319874432401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 373286286574078660612277 34995589366319874432401)
                  ·
                    rfl

theorem cell23_613383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 5].length) (baseStart_613383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613383 prefixEnd_613383 := by exact prefixLift 613383
  have htrace : WordTrace (prefixWord ++ tailWord_613383) baseStart_613383 baseEnd_613383 := by
    simpa [prefixWord, tailWord_613383, baseEnd_613383] using wordTrace_append hprefix tailTrace_613383
  have hstable : (prefixWord ++ tailWord_613383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613383).length < 2 ^ (prefixWord ++ tailWord_613383).sum := by decide
  have hdescent : baseEnd_613383 < baseStart_613383 := by decide
  rcases family_descends (prefixWord ++ tailWord_613383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613460 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_613460 : Nat := 118140960795 + 613460 * 2 ^ 59
def prefixEnd_613460 : Nat := 4983230072969 + 3 ^ 40 * 613460 * 2
def baseEnd_613460 : Nat := 104999947435758356209585

theorem tailTrace_613460 : CollatzResearch.WordTrace tailWord_613460 prefixEnd_613460 104999947435758356209585 := by
  unfold tailWord_613460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187362178773332735946917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14916482905031110314595889 11187362178773332735946917)
  ·
    refine ⟨2097630408519999887990047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11187362178773332735946917 2097630408519999887990047)
    ·
      refine ⟨3146445612779999831985071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097630408519999887990047 3146445612779999831985071)
      ·
        refine ⟨4719668419169999747977607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146445612779999831985071 4719668419169999747977607)
        ·
          refine ⟨7079502628754999621966411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719668419169999747977607 7079502628754999621966411)
          ·
            refine ⟨10619253943132499432949617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7079502628754999621966411 10619253943132499432949617)
            ·
              refine ⟨7964440457349374574712213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10619253943132499432949617 7964440457349374574712213)
              ·
                refine ⟨373333146438251933189635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7964440457349374574712213 373333146438251933189635)
                ·
                  refine ⟨559999719657377899784453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373333146438251933189635 559999719657377899784453)
                  ·
                    refine ⟨104999947435758356209585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559999719657377899784453 104999947435758356209585)
                    ·
                      rfl

theorem cell23_613460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_613460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613460 prefixEnd_613460 := by exact prefixLift 613460
  have htrace : WordTrace (prefixWord ++ tailWord_613460) baseStart_613460 baseEnd_613460 := by
    simpa [prefixWord, tailWord_613460, baseEnd_613460] using wordTrace_append hprefix tailTrace_613460
  have hstable : (prefixWord ++ tailWord_613460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613460).length < 2 ^ (prefixWord ++ tailWord_613460).sum := by decide
  have hdescent : baseEnd_613460 < baseStart_613460 := by decide
  rcases family_descends (prefixWord ++ tailWord_613460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613466 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_613466 : Nat := 118140960795 + 613466 * 2 ^ 59
def prefixEnd_613466 : Nat := 4983230072969 + 3 ^ 40 * 613466 * 2
def baseEnd_613466 : Nat := 315002923191202045153727

theorem tailTrace_613466 : CollatzResearch.WordTrace tailWord_613466 prefixEnd_613466 315002923191202045153727 := by
  unfold tailWord_613466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5593735798881232124153063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14916628797016618997741501 5593735798881232124153063)
  ·
    refine ⟨8390603698321848186229595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5593735798881232124153063 8390603698321848186229595)
    ·
      refine ⟨12585905547482772279344393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8390603698321848186229595 12585905547482772279344393)
      ·
        refine ⟨9439429160612079209508295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12585905547482772279344393 9439429160612079209508295)
        ·
          refine ⟨14159143740918118814262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9439429160612079209508295 14159143740918118814262443)
          ·
            refine ⟨21238715611377178221393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14159143740918118814262443 21238715611377178221393665)
            ·
              refine ⟨15929036708532883666045249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21238715611377178221393665 15929036708532883666045249)
              ·
                refine ⟨11946777531399662749533937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15929036708532883666045249 11946777531399662749533937)
                ·
                  refine ⟨8960083148549747062150453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11946777531399662749533937 8960083148549747062150453)
                  ·
                    refine ⟨840007795176538787076605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8960083148549747062150453 840007795176538787076605)
                    ·
                      refine ⟨315002923191202045153727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840007795176538787076605 315002923191202045153727)
                      ·
                        rfl

theorem cell23_613466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_613466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613466 prefixEnd_613466 := by exact prefixLift 613466
  have htrace : WordTrace (prefixWord ++ tailWord_613466) baseStart_613466 baseEnd_613466 := by
    simpa [prefixWord, tailWord_613466, baseEnd_613466] using wordTrace_append hprefix tailTrace_613466
  have hstable : (prefixWord ++ tailWord_613466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613466).length < 2 ^ (prefixWord ++ tailWord_613466).sum := by decide
  have hdescent : baseEnd_613466 < baseStart_613466 := by decide
  rcases family_descends (prefixWord ++ tailWord_613466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613473 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 6]
def baseStart_613473 : Nat := 118140960795 + 613473 * 2 ^ 59
def prefixEnd_613473 : Nat := 4983230072969 + 3 ^ 40 * 613473 * 2
def baseEnd_613473 : Nat := 35000724172864835307355

theorem tailTrace_613473 : CollatzResearch.WordTrace tailWord_613473 prefixEnd_613473 35000724172864835307355 := by
  unfold tailWord_613473
  simp only [CollatzResearch.WordTrace]
  refine ⟨22375198506499568692117073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14916799004333045794744715 22375198506499568692117073)
  ·
    refine ⟨16781398879874676519087805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22375198506499568692117073 16781398879874676519087805)
    ·
      refine ⟨6293024579953003694657927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16781398879874676519087805 6293024579953003694657927)
      ·
        refine ⟨9439536869929505541986891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293024579953003694657927 9439536869929505541986891)
        ·
          refine ⟨14159305304894258312980337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9439536869929505541986891 14159305304894258312980337)
          ·
            refine ⟨10619478978670693734735253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14159305304894258312980337 10619478978670693734735253)
            ·
              refine ⟨497788077125188768815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10619478978670693734735253 497788077125188768815715)
              ·
                refine ⟨746682115687783153223573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497788077125188768815715 746682115687783153223573)
                ·
                  refine ⟨35000724172864835307355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 746682115687783153223573 35000724172864835307355)
                  ·
                    rfl

theorem cell23_613473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_613473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613473 prefixEnd_613473 := by exact prefixLift 613473
  have htrace : WordTrace (prefixWord ++ tailWord_613473) baseStart_613473 baseEnd_613473 := by
    simpa [prefixWord, tailWord_613473, baseEnd_613473] using wordTrace_append hprefix tailTrace_613473
  have hstable : (prefixWord ++ tailWord_613473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613473).length < 2 ^ (prefixWord ++ tailWord_613473).sum := by decide
  have hdescent : baseEnd_613473 < baseStart_613473 := by decide
  rcases family_descends (prefixWord ++ tailWord_613473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613533 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_613533 : Nat := 118140960795 + 613533 * 2 ^ 59
def prefixEnd_613533 : Nat := 4983230072969 + 3 ^ 40 * 613533 * 2
def baseEnd_613533 : Nat := 105012442131684427671973

theorem tailTrace_613533 : CollatzResearch.WordTrace tailWord_613533 prefixEnd_613533 105012442131684427671973 := by
  unfold tailWord_613533
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377386886282198939301253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14918257924188132626200835 22377386886282198939301253)
  ·
    refine ⟨4195760041177912301118985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22377386886282198939301253 4195760041177912301118985)
    ·
      refine ⟨3146820030883434225839239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4195760041177912301118985 3146820030883434225839239)
      ·
        refine ⟨4720230046325151338758859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146820030883434225839239 4720230046325151338758859)
        ·
          refine ⟨7080345069487727008138289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720230046325151338758859 7080345069487727008138289)
          ·
            refine ⟨5310258802115795256103717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080345069487727008138289 5310258802115795256103717)
            ·
              refine ⟨995673525396711610519447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5310258802115795256103717 995673525396711610519447)
              ·
                refine ⟨1493510288095067415779171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995673525396711610519447 1493510288095067415779171)
                ·
                  refine ⟨2240265432142601123668757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493510288095067415779171 2240265432142601123668757)
                  ·
                    refine ⟨105012442131684427671973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2240265432142601123668757 105012442131684427671973)
                    ·
                      rfl

theorem cell23_613533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_613533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613533 prefixEnd_613533 := by exact prefixLift 613533
  have htrace : WordTrace (prefixWord ++ tailWord_613533) baseStart_613533 baseEnd_613533 := by
    simpa [prefixWord, tailWord_613533, baseEnd_613533] using wordTrace_append hprefix tailTrace_613533
  have hstable : (prefixWord ++ tailWord_613533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613533).length < 2 ^ (prefixWord ++ tailWord_613533).sum := by decide
  have hdescent : baseEnd_613533 < baseStart_613533 := by decide
  rcases family_descends (prefixWord ++ tailWord_613533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613576 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_613576 : Nat := 118140960795 + 613576 * 2 ^ 59
def prefixEnd_613576 : Nat := 4983230072969 + 3 ^ 40 * 613576 * 2
def baseEnd_613576 : Nat := 105019802021065538259407

theorem tailTrace_613576 : CollatzResearch.WordTrace tailWord_613576 prefixEnd_613576 105019802021065538259407 := by
  unfold tailWord_613576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11189477612563208641558291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14919303483417611522077721 11189477612563208641558291)
  ·
    refine ⟨16784216418844812962337437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11189477612563208641558291 16784216418844812962337437)
    ·
      refine ⟨6294081157066804860876539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16784216418844812962337437 6294081157066804860876539)
      ·
        refine ⟨9441121735600207291314809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294081157066804860876539 9441121735600207291314809)
        ·
          refine ⟨7080841301700155468486107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9441121735600207291314809 7080841301700155468486107)
          ·
            refine ⟨10621261952550233202729161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080841301700155468486107 10621261952550233202729161)
            ·
              refine ⟨7965946464412674902046871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10621261952550233202729161 7965946464412674902046871)
              ·
                refine ⟨11948919696619012353070307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965946464412674902046871 11948919696619012353070307)
                ·
                  refine ⟨17923379544928518529605461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11948919696619012353070307 17923379544928518529605461)
                  ·
                    refine ⟨105019802021065538259407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17923379544928518529605461 105019802021065538259407)
                    ·
                      rfl

theorem cell23_613576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_613576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613576 prefixEnd_613576 := by exact prefixLift 613576
  have htrace : WordTrace (prefixWord ++ tailWord_613576) baseStart_613576 baseEnd_613576 := by
    simpa [prefixWord, tailWord_613576, baseEnd_613576] using wordTrace_append hprefix tailTrace_613576
  have hstable : (prefixWord ++ tailWord_613576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613576).length < 2 ^ (prefixWord ++ tailWord_613576).sum := by decide
  have hdescent : baseEnd_613576 < baseStart_613576 := by decide
  rcases family_descends (prefixWord ++ tailWord_613576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613583 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 7, 2]
def baseStart_613583 : Nat := 118140960795 + 613583 * 2 ^ 59
def prefixEnd_613583 : Nat := 4983230072969 + 3 ^ 40 * 613583 * 2
def baseEnd_613583 : Nat := 315063000427778087390689

theorem tailTrace_613583 : CollatzResearch.WordTrace tailWord_613583 prefixEnd_613583 315063000427778087390689 := by
  unfold tailWord_613583
  simp only [CollatzResearch.WordTrace]
  refine ⟨22379210536101057478621403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14919473690734038319080935 22379210536101057478621403)
  ·
    refine ⟨33568815804151586217932105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22379210536101057478621403 33568815804151586217932105)
    ·
      refine ⟨25176611853113689663449079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33568815804151586217932105 25176611853113689663449079)
      ·
        refine ⟨37764917779670534495173619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25176611853113689663449079 37764917779670534495173619)
        ·
          refine ⟨56647376669505801742760429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37764917779670534495173619 56647376669505801742760429)
          ·
            refine ⟨21242766251064675653535161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56647376669505801742760429 21242766251064675653535161)
            ·
              refine ⟨15932074688298506740151371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21242766251064675653535161 15932074688298506740151371)
              ·
                refine ⟨23898112032447760110227057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15932074688298506740151371 23898112032447760110227057)
                ·
                  refine ⟨17923584024335820082670293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23898112032447760110227057 17923584024335820082670293)
                  ·
                    refine ⟨420084000570370783187585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17923584024335820082670293 420084000570370783187585)
                    ·
                      refine ⟨315063000427778087390689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420084000570370783187585 315063000427778087390689)
                      ·
                        rfl

theorem cell23_613583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7, 2].length) (baseStart_613583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613583 prefixEnd_613583 := by exact prefixLift 613583
  have htrace : WordTrace (prefixWord ++ tailWord_613583) baseStart_613583 baseEnd_613583 := by
    simpa [prefixWord, tailWord_613583, baseEnd_613583] using wordTrace_append hprefix tailTrace_613583
  have hstable : (prefixWord ++ tailWord_613583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613583).length < 2 ^ (prefixWord ++ tailWord_613583).sum := by decide
  have hdescent : baseEnd_613583 < baseStart_613583 := by decide
  rcases family_descends (prefixWord ++ tailWord_613583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613597 : List Nat := [1, 4, 3, 2, 2, 2, 2, 7]
def baseStart_613597 : Nat := 118140960795 + 613597 * 2 ^ 59
def prefixEnd_613597 : Nat := 4983230072969 + 3 ^ 40 * 613597 * 2
def baseEnd_613597 : Nat := 11669266265071890096875

theorem tailTrace_613597 : CollatzResearch.WordTrace tailWord_613597 prefixEnd_613597 11669266265071890096875 := by
  unfold tailWord_613597
  simp only [CollatzResearch.WordTrace]
  refine ⟨22379721158050337869631045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14919814105366891913087363 22379721158050337869631045)
  ·
    refine ⟨4196197717134438350555821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22379721158050337869631045 4196197717134438350555821)
    ·
      refine ⟨1573574143925414381458433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4196197717134438350555821 1573574143925414381458433)
      ·
        refine ⟨1180180607944060786093825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1573574143925414381458433 1180180607944060786093825)
        ·
          refine ⟨885135455958045589570369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180180607944060786093825 885135455958045589570369)
          ·
            refine ⟨663851591968534192177777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885135455958045589570369 663851591968534192177777)
            ·
              refine ⟨497888693976400644133333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663851591968534192177777 497888693976400644133333)
              ·
                refine ⟨11669266265071890096875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 497888693976400644133333 11669266265071890096875)
                ·
                  rfl

theorem cell23_613597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 7].length) (baseStart_613597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613597 prefixEnd_613597 := by exact prefixLift 613597
  have htrace : WordTrace (prefixWord ++ tailWord_613597) baseStart_613597 baseEnd_613597 := by
    simpa [prefixWord, tailWord_613597, baseEnd_613597] using wordTrace_append hprefix tailTrace_613597
  have hstable : (prefixWord ++ tailWord_613597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613597).length < 2 ^ (prefixWord ++ tailWord_613597).sum := by decide
  have hdescent : baseEnd_613597 < baseStart_613597 := by decide
  rcases family_descends (prefixWord ++ tailWord_613597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613690 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_613690 : Nat := 118140960795 + 613690 * 2 ^ 59
def prefixEnd_613690 : Nat := 4983230072969 + 3 ^ 40 * 613690 * 2
def baseEnd_613690 : Nat := 315117942857809168752697

theorem tailTrace_613690 : CollatzResearch.WordTrace tailWord_613690 prefixEnd_613690 315117942857809168752697 := by
  unfold tailWord_613690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595778286678353688191631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14922075431142276501844349 5595778286678353688191631)
  ·
    refine ⟨8393667430017530532287447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5595778286678353688191631 8393667430017530532287447)
    ·
      refine ⟨12590501145026295798431171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393667430017530532287447 12590501145026295798431171)
      ·
        refine ⟨18885751717539443697646757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590501145026295798431171 18885751717539443697646757)
        ·
          refine ⟨3541078447038645693308767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18885751717539443697646757 3541078447038645693308767)
          ·
            refine ⟨5311617670557968539963151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541078447038645693308767 5311617670557968539963151)
            ·
              refine ⟨7967426505836952809944727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311617670557968539963151 7967426505836952809944727)
              ·
                refine ⟨11951139758755429214917091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967426505836952809944727 11951139758755429214917091)
                ·
                  refine ⟨17926709638133143822375637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11951139758755429214917091 17926709638133143822375637)
                  ·
                    refine ⟨420157257143745558336929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17926709638133143822375637 420157257143745558336929)
                    ·
                      refine ⟨315117942857809168752697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420157257143745558336929 315117942857809168752697)
                      ·
                        rfl

theorem cell23_613690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_613690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613690 prefixEnd_613690 := by exact prefixLift 613690
  have htrace : WordTrace (prefixWord ++ tailWord_613690) baseStart_613690 baseEnd_613690 := by
    simpa [prefixWord, tailWord_613690, baseEnd_613690] using wordTrace_append hprefix tailTrace_613690
  have hstable : (prefixWord ++ tailWord_613690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613690).length < 2 ^ (prefixWord ++ tailWord_613690).sum := by decide
  have hdescent : baseEnd_613690 < baseStart_613690 := by decide
  rcases family_descends (prefixWord ++ tailWord_613690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613697 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_613697 : Nat := 118140960795 + 613697 * 2 ^ 59
def prefixEnd_613697 : Nat := 4983230072969 + 3 ^ 40 * 613697 * 2
def baseEnd_613697 : Nat := 315121537222390641365165

theorem tailTrace_613697 : CollatzResearch.WordTrace tailWord_613697 prefixEnd_613697 315121537222390641365165 := by
  unfold tailWord_613697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22383368457688054948271345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14922245638458703298847563 22383368457688054948271345)
  ·
    refine ⟨16787526343266041211203509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22383368457688054948271345 16787526343266041211203509)
    ·
      refine ⟨1573830594681191363550329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16787526343266041211203509 1573830594681191363550329)
      ·
        refine ⟨1180372946010893522662747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1573830594681191363550329 1180372946010893522662747)
        ·
          refine ⟨1770559419016340283994121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180372946010893522662747 1770559419016340283994121)
          ·
            refine ⟨1327919564262255212995591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770559419016340283994121 1327919564262255212995591)
            ·
              refine ⟨1991879346393382819493387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327919564262255212995591 1991879346393382819493387)
              ·
                refine ⟨2987819019590074229240081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991879346393382819493387 2987819019590074229240081)
                ·
                  refine ⟨2240864264692555671930061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987819019590074229240081 2240864264692555671930061)
                  ·
                    refine ⟨840324099259708376973773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240864264692555671930061 840324099259708376973773)
                    ·
                      refine ⟨315121537222390641365165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840324099259708376973773 315121537222390641365165)
                      ·
                        rfl

theorem cell23_613697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_613697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613697 prefixEnd_613697 := by exact prefixLift 613697
  have htrace : WordTrace (prefixWord ++ tailWord_613697) baseStart_613697 baseEnd_613697 := by
    simpa [prefixWord, tailWord_613697, baseEnd_613697] using wordTrace_append hprefix tailTrace_613697
  have hstable : (prefixWord ++ tailWord_613697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613697).length < 2 ^ (prefixWord ++ tailWord_613697).sum := by decide
  have hdescent : baseEnd_613697 < baseStart_613697 := by decide
  rcases family_descends (prefixWord ++ tailWord_613697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613717 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_613717 : Nat := 118140960795 + 613717 * 2 ^ 59
def prefixEnd_613717 : Nat := 4983230072969 + 3 ^ 40 * 613717 * 2
def baseEnd_613717 : Nat := 105043935611826854371691

theorem tailTrace_613717 : CollatzResearch.WordTrace tailWord_613717 prefixEnd_613717 105043935611826854371691 := by
  unfold tailWord_613717
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384097917615598363999405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14922731945077065575999603 22384097917615598363999405)
  ·
    refine ⟨8394036719105849386499777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22384097917615598363999405 8394036719105849386499777)
    ·
      refine ⟨6295527539329387039874833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8394036719105849386499777 6295527539329387039874833)
      ·
        refine ⟨4721645654497040279906125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6295527539329387039874833 4721645654497040279906125)
        ·
          refine ⟨1770617120436390104964797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4721645654497040279906125 1770617120436390104964797)
          ·
            refine ⟨663981420163646289361799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1770617120436390104964797 663981420163646289361799)
            ·
              refine ⟨995972130245469434042699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663981420163646289361799 995972130245469434042699)
              ·
                refine ⟨1493958195368204151064049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995972130245469434042699 1493958195368204151064049)
                ·
                  refine ⟨1120468646526153113298037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493958195368204151064049 1120468646526153113298037)
                  ·
                    refine ⟨105043935611826854371691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1120468646526153113298037 105043935611826854371691)
                    ·
                      rfl

theorem cell23_613717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_613717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613717 prefixEnd_613717 := by exact prefixLift 613717
  have htrace : WordTrace (prefixWord ++ tailWord_613717) baseStart_613717 baseEnd_613717 := by
    simpa [prefixWord, tailWord_613717, baseEnd_613717] using wordTrace_append hprefix tailTrace_613717
  have hstable : (prefixWord ++ tailWord_613717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613717).length < 2 ^ (prefixWord ++ tailWord_613717).sum := by decide
  have hdescent : baseEnd_613717 < baseStart_613717 := by decide
  rcases family_descends (prefixWord ++ tailWord_613717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613720 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_613720 : Nat := 118140960795 + 613720 * 2 ^ 59
def prefixEnd_613720 : Nat := 4983230072969 + 3 ^ 40 * 613720 * 2
def baseEnd_613720 : Nat := 315133347277444051377559

theorem tailTrace_613720 : CollatzResearch.WordTrace tailWord_613720 prefixEnd_613720 315133347277444051377559 := by
  unfold tailWord_613720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192103668302364938179307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14922804891069819917572409 11192103668302364938179307)
  ·
    refine ⟨16788155502453547407268961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11192103668302364938179307 16788155502453547407268961)
    ·
      refine ⟨12591116626840160555451721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16788155502453547407268961 12591116626840160555451721)
      ·
        refine ⟨9443337470130120416588791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12591116626840160555451721 9443337470130120416588791)
        ·
          refine ⟨14165006205195180624883187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9443337470130120416588791 14165006205195180624883187)
          ·
            refine ⟨21247509307792770937324781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14165006205195180624883187 21247509307792770937324781)
            ·
              refine ⟨7967815990422289101496793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21247509307792770937324781 7967815990422289101496793)
              ·
                refine ⟨5975861992816716826122595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7967815990422289101496793 5975861992816716826122595)
                ·
                  refine ⟨8963792989225075239183893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975861992816716826122595 8963792989225075239183893)
                  ·
                    refine ⟨420177796369925401836745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8963792989225075239183893 420177796369925401836745)
                    ·
                      refine ⟨315133347277444051377559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420177796369925401836745 315133347277444051377559)
                      ·
                        rfl

theorem cell23_613720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_613720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613720 prefixEnd_613720 := by exact prefixLift 613720
  have htrace : WordTrace (prefixWord ++ tailWord_613720) baseStart_613720 baseEnd_613720 := by
    simpa [prefixWord, tailWord_613720, baseEnd_613720] using wordTrace_append hprefix tailTrace_613720
  have hstable : (prefixWord ++ tailWord_613720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613720).length < 2 ^ (prefixWord ++ tailWord_613720).sum := by decide
  have hdescent : baseEnd_613720 < baseStart_613720 := by decide
  rcases family_descends (prefixWord ++ tailWord_613720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613733 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_613733 : Nat := 118140960795 + 613733 * 2 ^ 59
def prefixEnd_613733 : Nat := 4983230072969 + 3 ^ 40 * 613733 * 2
def baseEnd_613733 : Nat := 315140022525952500514999

theorem tailTrace_613733 : CollatzResearch.WordTrace tailWord_613733 prefixEnd_613733 315140022525952500514999 := by
  unfold tailWord_613733
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384681485557633096581853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14923120990371755397721235 22384681485557633096581853)
  ·
    refine ⟨8394255557084112411218195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22384681485557633096581853 8394255557084112411218195)
    ·
      refine ⟨12591383335626168616827293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8394255557084112411218195 12591383335626168616827293)
      ·
        refine ⟨4721768750859813231310235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12591383335626168616827293 4721768750859813231310235)
        ·
          refine ⟨7082653126289719846965353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721768750859813231310235 7082653126289719846965353)
          ·
            refine ⟨5311989844717289885224015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7082653126289719846965353 5311989844717289885224015)
            ·
              refine ⟨7967984767075934827836023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311989844717289885224015 7967984767075934827836023)
              ·
                refine ⟨11951977150613902241754035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967984767075934827836023 11951977150613902241754035)
                ·
                  refine ⟨17927965725920853362631053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11951977150613902241754035 17927965725920853362631053)
                  ·
                    refine ⟨6722987147220320010986645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17927965725920853362631053 6722987147220320010986645)
                    ·
                      refine ⟨315140022525952500514999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6722987147220320010986645 315140022525952500514999)
                      ·
                        rfl

theorem cell23_613733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_613733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613733 prefixEnd_613733 := by exact prefixLift 613733
  have htrace : WordTrace (prefixWord ++ tailWord_613733) baseStart_613733 baseEnd_613733 := by
    simpa [prefixWord, tailWord_613733, baseEnd_613733] using wordTrace_append hprefix tailTrace_613733
  have hstable : (prefixWord ++ tailWord_613733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613733).length < 2 ^ (prefixWord ++ tailWord_613733).sum := by decide
  have hdescent : baseEnd_613733 < baseStart_613733 := by decide
  rcases family_descends (prefixWord ++ tailWord_613733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613743 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 8]
def baseStart_613743 : Nat := 118140960795 + 613743 * 2 ^ 59
def prefixEnd_613743 : Nat := 4983230072969 + 3 ^ 40 * 613743 * 2
def baseEnd_613743 : Nat := 35016128592499717932217

theorem tailTrace_613743 : CollatzResearch.WordTrace tailWord_613743 prefixEnd_613743 35016128592499717932217 := by
  unfold tailWord_613743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22385046215521404804445883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14923364143680936536297255 22385046215521404804445883)
  ·
    refine ⟨33577569323282107206668825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22385046215521404804445883 33577569323282107206668825)
    ·
      refine ⟨25183176992461580405001619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33577569323282107206668825 25183176992461580405001619)
      ·
        refine ⟨37774765488692370607502429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25183176992461580405001619 37774765488692370607502429)
        ·
          refine ⟨14165537058259638977813411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37774765488692370607502429 14165537058259638977813411)
          ·
            refine ⟨21248305587389458466720117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14165537058259638977813411 21248305587389458466720117)
            ·
              refine ⟨1992028648817761731255011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21248305587389458466720117 1992028648817761731255011)
              ·
                refine ⟨2988042973226642596882517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992028648817761731255011 2988042973226642596882517)
                ·
                  refine ⟨35016128592499717932217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2988042973226642596882517 35016128592499717932217)
                  ·
                    rfl

theorem cell23_613743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 8].length) (baseStart_613743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613743 prefixEnd_613743 := by exact prefixLift 613743
  have htrace : WordTrace (prefixWord ++ tailWord_613743) baseStart_613743 baseEnd_613743 := by
    simpa [prefixWord, tailWord_613743, baseEnd_613743] using wordTrace_append hprefix tailTrace_613743
  have hstable : (prefixWord ++ tailWord_613743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613743).length < 2 ^ (prefixWord ++ tailWord_613743).sum := by decide
  have hdescent : baseEnd_613743 < baseStart_613743 := by decide
  rcases family_descends (prefixWord ++ tailWord_613743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613804 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_613804 : Nat := 118140960795 + 613804 * 2 ^ 59
def prefixEnd_613804 : Nat := 4983230072969 + 3 ^ 40 * 613804 * 2
def baseEnd_613804 : Nat := 315176479652421722727173

theorem tailTrace_613804 : CollatzResearch.WordTrace tailWord_613804 prefixEnd_613804 315176479652421722727173 := by
  unfold tailWord_613804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11193635534150206111208233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14924847378866941481610977 11193635534150206111208233)
  ·
    refine ⟨8395226650612654583406175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11193635534150206111208233 8395226650612654583406175)
    ·
      refine ⟨12592839975918981875109263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8395226650612654583406175 12592839975918981875109263)
      ·
        refine ⟨18889259963878472812663895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12592839975918981875109263 18889259963878472812663895)
        ·
          refine ⟨28333889945817709218995843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889259963878472812663895 28333889945817709218995843)
          ·
            refine ⟨42500834918726563828493765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28333889945817709218995843 42500834918726563828493765)
            ·
              refine ⟨7968906547261230717842581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42500834918726563828493765 7968906547261230717842581)
              ·
                refine ⟨373542494402870189898871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7968906547261230717842581 373542494402870189898871)
                ·
                  refine ⟨560313741604305284848307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373542494402870189898871 560313741604305284848307)
                  ·
                    refine ⟨840470612406457927272461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560313741604305284848307 840470612406457927272461)
                    ·
                      refine ⟨315176479652421722727173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840470612406457927272461 315176479652421722727173)
                      ·
                        rfl

theorem cell23_613804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_613804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613804 prefixEnd_613804 := by exact prefixLift 613804
  have htrace : WordTrace (prefixWord ++ tailWord_613804) baseStart_613804 baseEnd_613804 := by
    simpa [prefixWord, tailWord_613804, baseEnd_613804] using wordTrace_append hprefix tailTrace_613804
  have hstable : (prefixWord ++ tailWord_613804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613804).length < 2 ^ (prefixWord ++ tailWord_613804).sum := by decide
  have hdescent : baseEnd_613804 < baseStart_613804 := by decide
  rcases family_descends (prefixWord ++ tailWord_613804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613827 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 4]
def baseStart_613827 : Nat := 118140960795 + 613827 * 2 ^ 59
def prefixEnd_613827 : Nat := 4983230072969 + 3 ^ 40 * 613827 * 2
def baseEnd_613827 : Nat := 315188289707475132739567

theorem tailTrace_613827 : CollatzResearch.WordTrace tailWord_613827 prefixEnd_613827 315188289707475132739567 := by
  unfold tailWord_613827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22388109947217087150503735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14925406631478058100335823 22388109947217087150503735)
  ·
    refine ⟨33582164920825630725755603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22388109947217087150503735 33582164920825630725755603)
    ·
      refine ⟨50373247381238446088633405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33582164920825630725755603 50373247381238446088633405)
      ·
        refine ⟨18889967767964417283237527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50373247381238446088633405 18889967767964417283237527)
        ·
          refine ⟨28334951651946625924856291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889967767964417283237527 28334951651946625924856291)
          ·
            refine ⟨42502427477919938887284437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28334951651946625924856291 42502427477919938887284437)
            ·
              refine ⟨996150644013748567670729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42502427477919938887284437 996150644013748567670729)
              ·
                refine ⟨747112983010311425753047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996150644013748567670729 747112983010311425753047)
                ·
                  refine ⟨1120669474515467138629571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747112983010311425753047 1120669474515467138629571)
                  ·
                    refine ⟨1681004211773200707944357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120669474515467138629571 1681004211773200707944357)
                    ·
                      refine ⟨315188289707475132739567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1681004211773200707944357 315188289707475132739567)
                      ·
                        rfl

theorem cell23_613827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_613827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613827 prefixEnd_613827 := by exact prefixLift 613827
  have htrace : WordTrace (prefixWord ++ tailWord_613827) baseStart_613827 baseEnd_613827 := by
    simpa [prefixWord, tailWord_613827, baseEnd_613827] using wordTrace_append hprefix tailTrace_613827
  have hstable : (prefixWord ++ tailWord_613827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613827).length < 2 ^ (prefixWord ++ tailWord_613827).sum := by decide
  have hdescent : baseEnd_613827 < baseStart_613827 := by decide
  rcases family_descends (prefixWord ++ tailWord_613827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613840 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_613840 : Nat := 118140960795 + 613840 * 2 ^ 59
def prefixEnd_613840 : Nat := 4983230072969 + 3 ^ 40 * 613840 * 2
def baseEnd_613840 : Nat := 315194964955983581877007

theorem tailTrace_613840 : CollatzResearch.WordTrace tailWord_613840 prefixEnd_613840 315194964955983581877007 := by
  unfold tailWord_613840
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194292048084995185363487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14925722730779993580484649 11194292048084995185363487)
  ·
    refine ⟨16791438072127492778045231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11194292048084995185363487 16791438072127492778045231)
    ·
      refine ⟨25187157108191239167067847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16791438072127492778045231 25187157108191239167067847)
      ·
        refine ⟨37780735662286858750601771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25187157108191239167067847 37780735662286858750601771)
        ·
          refine ⟨56671103493430288125902657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37780735662286858750601771 56671103493430288125902657)
          ·
            refine ⟨42503327620072716094426993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56671103493430288125902657 42503327620072716094426993)
            ·
              refine ⟨31877495715054537070820245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42503327620072716094426993 31877495715054537070820245)
              ·
                refine ⟨1494257611643181425194699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31877495715054537070820245 1494257611643181425194699)
                ·
                  refine ⟨2241386417464772137792049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494257611643181425194699 2241386417464772137792049)
                  ·
                    refine ⟨1681039813098579103344037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241386417464772137792049 1681039813098579103344037)
                    ·
                      refine ⟨315194964955983581877007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1681039813098579103344037 315194964955983581877007)
                      ·
                        rfl

theorem cell23_613840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_613840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613840 prefixEnd_613840 := by exact prefixLift 613840
  have htrace : WordTrace (prefixWord ++ tailWord_613840) baseStart_613840 baseEnd_613840 := by
    simpa [prefixWord, tailWord_613840, baseEnd_613840] using wordTrace_append hprefix tailTrace_613840
  have hstable : (prefixWord ++ tailWord_613840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613840).length < 2 ^ (prefixWord ++ tailWord_613840).sum := by decide
  have hdescent : baseEnd_613840 < baseStart_613840 := by decide
  rcases family_descends (prefixWord ++ tailWord_613840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613847 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_613847 : Nat := 118140960795 + 613847 * 2 ^ 59
def prefixEnd_613847 : Nat := 4983230072969 + 3 ^ 40 * 613847 * 2
def baseEnd_613847 : Nat := 315198559320565054489475

theorem tailTrace_613847 : CollatzResearch.WordTrace tailWord_613847 prefixEnd_613847 315198559320565054489475 := by
  unfold tailWord_613847
  simp only [CollatzResearch.WordTrace]
  refine ⟨22388839407144630566231795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14925892938096420377487863 22388839407144630566231795)
  ·
    refine ⟨33583259110716945849347693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22388839407144630566231795 33583259110716945849347693)
    ·
      refine ⟨12593722166518854693505385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33583259110716945849347693 12593722166518854693505385)
      ·
        refine ⟨9445291624889141020129039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12593722166518854693505385 9445291624889141020129039)
        ·
          refine ⟨14167937437333711530193559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9445291624889141020129039 14167937437333711530193559)
          ·
            refine ⟨21251906156000567295290339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14167937437333711530193559 21251906156000567295290339)
            ·
              refine ⟨31877859234000850942935509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21251906156000567295290339 31877859234000850942935509)
              ·
                refine ⟨747137325796894943975051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31877859234000850942935509 747137325796894943975051)
                ·
                  refine ⟨1120705988695342415962577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747137325796894943975051 1120705988695342415962577)
                  ·
                    refine ⟨840529491521506811971933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1120705988695342415962577 840529491521506811971933)
                    ·
                      refine ⟨315198559320565054489475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840529491521506811971933 315198559320565054489475)
                      ·
                        rfl

theorem cell23_613847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_613847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613847 prefixEnd_613847 := by exact prefixLift 613847
  have htrace : WordTrace (prefixWord ++ tailWord_613847) baseStart_613847 baseEnd_613847 := by
    simpa [prefixWord, tailWord_613847, baseEnd_613847] using wordTrace_append hprefix tailTrace_613847
  have hstable : (prefixWord ++ tailWord_613847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613847).length < 2 ^ (prefixWord ++ tailWord_613847).sum := by decide
  have hdescent : baseEnd_613847 < baseStart_613847 := by decide
  rcases family_descends (prefixWord ++ tailWord_613847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613874 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_613874 : Nat := 118140960795 + 613874 * 2 ^ 59
def prefixEnd_613874 : Nat := 4983230072969 + 3 ^ 40 * 613874 * 2
def baseEnd_613874 : Nat := 315212423298236448851851

theorem tailTrace_613874 : CollatzResearch.WordTrace tailWord_613874 prefixEnd_613874 315212423298236448851851 := by
  unfold tailWord_613874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597456044511703544366169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14926549452031209451643117 5597456044511703544366169)
  ·
    refine ⟨4198092033383777658274627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5597456044511703544366169 4198092033383777658274627)
    ·
      refine ⟨6297138050075666487411941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198092033383777658274627 6297138050075666487411941)
      ·
        refine ⟨1180713384389187466389739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6297138050075666487411941 1180713384389187466389739)
        ·
          refine ⟨1771070076583781199584609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180713384389187466389739 1771070076583781199584609)
          ·
            refine ⟨1328302557437835899688457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771070076583781199584609 1328302557437835899688457)
            ·
              refine ⟨996226918078376924766343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328302557437835899688457 996226918078376924766343)
              ·
                refine ⟨1494340377117565387149515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996226918078376924766343 1494340377117565387149515)
                ·
                  refine ⟨2241510565676348080724273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494340377117565387149515 2241510565676348080724273)
                  ·
                    refine ⟨1681132924257261060543205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2241510565676348080724273 1681132924257261060543205)
                    ·
                      refine ⟨315212423298236448851851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1681132924257261060543205 315212423298236448851851)
                      ·
                        rfl

theorem cell23_613874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_613874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613874 prefixEnd_613874 := by exact prefixLift 613874
  have htrace : WordTrace (prefixWord ++ tailWord_613874) baseStart_613874 baseEnd_613874 := by
    simpa [prefixWord, tailWord_613874, baseEnd_613874] using wordTrace_append hprefix tailTrace_613874
  have hstable : (prefixWord ++ tailWord_613874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613874).length < 2 ^ (prefixWord ++ tailWord_613874).sum := by decide
  have hdescent : baseEnd_613874 < baseStart_613874 := by decide
  rcases family_descends (prefixWord ++ tailWord_613874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613928 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_613928 : Nat := 118140960795 + 613928 * 2 ^ 59
def prefixEnd_613928 : Nat := 4983230072969 + 3 ^ 40 * 613928 * 2
def baseEnd_613928 : Nat := 315240151253579237576603

theorem tailTrace_613928 : CollatzResearch.WordTrace tailWord_613928 prefixEnd_613928 315240151253579237576603 := by
  unfold tailWord_613928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195896859925590699965219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14927862479900787599953625 11195896859925590699965219)
  ·
    refine ⟨16793845289888386049947829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11195896859925590699965219 16793845289888386049947829)
    ·
      refine ⟨1574422995927036192182609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16793845289888386049947829 1574422995927036192182609)
      ·
        refine ⟨1180817246945277144136957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1574422995927036192182609 1180817246945277144136957)
        ·
          refine ⟨442806467604478929051359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1180817246945277144136957 442806467604478929051359)
          ·
            refine ⟨664209701406718393577039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442806467604478929051359 664209701406718393577039)
            ·
              refine ⟨996314552110077590365559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664209701406718393577039 996314552110077590365559)
              ·
                refine ⟨1494471828165116385548339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996314552110077590365559 1494471828165116385548339)
                ·
                  refine ⟨2241707742247674578322509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494471828165116385548339 2241707742247674578322509)
                  ·
                    refine ⟨840640403342877966870941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241707742247674578322509 840640403342877966870941)
                    ·
                      refine ⟨315240151253579237576603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840640403342877966870941 315240151253579237576603)
                      ·
                        rfl

theorem cell23_613928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_613928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613928 prefixEnd_613928 := by exact prefixLift 613928
  have htrace : WordTrace (prefixWord ++ tailWord_613928) baseStart_613928 baseEnd_613928 := by
    simpa [prefixWord, tailWord_613928, baseEnd_613928] using wordTrace_append hprefix tailTrace_613928
  have hstable : (prefixWord ++ tailWord_613928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613928).length < 2 ^ (prefixWord ++ tailWord_613928).sum := by decide
  have hdescent : baseEnd_613928 < baseStart_613928 := by decide
  rcases family_descends (prefixWord ++ tailWord_613928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613960 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_613960 : Nat := 118140960795 + 613960 * 2 ^ 59
def prefixEnd_613960 : Nat := 4983230072969 + 3 ^ 40 * 613960 * 2
def baseEnd_613960 : Nat := 315256582634523112376455

theorem tailTrace_613960 : CollatzResearch.WordTrace tailWord_613960 prefixEnd_613960 315256582634523112376455 := by
  unfold tailWord_613960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196480427867625432547667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14928640570490167243396889 11196480427867625432547667)
  ·
    refine ⟨16794720641801438148821501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11196480427867625432547667 16794720641801438148821501)
    ·
      refine ⟨6298020240675539305808063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16794720641801438148821501 6298020240675539305808063)
      ·
        refine ⟨9447030361013308958712095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298020240675539305808063 9447030361013308958712095)
        ·
          refine ⟨14170545541519963438068143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9447030361013308958712095 14170545541519963438068143)
          ·
            refine ⟨21255818312279945157102215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14170545541519963438068143 21255818312279945157102215)
            ·
              refine ⟨31883727468419917735653323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21255818312279945157102215 31883727468419917735653323)
              ·
                refine ⟨47825591202629876603479985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31883727468419917735653323 47825591202629876603479985)
                ·
                  refine ⟨35869193401972407452609989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47825591202629876603479985 35869193401972407452609989)
                  ·
                    refine ⟨6725473762869826397364373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35869193401972407452609989 6725473762869826397364373)
                    ·
                      refine ⟨315256582634523112376455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6725473762869826397364373 315256582634523112376455)
                      ·
                        rfl

theorem cell23_613960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_613960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_613960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_613960 prefixEnd_613960 := by exact prefixLift 613960
  have htrace : WordTrace (prefixWord ++ tailWord_613960) baseStart_613960 baseEnd_613960 := by
    simpa [prefixWord, tailWord_613960, baseEnd_613960] using wordTrace_append hprefix tailTrace_613960
  have hstable : (prefixWord ++ tailWord_613960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613960).length < 2 ^ (prefixWord ++ tailWord_613960).sum := by decide
  have hdescent : baseEnd_613960 < baseStart_613960 := by decide
  rcases family_descends (prefixWord ++ tailWord_613960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614124 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_614124 : Nat := 118140960795 + 614124 * 2 ^ 59
def prefixEnd_614124 : Nat := 4983230072969 + 3 ^ 40 * 614124 * 2
def baseEnd_614124 : Nat := 105113597820620156908567

theorem tailTrace_614124 : CollatzResearch.WordTrace tailWord_614124 prefixEnd_614124 105113597820620156908567 := by
  unfold tailWord_614124
  simp only [CollatzResearch.WordTrace]
  refine ⟨11199471213570553437032713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14932628284760737916043617 11199471213570553437032713)
  ·
    refine ⟨8399603410177915077774535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11199471213570553437032713 8399603410177915077774535)
    ·
      refine ⟨12599405115266872616661803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399603410177915077774535 12599405115266872616661803)
      ·
        refine ⟨18899107672900308924992705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12599405115266872616661803 18899107672900308924992705)
        ·
          refine ⟨14174330754675231693744529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18899107672900308924992705 14174330754675231693744529)
          ·
            refine ⟨10630748066006423770308397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14174330754675231693744529 10630748066006423770308397)
            ·
              refine ⟨3986530524752408913865649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10630748066006423770308397 3986530524752408913865649)
              ·
                refine ⟨2989897893564306685399237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986530524752408913865649 2989897893564306685399237)
                ·
                  refine ⟨560605855043307503512357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2989897893564306685399237 560605855043307503512357)
                  ·
                    refine ⟨105113597820620156908567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560605855043307503512357 105113597820620156908567)
                    ·
                      rfl

theorem cell23_614124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_614124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614124 prefixEnd_614124 := by exact prefixLift 614124
  have htrace : WordTrace (prefixWord ++ tailWord_614124) baseStart_614124 baseEnd_614124 := by
    simpa [prefixWord, tailWord_614124, baseEnd_614124] using wordTrace_append hprefix tailTrace_614124
  have hstable : (prefixWord ++ tailWord_614124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614124).length < 2 ^ (prefixWord ++ tailWord_614124).sum := by decide
  have hdescent : baseEnd_614124 < baseStart_614124 := by decide
  rcases family_descends (prefixWord ++ tailWord_614124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614125 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_614125 : Nat := 118140960795 + 614125 * 2 ^ 59
def prefixEnd_614125 : Nat := 4983230072969 + 3 ^ 40 * 614125 * 2
def baseEnd_614125 : Nat := 315341306942514966813197

theorem tailTrace_614125 : CollatzResearch.WordTrace tailWord_614125 prefixEnd_614125 315341306942514966813197 := by
  unfold tailWord_614125
  simp only [CollatzResearch.WordTrace]
  refine ⟨22398978900137484044851829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14932652600091656029901219 22398978900137484044851829)
  ·
    refine ⟨2099904271887889129204859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22398978900137484044851829 2099904271887889129204859)
    ·
      refine ⟨3149856407831833693807289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099904271887889129204859 3149856407831833693807289)
      ·
        refine ⟨2362392305873875270355467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3149856407831833693807289 2362392305873875270355467)
        ·
          refine ⟨3543588458810812905533201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362392305873875270355467 3543588458810812905533201)
          ·
            refine ⟨2657691344108109679149901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3543588458810812905533201 2657691344108109679149901)
            ·
              refine ⟨996634254040541129681213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2657691344108109679149901 996634254040541129681213)
              ·
                refine ⟨373737845265202923630455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 996634254040541129681213 373737845265202923630455)
                ·
                  refine ⟨560606767897804385445683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373737845265202923630455 560606767897804385445683)
                  ·
                    refine ⟨840910151846706578168525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560606767897804385445683 840910151846706578168525)
                    ·
                      refine ⟨315341306942514966813197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840910151846706578168525 315341306942514966813197)
                      ·
                        rfl

theorem cell23_614125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_614125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614125 prefixEnd_614125 := by exact prefixLift 614125
  have htrace : WordTrace (prefixWord ++ tailWord_614125) baseStart_614125 baseEnd_614125 := by
    simpa [prefixWord, tailWord_614125, baseEnd_614125] using wordTrace_append hprefix tailTrace_614125
  have hstable : (prefixWord ++ tailWord_614125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614125).length < 2 ^ (prefixWord ++ tailWord_614125).sum := by decide
  have hdescent : baseEnd_614125 < baseStart_614125 := by decide
  rcases family_descends (prefixWord ++ tailWord_614125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614131 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 5, 2, 2]
def baseStart_614131 : Nat := 118140960795 + 614131 * 2 ^ 59
def prefixEnd_614131 : Nat := 4983230072969 + 3 ^ 40 * 614131 * 2
def baseEnd_614131 : Nat := 315344387826441943338169

theorem tailTrace_614131 : CollatzResearch.WordTrace tailWord_614131 prefixEnd_614131 315344387826441943338169 := by
  unfold tailWord_614131
  simp only [CollatzResearch.WordTrace]
  refine ⟨22399197738115747069570247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14932798492077164713046831 22399197738115747069570247)
  ·
    refine ⟨33598796607173620604355371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22399197738115747069570247 33598796607173620604355371)
    ·
      refine ⟨50398194910760430906533057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33598796607173620604355371 50398194910760430906533057)
      ·
        refine ⟨37798646183070323179899793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50398194910760430906533057 37798646183070323179899793)
        ·
          refine ⟨28348984637302742384924845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37798646183070323179899793 28348984637302742384924845)
          ·
            refine ⟨10630869238988528394346817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28348984637302742384924845 10630869238988528394346817)
            ·
              refine ⟨7973151929241396295760113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10630869238988528394346817 7973151929241396295760113)
              ·
                refine ⟨5979863946931047221820085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7973151929241396295760113 5979863946931047221820085)
                ·
                  refine ⟨560612245024785677045633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5979863946931047221820085 560612245024785677045633)
                  ·
                    refine ⟨420459183768589257784225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 560612245024785677045633 420459183768589257784225)
                    ·
                      refine ⟨315344387826441943338169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420459183768589257784225 315344387826441943338169)
                      ·
                        rfl

theorem cell23_614131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 2, 2].length) (baseStart_614131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614131 prefixEnd_614131 := by exact prefixLift 614131
  have htrace : WordTrace (prefixWord ++ tailWord_614131) baseStart_614131 baseEnd_614131 := by
    simpa [prefixWord, tailWord_614131, baseEnd_614131] using wordTrace_append hprefix tailTrace_614131
  have hstable : (prefixWord ++ tailWord_614131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614131).length < 2 ^ (prefixWord ++ tailWord_614131).sum := by decide
  have hdescent : baseEnd_614131 < baseStart_614131 := by decide
  rcases family_descends (prefixWord ++ tailWord_614131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614142 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_614142 : Nat := 118140960795 + 614142 * 2 ^ 59
def prefixEnd_614142 : Nat := 4983230072969 + 3 ^ 40 * 614142 * 2
def baseEnd_614142 : Nat := 315350036113641400300619

theorem tailTrace_614142 : CollatzResearch.WordTrace tailWord_614142 prefixEnd_614142 315350036113641400300619 := by
  unfold tailWord_614142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799949867634486993527585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14933065960717263965480453 2799949867634486993527585)
  ·
    refine ⟨2099962400725865245145689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2799949867634486993527585 2099962400725865245145689)
    ·
      refine ⟨1574971800544398933859267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2099962400725865245145689 1574971800544398933859267)
      ·
        refine ⟨2362457700816598400788901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574971800544398933859267 2362457700816598400788901)
        ·
          refine ⟨442960818903112200147919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2362457700816598400788901 442960818903112200147919)
          ·
            refine ⟨664441228354668300221879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442960818903112200147919 664441228354668300221879)
            ·
              refine ⟨996661842532002450332819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664441228354668300221879 996661842532002450332819)
              ·
                refine ⟨1494992763798003675499229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996661842532002450332819 1494992763798003675499229)
                ·
                  refine ⟨560622286424251378312211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1494992763798003675499229 560622286424251378312211)
                  ·
                    refine ⟨840933429636377067468317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560622286424251378312211 840933429636377067468317)
                    ·
                      refine ⟨315350036113641400300619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840933429636377067468317 315350036113641400300619)
                      ·
                        rfl

theorem cell23_614142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_614142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614142 prefixEnd_614142 := by exact prefixLift 614142
  have htrace : WordTrace (prefixWord ++ tailWord_614142) baseStart_614142 baseEnd_614142 := by
    simpa [prefixWord, tailWord_614142, baseEnd_614142] using wordTrace_append hprefix tailTrace_614142
  have hstable : (prefixWord ++ tailWord_614142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614142).length < 2 ^ (prefixWord ++ tailWord_614142).sum := by decide
  have hdescent : baseEnd_614142 < baseStart_614142 := by decide
  rcases family_descends (prefixWord ++ tailWord_614142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614154 : List Nat := [3, 1, 2, 2, 1, 4, 2, 8]
def baseStart_614154 : Nat := 118140960795 + 614154 * 2 ^ 59
def prefixEnd_614154 : Nat := 4983230072969 + 3 ^ 40 * 614154 * 2
def baseEnd_614154 : Nat := 11679859180796124198169

theorem tailTrace_614154 : CollatzResearch.WordTrace tailWord_614154 prefixEnd_614154 11679859180796124198169 := by
  unfold tailWord_614154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600009154258105499414379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14933357744688281331771677 5600009154258105499414379)
  ·
    refine ⟨8400013731387158249121569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600009154258105499414379 8400013731387158249121569)
    ·
      refine ⟨6300010298540368686841177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400013731387158249121569 6300010298540368686841177)
      ·
        refine ⟨4725007723905276515130883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300010298540368686841177 4725007723905276515130883)
        ·
          refine ⟨7087511585857914772696325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725007723905276515130883 7087511585857914772696325)
          ·
            refine ⟨1328908422348359019880561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7087511585857914772696325 1328908422348359019880561)
            ·
              refine ⟨996681316761269264910421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328908422348359019880561 996681316761269264910421)
              ·
                refine ⟨11679859180796124198169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 996681316761269264910421 11679859180796124198169)
                ·
                  rfl

theorem cell23_614154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_614154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614154 prefixEnd_614154 := by exact prefixLift 614154
  have htrace : WordTrace (prefixWord ++ tailWord_614154) baseStart_614154 baseEnd_614154 := by
    simpa [prefixWord, tailWord_614154, baseEnd_614154] using wordTrace_append hprefix tailTrace_614154
  have hstable : (prefixWord ++ tailWord_614154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614154).length < 2 ^ (prefixWord ++ tailWord_614154).sum := by decide
  have hdescent : baseEnd_614154 < baseStart_614154 := by decide
  rcases family_descends (prefixWord ++ tailWord_614154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614158 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_614158 : Nat := 118140960795 + 614158 * 2 ^ 59
def prefixEnd_614158 : Nat := 4983230072969 + 3 ^ 40 * 614158 * 2
def baseEnd_614158 : Nat := 105119417268037779233515

theorem tailTrace_614158 : CollatzResearch.WordTrace tailWord_614158 prefixEnd_614158 105119417268037779233515 := by
  unfold tailWord_614158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800022813627241335100391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14933455006011953787202085 2800022813627241335100391)
  ·
    refine ⟨4200034220440862002650587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800022813627241335100391 4200034220440862002650587)
    ·
      refine ⟨6300051330661293003975881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200034220440862002650587 6300051330661293003975881)
      ·
        refine ⟨4725038497995969752981911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300051330661293003975881 4725038497995969752981911)
        ·
          refine ⟨7087557746993954629472867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725038497995969752981911 7087557746993954629472867)
          ·
            refine ⟨10631336620490931944209301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087557746993954629472867 10631336620490931944209301)
            ·
              refine ⟨498343904085512434884811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10631336620490931944209301 498343904085512434884811)
              ·
                refine ⟨747515856128268652327217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498343904085512434884811 747515856128268652327217)
                ·
                  refine ⟨560636892096201489245413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747515856128268652327217 560636892096201489245413)
                  ·
                    refine ⟨105119417268037779233515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560636892096201489245413 105119417268037779233515)
                    ·
                      rfl

theorem cell23_614158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_614158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614158 prefixEnd_614158 := by exact prefixLift 614158
  have htrace : WordTrace (prefixWord ++ tailWord_614158) baseStart_614158 baseEnd_614158 := by
    simpa [prefixWord, tailWord_614158, baseEnd_614158] using wordTrace_append hprefix tailTrace_614158
  have hstable : (prefixWord ++ tailWord_614158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614158).length < 2 ^ (prefixWord ++ tailWord_614158).sum := by decide
  have hdescent : baseEnd_614158 < baseStart_614158 := by decide
  rcases family_descends (prefixWord ++ tailWord_614158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614181 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_614181 : Nat := 118140960795 + 614181 * 2 ^ 59
def prefixEnd_614181 : Nat := 4983230072969 + 3 ^ 40 * 614181 * 2
def baseEnd_614181 : Nat := 315370061859166747712939

theorem tailTrace_614181 : CollatzResearch.WordTrace tailWord_614181 prefixEnd_614181 315370061859166747712939 := by
  unfold tailWord_614181
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401021387934605608890397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14934014258623070405926931 22401021387934605608890397)
  ·
    refine ⟨8400383020475477103333899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22401021387934605608890397 8400383020475477103333899)
    ·
      refine ⟨12600574530713215655000849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400383020475477103333899 12600574530713215655000849)
      ·
        refine ⟨9450430898034911741250637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12600574530713215655000849 9450430898034911741250637)
        ·
          refine ⟨3543911586763091902968989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9450430898034911741250637 3543911586763091902968989)
          ·
            refine ⟨1328966845036159463613371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3543911586763091902968989 1328966845036159463613371)
            ·
              refine ⟨1993450267554239195420057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328966845036159463613371 1993450267554239195420057)
              ·
                refine ⟨1495087700665679396565043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993450267554239195420057 1495087700665679396565043)
                ·
                  refine ⟨2242631550998519094847565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495087700665679396565043 2242631550998519094847565)
                  ·
                    refine ⟨840986831624444660567837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242631550998519094847565 840986831624444660567837)
                    ·
                      refine ⟨315370061859166747712939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 840986831624444660567837 315370061859166747712939)
                      ·
                        rfl

theorem cell23_614181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_614181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614181 prefixEnd_614181 := by exact prefixLift 614181
  have htrace : WordTrace (prefixWord ++ tailWord_614181) baseStart_614181 baseEnd_614181 := by
    simpa [prefixWord, tailWord_614181, baseEnd_614181] using wordTrace_append hprefix tailTrace_614181
  have hstable : (prefixWord ++ tailWord_614181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614181).length < 2 ^ (prefixWord ++ tailWord_614181).sum := by decide
  have hdescent : baseEnd_614181 < baseStart_614181 := by decide
  rcases family_descends (prefixWord ++ tailWord_614181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614204 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_614204 : Nat := 118140960795 + 614204 * 2 ^ 59
def prefixEnd_614204 : Nat := 4983230072969 + 3 ^ 40 * 614204 * 2
def baseEnd_614204 : Nat := 315381871914220157725333

theorem tailTrace_614204 : CollatzResearch.WordTrace tailWord_614204 prefixEnd_614204 315381871914220157725333 := by
  unfold tailWord_614204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200930133425640268488833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14934573511234187024651777 11200930133425640268488833)
  ·
    refine ⟨8400697600069230201366625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11200930133425640268488833 8400697600069230201366625)
    ·
      refine ⟨6300523200051922651024969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400697600069230201366625 6300523200051922651024969)
      ·
        refine ⟨4725392400038941988268727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300523200051922651024969 4725392400038941988268727)
        ·
          refine ⟨7088088600058412982403091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725392400038941988268727 7088088600058412982403091)
          ·
            refine ⟨10632132900087619473604637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088088600058412982403091 10632132900087619473604637)
            ·
              refine ⟨3987049837532857302601739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10632132900087619473604637 3987049837532857302601739)
              ·
                refine ⟨5980574756299285953902609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987049837532857302601739 5980574756299285953902609)
                ·
                  refine ⟨4485431067224464465426957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5980574756299285953902609 4485431067224464465426957)
                  ·
                    refine ⟨1682036650209174174535109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4485431067224464465426957 1682036650209174174535109)
                    ·
                      refine ⟨315381871914220157725333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1682036650209174174535109 315381871914220157725333)
                      ·
                        rfl

theorem cell23_614204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_614204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614204 prefixEnd_614204 := by exact prefixLift 614204
  have htrace : WordTrace (prefixWord ++ tailWord_614204) baseStart_614204 baseEnd_614204 := by
    simpa [prefixWord, tailWord_614204, baseEnd_614204] using wordTrace_append hprefix tailTrace_614204
  have hstable : (prefixWord ++ tailWord_614204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614204).length < 2 ^ (prefixWord ++ tailWord_614204).sum := by decide
  have hdescent : baseEnd_614204 < baseStart_614204 := by decide
  rcases family_descends (prefixWord ++ tailWord_614204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614224 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_614224 : Nat := 118140960795 + 614224 * 2 ^ 59
def prefixEnd_614224 : Nat := 4983230072969 + 3 ^ 40 * 614224 * 2
def baseEnd_614224 : Nat := 315392141527310079475241

theorem tailTrace_614224 : CollatzResearch.WordTrace tailWord_614224 prefixEnd_614224 315392141527310079475241 := by
  unfold tailWord_614224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201294863389411976352863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14935059817852549301803817 11201294863389411976352863)
  ·
    refine ⟨16801942295084117964529295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201294863389411976352863 16801942295084117964529295)
    ·
      refine ⟨25202913442626176946793943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16801942295084117964529295 25202913442626176946793943)
      ·
        refine ⟨37804370163939265420190915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25202913442626176946793943 37804370163939265420190915)
        ·
          refine ⟨56706555245908898130286373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37804370163939265420190915 56706555245908898130286373)
          ·
            refine ⟨10632479108607918399428695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56706555245908898130286373 10632479108607918399428695)
            ·
              refine ⟨15948718662911877599143043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10632479108607918399428695 15948718662911877599143043)
              ·
                refine ⟨23923077994367816398714565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15948718662911877599143043 23923077994367816398714565)
                ·
                  refine ⟨4485577123943965574758981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23923077994367816398714565 4485577123943965574758981)
                  ·
                    refine ⟨841045710739493545267309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485577123943965574758981 841045710739493545267309)
                    ·
                      refine ⟨315392141527310079475241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841045710739493545267309 315392141527310079475241)
                      ·
                        rfl

theorem cell23_614224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_614224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614224 prefixEnd_614224 := by exact prefixLift 614224
  have htrace : WordTrace (prefixWord ++ tailWord_614224) baseStart_614224 baseEnd_614224 := by
    simpa [prefixWord, tailWord_614224, baseEnd_614224] using wordTrace_append hprefix tailTrace_614224
  have hstable : (prefixWord ++ tailWord_614224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614224).length < 2 ^ (prefixWord ++ tailWord_614224).sum := by decide
  have hdescent : baseEnd_614224 < baseStart_614224 := by decide
  rcases family_descends (prefixWord ++ tailWord_614224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614234 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_614234 : Nat := 118140960795 + 614234 * 2 ^ 59
def prefixEnd_614234 : Nat := 4983230072969 + 3 ^ 40 * 614234 * 2
def baseEnd_614234 : Nat := 315397276333855040350195

theorem tailTrace_614234 : CollatzResearch.WordTrace tailWord_614234 prefixEnd_614234 315397276333855040350195 := by
  unfold tailWord_614234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600738614185648915142439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14935302971161730440379837 5600738614185648915142439)
  ·
    refine ⟨8401107921278473372713659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600738614185648915142439 8401107921278473372713659)
    ·
      refine ⟨12601661881917710059070489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8401107921278473372713659 12601661881917710059070489)
      ·
        refine ⟨9451246411438282544302867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12601661881917710059070489 9451246411438282544302867)
        ·
          refine ⟨14176869617157423816454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451246411438282544302867 14176869617157423816454301)
          ·
            refine ⟨5316326106434033931170363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14176869617157423816454301 5316326106434033931170363)
            ·
              refine ⟨7974489159651050896755545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316326106434033931170363 7974489159651050896755545)
              ·
                refine ⟨5980866869738288172566659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7974489159651050896755545 5980866869738288172566659)
                ·
                  refine ⟨8971300304607432258849989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5980866869738288172566659 8971300304607432258849989)
                  ·
                    refine ⟨1682118807113893548534373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8971300304607432258849989 1682118807113893548534373)
                    ·
                      refine ⟨315397276333855040350195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1682118807113893548534373 315397276333855040350195)
                      ·
                        rfl

theorem cell23_614234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_614234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614234 prefixEnd_614234 := by exact prefixLift 614234
  have htrace : WordTrace (prefixWord ++ tailWord_614234) baseStart_614234 baseEnd_614234 := by
    simpa [prefixWord, tailWord_614234, baseEnd_614234] using wordTrace_append hprefix tailTrace_614234
  have hstable : (prefixWord ++ tailWord_614234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614234).length < 2 ^ (prefixWord ++ tailWord_614234).sum := by decide
  have hdescent : baseEnd_614234 < baseStart_614234 := by decide
  rcases family_descends (prefixWord ++ tailWord_614234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614242 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_614242 : Nat := 118140960795 + 614242 * 2 ^ 59
def prefixEnd_614242 : Nat := 4983230072969 + 3 ^ 40 * 614242 * 2
def baseEnd_614242 : Nat := 315401384179091009050159

theorem tailTrace_614242 : CollatzResearch.WordTrace tailWord_614242 prefixEnd_614242 315401384179091009050159 := by
  unfold tailWord_614242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600811560178403256715245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14935497493809075351240653 5600811560178403256715245)
  ·
    refine ⟨2100304335066901221268217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5600811560178403256715245 2100304335066901221268217)
    ·
      refine ⟨1575228251300175915951163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2100304335066901221268217 1575228251300175915951163)
      ·
        refine ⟨2362842376950263873926745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575228251300175915951163 2362842376950263873926745)
        ·
          refine ⟨1772131782712697905445059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2362842376950263873926745 1772131782712697905445059)
          ·
            refine ⟨2658197674069046858167589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772131782712697905445059 2658197674069046858167589)
            ·
              refine ⟨498412063887946285906423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2658197674069046858167589 498412063887946285906423)
              ·
                refine ⟨747618095831919428859635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498412063887946285906423 747618095831919428859635)
                ·
                  refine ⟨1121427143747879143289453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747618095831919428859635 1121427143747879143289453)
                  ·
                    refine ⟨420535178905454678733545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121427143747879143289453 420535178905454678733545)
                    ·
                      refine ⟨315401384179091009050159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420535178905454678733545 315401384179091009050159)
                      ·
                        rfl

theorem cell23_614242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_614242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614242 prefixEnd_614242 := by exact prefixLift 614242
  have htrace : WordTrace (prefixWord ++ tailWord_614242) baseStart_614242 baseEnd_614242 := by
    simpa [prefixWord, tailWord_614242, baseEnd_614242] using wordTrace_append hprefix tailTrace_614242
  have hstable : (prefixWord ++ tailWord_614242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614242).length < 2 ^ (prefixWord ++ tailWord_614242).sum := by decide
  have hdescent : baseEnd_614242 < baseStart_614242 := by decide
  rcases family_descends (prefixWord ++ tailWord_614242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614261 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 7]
def baseStart_614261 : Nat := 118140960795 + 614261 * 2 ^ 59
def prefixEnd_614261 : Nat := 4983230072969 + 3 ^ 40 * 614261 * 2
def baseEnd_614261 : Nat := 35045682256836270523619

theorem tailTrace_614261 : CollatzResearch.WordTrace tailWord_614261 prefixEnd_614261 35045682256836270523619 := by
  unfold tailWord_614261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22403939227644779271802637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14935959485096519514535091 22403939227644779271802637)
  ·
    refine ⟨8401477210366792226925989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22403939227644779271802637 8401477210366792226925989)
    ·
      refine ⟨1575276976943773542548623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8401477210366792226925989 1575276976943773542548623)
      ·
        refine ⟨2362915465415660313822935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575276976943773542548623 2362915465415660313822935)
        ·
          refine ⟨3544373198123490470734403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362915465415660313822935 3544373198123490470734403)
          ·
            refine ⟨5316559797185235706101605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544373198123490470734403 5316559797185235706101605)
            ·
              refine ⟨996854961972231694894051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5316559797185235706101605 996854961972231694894051)
              ·
                refine ⟨1495282442958347542341077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996854961972231694894051 1495282442958347542341077)
                ·
                  refine ⟨35045682256836270523619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1495282442958347542341077 35045682256836270523619)
                  ·
                    rfl

theorem cell23_614261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_614261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614261 prefixEnd_614261 := by exact prefixLift 614261
  have htrace : WordTrace (prefixWord ++ tailWord_614261) baseStart_614261 baseEnd_614261 := by
    simpa [prefixWord, tailWord_614261, baseEnd_614261] using wordTrace_append hprefix tailTrace_614261
  have hstable : (prefixWord ++ tailWord_614261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614261).length < 2 ^ (prefixWord ++ tailWord_614261).sum := by decide
  have hdescent : baseEnd_614261 < baseStart_614261 := by decide
  rcases family_descends (prefixWord ++ tailWord_614261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614284 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_614284 : Nat := 118140960795 + 614284 * 2 ^ 59
def prefixEnd_614284 : Nat := 4983230072969 + 3 ^ 40 * 614284 * 2
def baseEnd_614284 : Nat := 315422950366579844724965

theorem tailTrace_614284 : CollatzResearch.WordTrace tailWord_614284 prefixEnd_614284 315422950366579844724965 := by
  unfold tailWord_614284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202389053280727099944953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14936518737707636133259937 11202389053280727099944953)
  ·
    refine ⟨8401791789960545324958715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11202389053280727099944953 8401791789960545324958715)
    ·
      refine ⟨12602687684940817987438073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8401791789960545324958715 12602687684940817987438073)
      ·
        refine ⟨9452015763705613490578555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12602687684940817987438073 9452015763705613490578555)
        ·
          refine ⟨14178023645558420235867833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9452015763705613490578555 14178023645558420235867833)
          ·
            refine ⟨10633517734168815176900875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14178023645558420235867833 10633517734168815176900875)
            ·
              refine ⟨15950276601253222765351313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10633517734168815176900875 15950276601253222765351313)
              ·
                refine ⟨11962707450939917074013485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15950276601253222765351313 11962707450939917074013485)
                ·
                  refine ⟨4486015294102468902755057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11962707450939917074013485 4486015294102468902755057)
                  ·
                    refine ⟨3364511470576851677066293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4486015294102468902755057 3364511470576851677066293)
                    ·
                      refine ⟨315422950366579844724965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3364511470576851677066293 315422950366579844724965)
                      ·
                        rfl

theorem cell23_614284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_614284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614284 prefixEnd_614284 := by exact prefixLift 614284
  have htrace : WordTrace (prefixWord ++ tailWord_614284) baseStart_614284 baseEnd_614284 := by
    simpa [prefixWord, tailWord_614284, baseEnd_614284] using wordTrace_append hprefix tailTrace_614284
  have hstable : (prefixWord ++ tailWord_614284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614284).length < 2 ^ (prefixWord ++ tailWord_614284).sum := by decide
  have hdescent : baseEnd_614284 < baseStart_614284 := by decide
  rcases family_descends (prefixWord ++ tailWord_614284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614312 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 7]
def baseStart_614312 : Nat := 118140960795 + 614312 * 2 ^ 59
def prefixEnd_614312 : Nat := 4983230072969 + 3 ^ 40 * 614312 * 2
def baseEnd_614312 : Nat := 35048591980545081686093

theorem tailTrace_614312 : CollatzResearch.WordTrace tailWord_614312 prefixEnd_614312 35048591980545081686093 := by
  unfold tailWord_614312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202899675230007490954595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14937199566973343321272793 11202899675230007490954595)
  ·
    refine ⟨16804349512845011236431893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202899675230007490954595 16804349512845011236431893)
    ·
      refine ⟨787703883414609901707745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16804349512845011236431893 787703883414609901707745)
      ·
        refine ⟨590777912560957426280809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787703883414609901707745 590777912560957426280809)
        ·
          refine ⟨443083434420718069710607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590777912560957426280809 443083434420718069710607)
          ·
            refine ⟨664625151631077104565911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443083434420718069710607 664625151631077104565911)
            ·
              refine ⟨996937727446615656848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664625151631077104565911 996937727446615656848867)
              ·
                refine ⟨1495406591169923485273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996937727446615656848867 1495406591169923485273301)
                ·
                  refine ⟨35048591980545081686093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1495406591169923485273301 35048591980545081686093)
                  ·
                    rfl

theorem cell23_614312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_614312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614312 prefixEnd_614312 := by exact prefixLift 614312
  have htrace : WordTrace (prefixWord ++ tailWord_614312) baseStart_614312 baseEnd_614312 := by
    simpa [prefixWord, tailWord_614312, baseEnd_614312] using wordTrace_append hprefix tailTrace_614312
  have hstable : (prefixWord ++ tailWord_614312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614312).length < 2 ^ (prefixWord ++ tailWord_614312).sum := by decide
  have hdescent : baseEnd_614312 < baseStart_614312 := by decide
  rcases family_descends (prefixWord ++ tailWord_614312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614348 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_614348 : Nat := 118140960795 + 614348 * 2 ^ 59
def prefixEnd_614348 : Nat := 4983230072969 + 3 ^ 40 * 614348 * 2
def baseEnd_614348 : Nat := 315455813128467594324671

theorem tailTrace_614348 : CollatzResearch.WordTrace tailWord_614348 prefixEnd_614348 315455813128467594324671 := by
  unfold tailWord_614348
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203556189164796565109849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14938074918886395420146465 11203556189164796565109849)
  ·
    refine ⟨8402667141873597423832387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11203556189164796565109849 8402667141873597423832387)
    ·
      refine ⟨12604000712810396135748581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8402667141873597423832387 12604000712810396135748581)
      ·
        refine ⟨2363250133651949275452859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12604000712810396135748581 2363250133651949275452859)
        ·
          refine ⟨3544875200477923913179289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363250133651949275452859 3544875200477923913179289)
          ·
            refine ⟨2658656400358442934884467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544875200477923913179289 2658656400358442934884467)
            ·
              refine ⟨3987984600537664402326701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658656400358442934884467 3987984600537664402326701)
              ·
                refine ⟨1495494225201624150872513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987984600537664402326701 1495494225201624150872513)
                ·
                  refine ⟨1121620668901218113154385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1495494225201624150872513 1121620668901218113154385)
                  ·
                    refine ⟨841215501675913584865789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1121620668901218113154385 841215501675913584865789)
                    ·
                      refine ⟨315455813128467594324671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841215501675913584865789 315455813128467594324671)
                      ·
                        rfl

theorem cell23_614348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_614348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614348 prefixEnd_614348 := by exact prefixLift 614348
  have htrace : WordTrace (prefixWord ++ tailWord_614348) baseStart_614348 baseEnd_614348 := by
    simpa [prefixWord, tailWord_614348, baseEnd_614348] using wordTrace_append hprefix tailTrace_614348
  have hstable : (prefixWord ++ tailWord_614348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614348).length < 2 ^ (prefixWord ++ tailWord_614348).sum := by decide
  have hdescent : baseEnd_614348 < baseStart_614348 := by decide
  rcases family_descends (prefixWord ++ tailWord_614348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614405 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_614405 : Nat := 118140960795 + 614405 * 2 ^ 59
def prefixEnd_614405 : Nat := 4983230072969 + 3 ^ 40 * 614405 * 2
def baseEnd_614405 : Nat := 315485081525773871311909

theorem tailTrace_614405 : CollatzResearch.WordTrace tailWord_614405 prefixEnd_614405 315485081525773871311909 := by
  unfold tailWord_614405
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409191339123091865044669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14939460892748727910029779 22409191339123091865044669)
  ·
    refine ⟨8403446752171159449391751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22409191339123091865044669 8403446752171159449391751)
    ·
      refine ⟨12605170128256739174087627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403446752171159449391751 12605170128256739174087627)
      ·
        refine ⟨18907755192385108761131441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12605170128256739174087627 18907755192385108761131441)
        ·
          refine ⟨14180816394288831570848581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18907755192385108761131441 14180816394288831570848581)
          ·
            refine ⟨2658903073929155919534109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14180816394288831570848581 2658903073929155919534109)
            ·
              refine ⟨997088652723433469825291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658903073929155919534109 997088652723433469825291)
              ·
                refine ⟨1495632979085150204737937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997088652723433469825291 1495632979085150204737937)
                ·
                  refine ⟨1121724734313862653553453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1495632979085150204737937 1121724734313862653553453)
                  ·
                    refine ⟨420646775367698495082545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121724734313862653553453 420646775367698495082545)
                    ·
                      refine ⟨315485081525773871311909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420646775367698495082545 315485081525773871311909)
                      ·
                        rfl

theorem cell23_614405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_614405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614405 prefixEnd_614405 := by exact prefixLift 614405
  have htrace : WordTrace (prefixWord ++ tailWord_614405) baseStart_614405 baseEnd_614405 := by
    simpa [prefixWord, tailWord_614405, baseEnd_614405] using wordTrace_append hprefix tailTrace_614405
  have hstable : (prefixWord ++ tailWord_614405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614405).length < 2 ^ (prefixWord ++ tailWord_614405).sum := by decide
  have hdescent : baseEnd_614405 < baseStart_614405 := by decide
  rcases family_descends (prefixWord ++ tailWord_614405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614411 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 6]
def baseStart_614411 : Nat := 118140960795 + 614411 * 2 ^ 59
def prefixEnd_614411 : Nat := 4983230072969 + 3 ^ 40 * 614411 * 2
def baseEnd_614411 : Nat := 105162720803233615945627

theorem tailTrace_614411 : CollatzResearch.WordTrace tailWord_614411 prefixEnd_614411 105162720803233615945627 := by
  unfold tailWord_614411
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409410177101354889763087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14939606784734236593175391 22409410177101354889763087)
  ·
    refine ⟨33614115265652032334644631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22409410177101354889763087 33614115265652032334644631)
    ·
      refine ⟨50421172898478048501966947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33614115265652032334644631 50421172898478048501966947)
      ·
        refine ⟨75631759347717072752950421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50421172898478048501966947 75631759347717072752950421)
        ·
          refine ⟨3545238719424237785294551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75631759347717072752950421 3545238719424237785294551)
          ·
            refine ⟨5317858079136356677941827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545238719424237785294551 5317858079136356677941827)
            ·
              refine ⟨7976787118704535016912741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317858079136356677941827 7976787118704535016912741)
              ·
                refine ⟨1495647584757100315671139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7976787118704535016912741 1495647584757100315671139)
                ·
                  refine ⟨2243471377135650473506709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495647584757100315671139 2243471377135650473506709)
                  ·
                    refine ⟨105162720803233615945627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2243471377135650473506709 105162720803233615945627)
                    ·
                      rfl

theorem cell23_614411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_614411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614411 prefixEnd_614411 := by exact prefixLift 614411
  have htrace : WordTrace (prefixWord ++ tailWord_614411) baseStart_614411 baseEnd_614411 := by
    simpa [prefixWord, tailWord_614411, baseEnd_614411] using wordTrace_append hprefix tailTrace_614411
  have hstable : (prefixWord ++ tailWord_614411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614411).length < 2 ^ (prefixWord ++ tailWord_614411).sum := by decide
  have hdescent : baseEnd_614411 < baseStart_614411 := by decide
  rcases family_descends (prefixWord ++ tailWord_614411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614412 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_614412 : Nat := 118140960795 + 614412 * 2 ^ 59
def prefixEnd_614412 : Nat := 4983230072969 + 3 ^ 40 * 614412 * 2
def baseEnd_614412 : Nat := 315488675890355343924377

theorem tailTrace_614412 : CollatzResearch.WordTrace tailWord_614412 prefixEnd_614412 315488675890355343924377 := by
  unfold tailWord_614412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204723325048866030274745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14939631100065154707032993 11204723325048866030274745)
  ·
    refine ⟨8403542493786649522706059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11204723325048866030274745 8403542493786649522706059)
    ·
      refine ⟨12605313740679974284059089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403542493786649522706059 12605313740679974284059089)
      ·
        refine ⟨9453985305509980713044317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12605313740679974284059089 9453985305509980713044317)
        ·
          refine ⟨3545244489566242767391619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9453985305509980713044317 3545244489566242767391619)
          ·
            refine ⟨5317866734349364151087429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545244489566242767391619 5317866734349364151087429)
            ·
              refine ⟨997100012690505778328893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5317866734349364151087429 997100012690505778328893)
              ·
                refine ⟨373912504758939666873335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997100012690505778328893 373912504758939666873335)
                ·
                  refine ⟨560868757138409500310003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373912504758939666873335 560868757138409500310003)
                  ·
                    refine ⟨841303135707614250465005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560868757138409500310003 841303135707614250465005)
                    ·
                      refine ⟨315488675890355343924377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841303135707614250465005 315488675890355343924377)
                      ·
                        rfl

theorem cell23_614412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_614412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614412 prefixEnd_614412 := by exact prefixLift 614412
  have htrace : WordTrace (prefixWord ++ tailWord_614412) baseStart_614412 baseEnd_614412 := by
    simpa [prefixWord, tailWord_614412, baseEnd_614412] using wordTrace_append hprefix tailTrace_614412
  have hstable : (prefixWord ++ tailWord_614412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614412).length < 2 ^ (prefixWord ++ tailWord_614412).sum := by decide
  have hdescent : baseEnd_614412 < baseStart_614412 := by decide
  rcases family_descends (prefixWord ++ tailWord_614412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614431 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_614431 : Nat := 118140960795 + 614431 * 2 ^ 59
def prefixEnd_614431 : Nat := 4983230072969 + 3 ^ 40 * 614431 * 2
def baseEnd_614431 : Nat := 315498432022790769586789

theorem tailTrace_614431 : CollatzResearch.WordTrace tailWord_614431 prefixEnd_614431 315498432022790769586789 := by
  unfold tailWord_614431
  simp only [CollatzResearch.WordTrace]
  refine ⟨22410139637028898305491147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14940093091352598870327431 22410139637028898305491147)
  ·
    refine ⟨33615209455543347458236721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22410139637028898305491147 33615209455543347458236721)
    ·
      refine ⟨25211407091657510593677541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33615209455543347458236721 25211407091657510593677541)
      ·
        refine ⟨4727138829685783236314539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25211407091657510593677541 4727138829685783236314539)
        ·
          refine ⟨7090708244528674854471809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727138829685783236314539 7090708244528674854471809)
          ·
            refine ⟨5318031183396506140853857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7090708244528674854471809 5318031183396506140853857)
            ·
              refine ⟨3988523387547379605640393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318031183396506140853857 3988523387547379605640393)
              ·
                refine ⟨2991392540660534704230295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3988523387547379605640393 2991392540660534704230295)
                ·
                  refine ⟨4487088810990802056345443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991392540660534704230295 4487088810990802056345443)
                  ·
                    refine ⟨6730633216486203084518165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4487088810990802056345443 6730633216486203084518165)
                    ·
                      refine ⟨315498432022790769586789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6730633216486203084518165 315498432022790769586789)
                      ·
                        rfl

theorem cell23_614431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_614431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614431 prefixEnd_614431 := by exact prefixLift 614431
  have htrace : WordTrace (prefixWord ++ tailWord_614431) baseStart_614431 baseEnd_614431 := by
    simpa [prefixWord, tailWord_614431, baseEnd_614431] using wordTrace_append hprefix tailTrace_614431
  have hstable : (prefixWord ++ tailWord_614431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614431).length < 2 ^ (prefixWord ++ tailWord_614431).sum := by decide
  have hdescent : baseEnd_614431 < baseStart_614431 := by decide
  rcases family_descends (prefixWord ++ tailWord_614431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614448 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_614448 : Nat := 118140960795 + 614448 * 2 ^ 59
def prefixEnd_614448 : Nat := 4983230072969 + 3 ^ 40 * 614448 * 2
def baseEnd_614448 : Nat := 315507161193917203074211

theorem tailTrace_614448 : CollatzResearch.WordTrace tailWord_614448 prefixEnd_614448 315507161193917203074211 := by
  unfold tailWord_614448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205379838983655104429999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14940506451978206805906665 11205379838983655104429999)
  ·
    refine ⟨16808069758475482656644999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205379838983655104429999 16808069758475482656644999)
    ·
      refine ⟨25212104637713223984967499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16808069758475482656644999 25212104637713223984967499)
      ·
        refine ⟨37818156956569835977451249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25212104637713223984967499 37818156956569835977451249)
        ·
          refine ⟨28363617717427376983088437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37818156956569835977451249 28363617717427376983088437)
          ·
            refine ⟨2659089161008816592164541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28363617717427376983088437 2659089161008816592164541)
            ·
              refine ⟨997158435378306222061703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2659089161008816592164541 997158435378306222061703)
              ·
                refine ⟨1495737653067459333092555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997158435378306222061703 1495737653067459333092555)
                ·
                  refine ⟨2243606479601188999638833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495737653067459333092555 2243606479601188999638833)
                  ·
                    refine ⟨1682704859700891749729125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2243606479601188999638833 1682704859700891749729125)
                    ·
                      refine ⟨315507161193917203074211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1682704859700891749729125 315507161193917203074211)
                      ·
                        rfl

theorem cell23_614448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_614448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614448 prefixEnd_614448 := by exact prefixLift 614448
  have htrace : WordTrace (prefixWord ++ tailWord_614448) baseStart_614448 baseEnd_614448 := by
    simpa [prefixWord, tailWord_614448, baseEnd_614448] using wordTrace_append hprefix tailTrace_614448
  have hstable : (prefixWord ++ tailWord_614448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614448).length < 2 ^ (prefixWord ++ tailWord_614448).sum := by decide
  have hdescent : baseEnd_614448 < baseStart_614448 := by decide
  rcases family_descends (prefixWord ++ tailWord_614448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614481 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_614481 : Nat := 118140960795 + 614481 * 2 ^ 59
def prefixEnd_614481 : Nat := 4983230072969 + 3 ^ 40 * 614481 * 2
def baseEnd_614481 : Nat := 315524106055515573961559

theorem tailTrace_614481 : CollatzResearch.WordTrace tailWord_614481 prefixEnd_614481 315524106055515573961559 := by
  unfold tailWord_614481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411963286847756844811297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14941308857898504563207531 22411963286847756844811297)
  ·
    refine ⟨16808972465135817633608473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22411963286847756844811297 16808972465135817633608473)
    ·
      refine ⟨12606729348851863225206355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16808972465135817633608473 12606729348851863225206355)
      ·
        refine ⟨18910094023277794837809533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606729348851863225206355 18910094023277794837809533)
        ·
          refine ⟨7091285258729173064178575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18910094023277794837809533 7091285258729173064178575)
          ·
            refine ⟨10636927888093759596267863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091285258729173064178575 10636927888093759596267863)
            ·
              refine ⟨15955391832140639394401795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636927888093759596267863 15955391832140639394401795)
              ·
                refine ⟨23933087748210959091602693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15955391832140639394401795 23933087748210959091602693)
                ·
                  refine ⟨4487453952789554829675505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23933087748210959091602693 4487453952789554829675505)
                  ·
                    refine ⟨3365590464592166122256629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4487453952789554829675505 3365590464592166122256629)
                    ·
                      refine ⟨315524106055515573961559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3365590464592166122256629 315524106055515573961559)
                      ·
                        rfl

theorem cell23_614481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_614481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614481 prefixEnd_614481 := by exact prefixLift 614481
  have htrace : WordTrace (prefixWord ++ tailWord_614481) baseStart_614481 baseEnd_614481 := by
    simpa [prefixWord, tailWord_614481, baseEnd_614481] using wordTrace_append hprefix tailTrace_614481
  have hstable : (prefixWord ++ tailWord_614481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614481).length < 2 ^ (prefixWord ++ tailWord_614481).sum := by decide
  have hdescent : baseEnd_614481 < baseStart_614481 := by decide
  rcases family_descends (prefixWord ++ tailWord_614481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614485 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_614485 : Nat := 118140960795 + 614485 * 2 ^ 59
def prefixEnd_614485 : Nat := 4983230072969 + 3 ^ 40 * 614485 * 2
def baseEnd_614485 : Nat := 315526159978133558311541

theorem tailTrace_614485 : CollatzResearch.WordTrace tailWord_614485 prefixEnd_614485 315526159978133558311541 := by
  unfold tailWord_614485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22412109178833265527956909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14941406119222177018637939 22412109178833265527956909)
  ·
    refine ⟨8404540942062474572983841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22412109178833265527956909 8404540942062474572983841)
    ·
      refine ⟨6303405706546855929737881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8404540942062474572983841 6303405706546855929737881)
      ·
        refine ⟨4727554279910141947303411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6303405706546855929737881 4727554279910141947303411)
        ·
          refine ⟨7091331419865212920955117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727554279910141947303411 7091331419865212920955117)
          ·
            refine ⟨2659249282449454845358169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7091331419865212920955117 2659249282449454845358169)
            ·
              refine ⟨1994436961837091134018627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659249282449454845358169 1994436961837091134018627)
              ·
                refine ⟨2991655442755636701027941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994436961837091134018627 2991655442755636701027941)
                ·
                  refine ⟨560935395516681881442739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2991655442755636701027941 560935395516681881442739)
                  ·
                    refine ⟨841403093275022822164109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560935395516681881442739 841403093275022822164109)
                    ·
                      refine ⟨315526159978133558311541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841403093275022822164109 315526159978133558311541)
                      ·
                        rfl

theorem cell23_614485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_614485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614485 prefixEnd_614485 := by exact prefixLift 614485
  have htrace : WordTrace (prefixWord ++ tailWord_614485) baseStart_614485 baseEnd_614485 := by
    simpa [prefixWord, tailWord_614485, baseEnd_614485] using wordTrace_append hprefix tailTrace_614485
  have hstable : (prefixWord ++ tailWord_614485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614485).length < 2 ^ (prefixWord ++ tailWord_614485).sum := by decide
  have hdescent : baseEnd_614485 < baseStart_614485 := by decide
  rcases family_descends (prefixWord ++ tailWord_614485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614486 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_614486 : Nat := 118140960795 + 614486 * 2 ^ 59
def prefixEnd_614486 : Nat := 4983230072969 + 3 ^ 40 * 614486 * 2
def baseEnd_614486 : Nat := 315526673458788054399037

theorem tailTrace_614486 : CollatzResearch.WordTrace tailWord_614486 prefixEnd_614486 315526673458788054399037 := by
  unfold tailWord_614486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400759103239352668671457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14941430434553095132495541 1400759103239352668671457)
  ·
    refine ⟨1050569327429514501503593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1400759103239352668671457 1050569327429514501503593)
    ·
      refine ⟨787926995572135876127695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050569327429514501503593 787926995572135876127695)
      ·
        refine ⟨1181890493358203814191543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787926995572135876127695 1181890493358203814191543)
        ·
          refine ⟨1772835740037305721287315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181890493358203814191543 1772835740037305721287315)
          ·
            refine ⟨2659253610055958581930973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772835740037305721287315 2659253610055958581930973)
            ·
              refine ⟨997220103770984468224115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2659253610055958581930973 997220103770984468224115)
              ·
                refine ⟨1495830155656476702336173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997220103770984468224115 1495830155656476702336173)
                ·
                  refine ⟨560936308371178763376065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1495830155656476702336173 560936308371178763376065)
                  ·
                    refine ⟨420702231278384072532049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 560936308371178763376065 420702231278384072532049)
                    ·
                      refine ⟨315526673458788054399037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420702231278384072532049 315526673458788054399037)
                      ·
                        rfl

theorem cell23_614486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_614486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614486 prefixEnd_614486 := by exact prefixLift 614486
  have htrace : WordTrace (prefixWord ++ tailWord_614486) baseStart_614486 baseEnd_614486 := by
    simpa [prefixWord, tailWord_614486, baseEnd_614486] using wordTrace_append hprefix tailTrace_614486
  have hstable : (prefixWord ++ tailWord_614486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614486).length < 2 ^ (prefixWord ++ tailWord_614486).sum := by decide
  have hdescent : baseEnd_614486 < baseStart_614486 := by decide
  rcases family_descends (prefixWord ++ tailWord_614486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614512 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2]
def baseStart_614512 : Nat := 118140960795 + 614512 * 2 ^ 59
def prefixEnd_614512 : Nat := 4983230072969 + 3 ^ 40 * 614512 * 2
def baseEnd_614512 : Nat := 315540023955804952673917

theorem tailTrace_614512 : CollatzResearch.WordTrace tailWord_614512 prefixEnd_614512 315540023955804952673917 := by
  unfold tailWord_614512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206546974867724569594895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14942062633156966092793193 11206546974867724569594895)
  ·
    refine ⟨16809820462301586854392343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11206546974867724569594895 16809820462301586854392343)
    ·
      refine ⟨25214730693452380281588515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16809820462301586854392343 25214730693452380281588515)
      ·
        refine ⟨37822096040178570422382773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25214730693452380281588515 37822096040178570422382773)
        ·
          refine ⟨3545821503766740977098385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37822096040178570422382773 3545821503766740977098385)
          ·
            refine ⟨2659366127825055732823789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545821503766740977098385 2659366127825055732823789)
            ·
              refine ⟨997262297934395899808921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2659366127825055732823789 997262297934395899808921)
              ·
                refine ⟨747946723450796924856691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997262297934395899808921 747946723450796924856691)
                ·
                  refine ⟨1121920085176195387285037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747946723450796924856691 1121920085176195387285037)
                  ·
                    refine ⟨420720031941073270231889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121920085176195387285037 420720031941073270231889)
                    ·
                      refine ⟨315540023955804952673917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420720031941073270231889 315540023955804952673917)
                      ·
                        rfl

theorem cell23_614512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2].length) (baseStart_614512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614512 prefixEnd_614512 := by exact prefixLift 614512
  have htrace : WordTrace (prefixWord ++ tailWord_614512) baseStart_614512 baseEnd_614512 := by
    simpa [prefixWord, tailWord_614512, baseEnd_614512] using wordTrace_append hprefix tailTrace_614512
  have hstable : (prefixWord ++ tailWord_614512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614512).length < 2 ^ (prefixWord ++ tailWord_614512).sum := by decide
  have hdescent : baseEnd_614512 < baseStart_614512 := by decide
  rcases family_descends (prefixWord ++ tailWord_614512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614525 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_614525 : Nat := 118140960795 + 614525 * 2 ^ 59
def prefixEnd_614525 : Nat := 4983230072969 + 3 ^ 40 * 614525 * 2
def baseEnd_614525 : Nat := 315546699204313401811357

theorem tailTrace_614525 : CollatzResearch.WordTrace tailWord_614525 prefixEnd_614525 315546699204313401811357 := by
  unfold tailWord_614525
  simp only [CollatzResearch.WordTrace]
  refine ⟨22413568098688352359413029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14942378732458901572942019 22413568098688352359413029)
  ·
    refine ⟨4202544018504066067389943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22413568098688352359413029 4202544018504066067389943)
    ·
      refine ⟨6303816027756099101084915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4202544018504066067389943 6303816027756099101084915)
      ·
        refine ⟨9455724041634148651627373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6303816027756099101084915 9455724041634148651627373)
        ·
          refine ⟨3545896515612805744360265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9455724041634148651627373 3545896515612805744360265)
          ·
            refine ⟨2659422386709604308270199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545896515612805744360265 2659422386709604308270199)
            ·
              refine ⟨3989133580064406462405299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659422386709604308270199 3989133580064406462405299)
              ·
                refine ⟨5983700370096609693607949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989133580064406462405299 5983700370096609693607949)
                ·
                  refine ⟨2243887638786228635102981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5983700370096609693607949 2243887638786228635102981)
                  ·
                    refine ⟨420728932272417869081809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2243887638786228635102981 420728932272417869081809)
                    ·
                      refine ⟨315546699204313401811357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420728932272417869081809 315546699204313401811357)
                      ·
                        rfl

theorem cell23_614525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_614525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614525 prefixEnd_614525 := by exact prefixLift 614525
  have htrace : WordTrace (prefixWord ++ tailWord_614525) baseStart_614525 baseEnd_614525 := by
    simpa [prefixWord, tailWord_614525, baseEnd_614525] using wordTrace_append hprefix tailTrace_614525
  have hstable : (prefixWord ++ tailWord_614525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614525).length < 2 ^ (prefixWord ++ tailWord_614525).sum := by decide
  have hdescent : baseEnd_614525 < baseStart_614525 := by decide
  rcases family_descends (prefixWord ++ tailWord_614525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614559 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 2, 2, 2]
def baseStart_614559 : Nat := 118140960795 + 614559 * 2 ^ 59
def prefixEnd_614559 : Nat := 4983230072969 + 3 ^ 40 * 614559 * 2
def baseEnd_614559 : Nat := 315564157546566268786201

theorem tailTrace_614559 : CollatzResearch.WordTrace tailWord_614559 prefixEnd_614559 315564157546566268786201 := by
  unfold tailWord_614559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22414808180565176166150731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14943205453710117444100487 22414808180565176166150731)
  ·
    refine ⟨33622212270847764249226097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22414808180565176166150731 33622212270847764249226097)
    ·
      refine ⟨25216659203135823186919573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33622212270847764249226097 25216659203135823186919573)
      ·
        refine ⟨1182030900146991711886855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25216659203135823186919573 1182030900146991711886855)
        ·
          refine ⟨1773046350220487567830283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182030900146991711886855 1773046350220487567830283)
          ·
            refine ⟨2659569525330731351745425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773046350220487567830283 2659569525330731351745425)
            ·
              refine ⟨1994677143998048513809069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659569525330731351745425 1994677143998048513809069)
              ·
                refine ⟨748003928999268192678401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994677143998048513809069 748003928999268192678401)
                ·
                  refine ⟨561002946749451144508801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748003928999268192678401 561002946749451144508801)
                  ·
                    refine ⟨420752210062088358381601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 561002946749451144508801 420752210062088358381601)
                    ·
                      refine ⟨315564157546566268786201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420752210062088358381601 315564157546566268786201)
                      ·
                        rfl

theorem cell23_614559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_614559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614559 prefixEnd_614559 := by exact prefixLift 614559
  have htrace : WordTrace (prefixWord ++ tailWord_614559) baseStart_614559 baseEnd_614559 := by
    simpa [prefixWord, tailWord_614559, baseEnd_614559] using wordTrace_append hprefix tailTrace_614559
  have hstable : (prefixWord ++ tailWord_614559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614559).length < 2 ^ (prefixWord ++ tailWord_614559).sum := by decide
  have hdescent : baseEnd_614559 < baseStart_614559 := by decide
  rcases family_descends (prefixWord ++ tailWord_614559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614578 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_614578 : Nat := 118140960795 + 614578 * 2 ^ 59
def prefixEnd_614578 : Nat := 4983230072969 + 3 ^ 40 * 614578 * 2
def baseEnd_614578 : Nat := 105191304559667231482871

theorem tailTrace_614578 : CollatzResearch.WordTrace tailWord_614578 prefixEnd_614578 105191304559667231482871 := by
  unfold tailWord_614578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603875291874085602773097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14943667444997561607394925 5603875291874085602773097)
  ·
    refine ⟨4202906468905564202079823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5603875291874085602773097 4202906468905564202079823)
    ·
      refine ⟨6304359703358346303119735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4202906468905564202079823 6304359703358346303119735)
      ·
        refine ⟨9456539555037519454679603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304359703358346303119735 9456539555037519454679603)
        ·
          refine ⟨14184809332556279182019405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456539555037519454679603 14184809332556279182019405)
          ·
            refine ⟨5319303499708604693257277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14184809332556279182019405 5319303499708604693257277)
            ·
              refine ⟨1994738812390726759971479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5319303499708604693257277 1994738812390726759971479)
              ·
                refine ⟨2992108218586090139957219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994738812390726759971479 2992108218586090139957219)
                ·
                  refine ⟨4488162327879135209935829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992108218586090139957219 4488162327879135209935829)
                  ·
                    refine ⟨105191304559667231482871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4488162327879135209935829 105191304559667231482871)
                    ·
                      rfl

theorem cell23_614578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_614578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614578 prefixEnd_614578 := by exact prefixLift 614578
  have htrace : WordTrace (prefixWord ++ tailWord_614578) baseStart_614578 baseEnd_614578 := by
    simpa [prefixWord, tailWord_614578, baseEnd_614578] using wordTrace_append hprefix tailTrace_614578
  have hstable : (prefixWord ++ tailWord_614578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614578).length < 2 ^ (prefixWord ++ tailWord_614578).sum := by decide
  have hdescent : baseEnd_614578 < baseStart_614578 := by decide
  rcases family_descends (prefixWord ++ tailWord_614578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614593 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_614593 : Nat := 118140960795 + 614593 * 2 ^ 59
def prefixEnd_614593 : Nat := 4983230072969 + 3 ^ 40 * 614593 * 2
def baseEnd_614593 : Nat := 315581615888819135761045

theorem tailTrace_614593 : CollatzResearch.WordTrace tailWord_614593 prefixEnd_614593 315581615888819135761045 := by
  unfold tailWord_614593
  simp only [CollatzResearch.WordTrace]
  refine ⟨22416048262441999972888433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14944032174961333315258955 22416048262441999972888433)
  ·
    refine ⟨16812036196831499979666325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22416048262441999972888433 16812036196831499979666325)
    ·
      refine ⟨788064196726476561546859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16812036196831499979666325 788064196726476561546859)
      ·
        refine ⟨1182096295089714842320289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788064196726476561546859 1182096295089714842320289)
        ·
          refine ⟨886572221317286131740217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182096295089714842320289 886572221317286131740217)
          ·
            refine ⟨664929165987964598805163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886572221317286131740217 664929165987964598805163)
            ·
              refine ⟨997393748981946898207745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664929165987964598805163 997393748981946898207745)
              ·
                refine ⟨748045311736460173655809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997393748981946898207745 748045311736460173655809)
                ·
                  refine ⟨561033983802345130241857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748045311736460173655809 561033983802345130241857)
                  ·
                    refine ⟨420775487851758847681393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 561033983802345130241857 420775487851758847681393)
                    ·
                      refine ⟨315581615888819135761045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420775487851758847681393 315581615888819135761045)
                      ·
                        rfl

theorem cell23_614593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_614593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614593 prefixEnd_614593 := by exact prefixLift 614593
  have htrace : WordTrace (prefixWord ++ tailWord_614593) baseStart_614593 baseEnd_614593 := by
    simpa [prefixWord, tailWord_614593, baseEnd_614593] using wordTrace_append hprefix tailTrace_614593
  have hstable : (prefixWord ++ tailWord_614593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614593).length < 2 ^ (prefixWord ++ tailWord_614593).sum := by decide
  have hdescent : baseEnd_614593 < baseStart_614593 := by decide
  rcases family_descends (prefixWord ++ tailWord_614593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614625 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_614625 : Nat := 118140960795 + 614625 * 2 ^ 59
def prefixEnd_614625 : Nat := 4983230072969 + 3 ^ 40 * 614625 * 2
def baseEnd_614625 : Nat := 105199349089921003520299

theorem tailTrace_614625 : CollatzResearch.WordTrace tailWord_614625 prefixEnd_614625 105199349089921003520299 := by
  unfold tailWord_614625
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417215398326069438053329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14944810265550712958702219 22417215398326069438053329)
  ·
    refine ⟨16812911548744552078539997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417215398326069438053329 16812911548744552078539997)
    ·
      refine ⟨6304841830779207029452499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16812911548744552078539997 6304841830779207029452499)
      ·
        refine ⟨9457262746168810544178749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304841830779207029452499 9457262746168810544178749)
        ·
          refine ⟨3546473529813303954067031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9457262746168810544178749 3546473529813303954067031)
          ·
            refine ⟨5319710294719955931100547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546473529813303954067031 5319710294719955931100547)
            ·
              refine ⟨7979565442079933896650821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319710294719955931100547 7979565442079933896650821)
              ·
                refine ⟨1496168520389987605622029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7979565442079933896650821 1496168520389987605622029)
                ·
                  refine ⟨561063195146245352108261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1496168520389987605622029 561063195146245352108261)
                  ·
                    refine ⟨105199349089921003520299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561063195146245352108261 105199349089921003520299)
                    ·
                      rfl

theorem cell23_614625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_614625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614625 prefixEnd_614625 := by exact prefixLift 614625
  have htrace : WordTrace (prefixWord ++ tailWord_614625) baseStart_614625 baseEnd_614625 := by
    simpa [prefixWord, tailWord_614625, baseEnd_614625] using wordTrace_append hprefix tailTrace_614625
  have hstable : (prefixWord ++ tailWord_614625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614625).length < 2 ^ (prefixWord ++ tailWord_614625).sum := by decide
  have hdescent : baseEnd_614625 < baseStart_614625 := by decide
  rcases family_descends (prefixWord ++ tailWord_614625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614628 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_614628 : Nat := 118140960795 + 614628 * 2 ^ 59
def prefixEnd_614628 : Nat := 4983230072969 + 3 ^ 40 * 614628 * 2
def baseEnd_614628 : Nat := 315599587711726498823383

theorem tailTrace_614628 : CollatzResearch.WordTrace tailWord_614628 prefixEnd_614628 315599587711726498823383 := by
  unfold tailWord_614628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11208662408657600475206269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14944883211543467300275025 11208662408657600475206269)
  ·
    refine ⟨4203248403246600178202351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11208662408657600475206269 4203248403246600178202351)
    ·
      refine ⟨6304872604869900267303527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203248403246600178202351 6304872604869900267303527)
      ·
        refine ⟨9457308907304850400955291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304872604869900267303527 9457308907304850400955291)
        ·
          refine ⟨14185963360957275601432937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457308907304850400955291 14185963360957275601432937)
          ·
            refine ⟨10639472520717956701074703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14185963360957275601432937 10639472520717956701074703)
            ·
              refine ⟨15959208781076935051612055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10639472520717956701074703 15959208781076935051612055)
              ·
                refine ⟨23938813171615402577418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15959208781076935051612055 23938813171615402577418083)
                ·
                  refine ⟨35908219757423103866127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23938813171615402577418083 35908219757423103866127125)
                  ·
                    refine ⟨1683197801129207993724709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35908219757423103866127125 1683197801129207993724709)
                    ·
                      refine ⟨315599587711726498823383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1683197801129207993724709 315599587711726498823383)
                      ·
                        rfl

theorem cell23_614628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_614628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614628 prefixEnd_614628 := by exact prefixLift 614628
  have htrace : WordTrace (prefixWord ++ tailWord_614628) baseStart_614628 baseEnd_614628 := by
    simpa [prefixWord, tailWord_614628, baseEnd_614628] using wordTrace_append hprefix tailTrace_614628
  have hstable : (prefixWord ++ tailWord_614628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614628).length < 2 ^ (prefixWord ++ tailWord_614628).sum := by decide
  have hdescent : baseEnd_614628 < baseStart_614628 := by decide
  rcases family_descends (prefixWord ++ tailWord_614628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614635 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3]
def baseStart_614635 : Nat := 118140960795 + 614635 * 2 ^ 59
def prefixEnd_614635 : Nat := 4983230072969 + 3 ^ 40 * 614635 * 2
def baseEnd_614635 : Nat := 315603182076307971435851

theorem tailTrace_614635 : CollatzResearch.WordTrace tailWord_614635 prefixEnd_614635 315603182076307971435851 := by
  unfold tailWord_614635
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417580128289841145917359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945053418859894097278239 22417580128289841145917359)
  ·
    refine ⟨33626370192434761718876039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22417580128289841145917359 33626370192434761718876039)
    ·
      refine ⟨50439555288652142578314059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33626370192434761718876039 50439555288652142578314059)
      ·
        refine ⟨75659332932978213867471089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50439555288652142578314059 75659332932978213867471089)
        ·
          refine ⟨56744499699733660400603317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75659332932978213867471089 56744499699733660400603317)
          ·
            refine ⟨5319796846850030662556561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56744499699733660400603317 5319796846850030662556561)
            ·
              refine ⟨3989847635137522996917421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5319796846850030662556561 3989847635137522996917421)
              ·
                refine ⟨1496192863176571123844033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3989847635137522996917421 1496192863176571123844033)
                ·
                  refine ⟨1122144647382428342883025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496192863176571123844033 1122144647382428342883025)
                  ·
                    refine ⟨841608485536821257162269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122144647382428342883025 841608485536821257162269)
                    ·
                      refine ⟨315603182076307971435851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841608485536821257162269 315603182076307971435851)
                      ·
                        rfl

theorem cell23_614635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].length) (baseStart_614635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614635 prefixEnd_614635 := by exact prefixLift 614635
  have htrace : WordTrace (prefixWord ++ tailWord_614635) baseStart_614635 baseEnd_614635 := by
    simpa [prefixWord, tailWord_614635, baseEnd_614635] using wordTrace_append hprefix tailTrace_614635
  have hstable : (prefixWord ++ tailWord_614635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614635).length < 2 ^ (prefixWord ++ tailWord_614635).sum := by decide
  have hdescent : baseEnd_614635 < baseStart_614635 := by decide
  rcases family_descends (prefixWord ++ tailWord_614635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614652 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_614652 : Nat := 118140960795 + 614652 * 2 ^ 59
def prefixEnd_614652 : Nat := 4983230072969 + 3 ^ 40 * 614652 * 2
def baseEnd_614652 : Nat := 315611911247434404923273

theorem tailTrace_614652 : CollatzResearch.WordTrace tailWord_614652 prefixEnd_614652 315611911247434404923273 := by
  unfold tailWord_614652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209100084614126524643105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14945466779485502032857473 11209100084614126524643105)
  ·
    refine ⟨8406825063460594893482329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11209100084614126524643105 8406825063460594893482329)
    ·
      refine ⟨6305118797595446170111747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8406825063460594893482329 6305118797595446170111747)
      ·
        refine ⟨9457678196393169255167621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305118797595446170111747 9457678196393169255167621)
        ·
          refine ⟨1773314661823719235343929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9457678196393169255167621 1773314661823719235343929)
          ·
            refine ⟨1329985996367789426507947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773314661823719235343929 1329985996367789426507947)
            ·
              refine ⟨1994978994551684139761921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329985996367789426507947 1994978994551684139761921)
              ·
                refine ⟨1496234245913763104821441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994978994551684139761921 1496234245913763104821441)
                ·
                  refine ⟨1122175684435322328616081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496234245913763104821441 1122175684435322328616081)
                  ·
                    refine ⟨841631763326491746462061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122175684435322328616081 841631763326491746462061)
                    ·
                      refine ⟨315611911247434404923273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841631763326491746462061 315611911247434404923273)
                      ·
                        rfl

theorem cell23_614652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_614652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614652 prefixEnd_614652 := by exact prefixLift 614652
  have htrace : WordTrace (prefixWord ++ tailWord_614652) baseStart_614652 baseEnd_614652 := by
    simpa [prefixWord, tailWord_614652, baseEnd_614652] using wordTrace_append hprefix tailTrace_614652
  have hstable : (prefixWord ++ tailWord_614652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614652).length < 2 ^ (prefixWord ++ tailWord_614652).sum := by decide
  have hdescent : baseEnd_614652 < baseStart_614652 := by decide
  rcases family_descends (prefixWord ++ tailWord_614652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614659 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 1, 4]
def baseStart_614659 : Nat := 118140960795 + 614659 * 2 ^ 59
def prefixEnd_614659 : Nat := 4983230072969 + 3 ^ 40 * 614659 * 2
def baseEnd_614659 : Nat := 105205168537338625845247

theorem tailTrace_614659 : CollatzResearch.WordTrace tailWord_614659 prefixEnd_614659 105205168537338625845247 := by
  unfold tailWord_614659
  simp only [CollatzResearch.WordTrace]
  refine ⟨22418455480202893244791031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945636986801928829860687 22418455480202893244791031)
  ·
    refine ⟨33627683220304339867186547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22418455480202893244791031 33627683220304339867186547)
    ·
      refine ⟨50441524830456509800779821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33627683220304339867186547 50441524830456509800779821)
      ·
        refine ⟨18915571811421191175292433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50441524830456509800779821 18915571811421191175292433)
        ·
          refine ⟨14186678858565893381469325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18915571811421191175292433 14186678858565893381469325)
          ·
            refine ⟨5320004571962210018050997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14186678858565893381469325 5320004571962210018050997)
            ·
              refine ⟨498750428621457189192281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5320004571962210018050997 498750428621457189192281)
              ·
                refine ⟨374062821466092891894211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498750428621457189192281 374062821466092891894211)
                ·
                  refine ⟨561094232199139337841317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374062821466092891894211 561094232199139337841317)
                  ·
                    refine ⟨105205168537338625845247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561094232199139337841317 105205168537338625845247)
                    ·
                      rfl

theorem cell23_614659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 4].length) (baseStart_614659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614659 prefixEnd_614659 := by exact prefixLift 614659
  have htrace : WordTrace (prefixWord ++ tailWord_614659) baseStart_614659 baseEnd_614659 := by
    simpa [prefixWord, tailWord_614659, baseEnd_614659] using wordTrace_append hprefix tailTrace_614659
  have hstable : (prefixWord ++ tailWord_614659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614659).length < 2 ^ (prefixWord ++ tailWord_614659).sum := by decide
  have hdescent : baseEnd_614659 < baseStart_614659 := by decide
  rcases family_descends (prefixWord ++ tailWord_614659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614675 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 5, 2]
def baseStart_614675 : Nat := 118140960795 + 614675 * 2 ^ 59
def prefixEnd_614675 : Nat := 4983230072969 + 3 ^ 40 * 614675 * 2
def baseEnd_614675 : Nat := 315623721302487814935667

theorem tailTrace_614675 : CollatzResearch.WordTrace tailWord_614675 prefixEnd_614675 315623721302487814935667 := by
  unfold tailWord_614675
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419039048144927977373479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14946026032096618651582319 22419039048144927977373479)
  ·
    refine ⟨33628558572217391966060219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22419039048144927977373479 33628558572217391966060219)
    ·
      refine ⟨50442837858326087949090329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33628558572217391966060219 50442837858326087949090329)
      ·
        refine ⟨37832128393744565961817747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50442837858326087949090329 37832128393744565961817747)
        ·
          refine ⟨56748192590616848942726621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37832128393744565961817747 56748192590616848942726621)
          ·
            refine ⟨21280572221481318353522483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56748192590616848942726621 21280572221481318353522483)
            ·
              refine ⟨31920858332221977530283725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21280572221481318353522483 31920858332221977530283725)
              ·
                refine ⟨11970321874583241573856397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31920858332221977530283725 11970321874583241573856397)
                ·
                  refine ⟨4488870702968715590196149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11970321874583241573856397 4488870702968715590196149)
                  ·
                    refine ⟨420831628403317086580889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4488870702968715590196149 420831628403317086580889)
                    ·
                      refine ⟨315623721302487814935667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420831628403317086580889 315623721302487814935667)
                      ·
                        rfl

theorem cell23_614675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5, 2].length) (baseStart_614675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614675 prefixEnd_614675 := by exact prefixLift 614675
  have htrace : WordTrace (prefixWord ++ tailWord_614675) baseStart_614675 baseEnd_614675 := by
    simpa [prefixWord, tailWord_614675, baseEnd_614675] using wordTrace_append hprefix tailTrace_614675
  have hstable : (prefixWord ++ tailWord_614675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614675).length < 2 ^ (prefixWord ++ tailWord_614675).sum := by decide
  have hdescent : baseEnd_614675 < baseStart_614675 := by decide
  rcases family_descends (prefixWord ++ tailWord_614675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614686 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_614686 : Nat := 118140960795 + 614686 * 2 ^ 59
def prefixEnd_614686 : Nat := 4983230072969 + 3 ^ 40 * 614686 * 2
def baseEnd_614686 : Nat := 315629369589687271898117

theorem tailTrace_614686 : CollatzResearch.WordTrace tailWord_614686 prefixEnd_614686 315629369589687271898117 := by
  unfold tailWord_614686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802430031388134607002989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14946293500736717904015941 2802430031388134607002989)
  ·
    refine ⟨1050911261770550477626121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2802430031388134607002989 1050911261770550477626121)
    ·
      refine ⟨788183446327912858219591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050911261770550477626121 788183446327912858219591)
      ·
        refine ⟨1182275169491869287329387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788183446327912858219591 1182275169491869287329387)
        ·
          refine ⟨1773412754237803930994081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182275169491869287329387 1773412754237803930994081)
          ·
            refine ⟨1330059565678352948245561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773412754237803930994081 1330059565678352948245561)
            ·
              refine ⟨997544674258764711184171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330059565678352948245561 997544674258764711184171)
              ·
                refine ⟨1496317011388147066776257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997544674258764711184171 1496317011388147066776257)
                ·
                  refine ⟨1122237758541110300082193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496317011388147066776257 1122237758541110300082193)
                  ·
                    refine ⟨841678318905832725061645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122237758541110300082193 841678318905832725061645)
                    ·
                      refine ⟨315629369589687271898117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841678318905832725061645 315629369589687271898117)
                      ·
                        rfl

theorem cell23_614686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_614686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614686 prefixEnd_614686 := by exact prefixLift 614686
  have htrace : WordTrace (prefixWord ++ tailWord_614686) baseStart_614686 baseEnd_614686 := by
    simpa [prefixWord, tailWord_614686, baseEnd_614686] using wordTrace_append hprefix tailTrace_614686
  have hstable : (prefixWord ++ tailWord_614686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614686).length < 2 ^ (prefixWord ++ tailWord_614686).sum := by decide
  have hdescent : baseEnd_614686 < baseStart_614686 := by decide
  rcases family_descends (prefixWord ++ tailWord_614686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614732 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_614732 : Nat := 118140960795 + 614732 * 2 ^ 59
def prefixEnd_614732 : Nat := 4983230072969 + 3 ^ 40 * 614732 * 2
def baseEnd_614732 : Nat := 105217663233264697307635

theorem tailTrace_614732 : CollatzResearch.WordTrace tailWord_614732 prefixEnd_614732 105217663233264697307635 := by
  unfold tailWord_614732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210559004469213356099225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14947412005958951141465633 11210559004469213356099225)
  ·
    refine ⟨8407919253351910017074419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11210559004469213356099225 8407919253351910017074419)
    ·
      refine ⟨12611878880027865025611629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407919253351910017074419 12611878880027865025611629)
      ·
        refine ⟨4729454580010449384604361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12611878880027865025611629 4729454580010449384604361)
        ·
          refine ⟨3547090935007837038453271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729454580010449384604361 3547090935007837038453271)
          ·
            refine ⟨5320636402511755557679907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547090935007837038453271 5320636402511755557679907)
            ·
              refine ⟨7980954603767633336519861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320636402511755557679907 7980954603767633336519861)
              ·
                refine ⟨748214494103215625298737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7980954603767633336519861 748214494103215625298737)
                ·
                  refine ⟨561160870577411718974053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748214494103215625298737 561160870577411718974053)
                  ·
                    refine ⟨105217663233264697307635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561160870577411718974053 105217663233264697307635)
                    ·
                      rfl

theorem cell23_614732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_614732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614732 prefixEnd_614732 := by exact prefixLift 614732
  have htrace : WordTrace (prefixWord ++ tailWord_614732) baseStart_614732 baseEnd_614732 := by
    simpa [prefixWord, tailWord_614732, baseEnd_614732] using wordTrace_append hprefix tailTrace_614732
  have hstable : (prefixWord ++ tailWord_614732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614732).length < 2 ^ (prefixWord ++ tailWord_614732).sum := by decide
  have hdescent : baseEnd_614732 < baseStart_614732 := by decide
  rcases family_descends (prefixWord ++ tailWord_614732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614759 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_614759 : Nat := 118140960795 + 614759 * 2 ^ 59
def prefixEnd_614759 : Nat := 4983230072969 + 3 ^ 40 * 614759 * 2
def baseEnd_614759 : Nat := 315666853677465486285281

theorem tailTrace_614759 : CollatzResearch.WordTrace tailWord_614759 prefixEnd_614759 315666853677465486285281 := by
  unfold tailWord_614759
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422102779840610323431331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14948068519893740215620887 22422102779840610323431331)
  ·
    refine ⟨33633154169760915485146997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22422102779840610323431331 33633154169760915485146997)
    ·
      refine ⟨3153108203415085826732531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33633154169760915485146997 3153108203415085826732531)
      ·
        refine ⟨4729662305122628740098797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153108203415085826732531 4729662305122628740098797)
        ·
          refine ⟨1773623364420985777537049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4729662305122628740098797 1773623364420985777537049)
          ·
            refine ⟨1330217523315739333152787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773623364420985777537049 1330217523315739333152787)
            ·
              refine ⟨1995326284973608999729181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330217523315739333152787 1995326284973608999729181)
              ·
                refine ⟨748247356865103374898443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995326284973608999729181 748247356865103374898443)
                ·
                  refine ⟨1122371035297655062347665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748247356865103374898443 1122371035297655062347665)
                  ·
                    refine ⟨841778276473241296760749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122371035297655062347665 841778276473241296760749)
                    ·
                      refine ⟨315666853677465486285281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841778276473241296760749 315666853677465486285281)
                      ·
                        rfl

theorem cell23_614759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_614759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614759 prefixEnd_614759 := by exact prefixLift 614759
  have htrace : WordTrace (prefixWord ++ tailWord_614759) baseStart_614759 baseEnd_614759 := by
    simpa [prefixWord, tailWord_614759, baseEnd_614759] using wordTrace_append hprefix tailTrace_614759
  have hstable : (prefixWord ++ tailWord_614759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614759).length < 2 ^ (prefixWord ++ tailWord_614759).sum := by decide
  have hdescent : baseEnd_614759 < baseStart_614759 := by decide
  rcases family_descends (prefixWord ++ tailWord_614759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614773 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_614773 : Nat := 118140960795 + 614773 * 2 ^ 59
def prefixEnd_614773 : Nat := 4983230072969 + 3 ^ 40 * 614773 * 2
def baseEnd_614773 : Nat := 315674042406628431510217

theorem tailTrace_614773 : CollatzResearch.WordTrace tailWord_614773 prefixEnd_614773 315674042406628431510217 := by
  unfold tailWord_614773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422613401789890714440973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14948408934526593809627315 22422613401789890714440973)
  ·
    refine ⟨8408480025671209017915365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22422613401789890714440973 8408480025671209017915365)
    ·
      refine ⟨1576590004813351690859131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8408480025671209017915365 1576590004813351690859131)
      ·
        refine ⟨2364885007220027536288697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576590004813351690859131 2364885007220027536288697)
        ·
          refine ⟨1773663755415020652216523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364885007220027536288697 1773663755415020652216523)
          ·
            refine ⟨2660495633122530978324785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773663755415020652216523 2660495633122530978324785)
            ·
              refine ⟨1995371724841898233743589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660495633122530978324785 1995371724841898233743589)
              ·
                refine ⟨374132198407855918826923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1995371724841898233743589 374132198407855918826923)
                ·
                  refine ⟨561198297611783878240385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374132198407855918826923 561198297611783878240385)
                  ·
                    refine ⟨420898723208837908680289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 561198297611783878240385 420898723208837908680289)
                    ·
                      refine ⟨315674042406628431510217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 420898723208837908680289 315674042406628431510217)
                      ·
                        rfl

theorem cell23_614773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_614773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614773 prefixEnd_614773 := by exact prefixLift 614773
  have htrace : WordTrace (prefixWord ++ tailWord_614773) baseStart_614773 baseEnd_614773 := by
    simpa [prefixWord, tailWord_614773, baseEnd_614773] using wordTrace_append hprefix tailTrace_614773
  have hstable : (prefixWord ++ tailWord_614773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614773).length < 2 ^ (prefixWord ++ tailWord_614773).sum := by decide
  have hdescent : baseEnd_614773 < baseStart_614773 := by decide
  rcases family_descends (prefixWord ++ tailWord_614773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614825 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_614825 : Nat := 118140960795 + 614825 * 2 ^ 59
def prefixEnd_614825 : Nat := 4983230072969 + 3 ^ 40 * 614825 * 2
def baseEnd_614825 : Nat := 315700743400662228059977

theorem tailTrace_614825 : CollatzResearch.WordTrace tailWord_614825 prefixEnd_614825 315700743400662228059977 := by
  unfold tailWord_614825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424509997601503595333929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14949673331734335730222619 22424509997601503595333929)
  ·
    refine ⟨16818382498201127696500447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22424509997601503595333929 16818382498201127696500447)
    ·
      refine ⟨25227573747301691544750671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16818382498201127696500447 25227573747301691544750671)
      ·
        refine ⟨37841360620952537317126007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25227573747301691544750671 37841360620952537317126007)
        ·
          refine ⟨56762040931428805975689011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37841360620952537317126007 56762040931428805975689011)
          ·
            refine ⟨85143061397143208963533517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56762040931428805975689011 85143061397143208963533517)
            ·
              refine ⟨31928648023928703361325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85143061397143208963533517 31928648023928703361325069)
              ·
                refine ⟨11973243008973263760496901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31928648023928703361325069 11973243008973263760496901)
                ·
                  refine ⟨2244983064182486955093169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11973243008973263760496901 2244983064182486955093169)
                  ·
                    refine ⟨1683737298136865216319877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244983064182486955093169 1683737298136865216319877)
                    ·
                      refine ⟨315700743400662228059977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1683737298136865216319877 315700743400662228059977)
                      ·
                        rfl

theorem cell23_614825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_614825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614825 prefixEnd_614825 := by exact prefixLift 614825
  have htrace : WordTrace (prefixWord ++ tailWord_614825) baseStart_614825 baseEnd_614825 := by
    simpa [prefixWord, tailWord_614825, baseEnd_614825] using wordTrace_append hprefix tailTrace_614825
  have hstable : (prefixWord ++ tailWord_614825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614825).length < 2 ^ (prefixWord ++ tailWord_614825).sum := by decide
  have hdescent : baseEnd_614825 < baseStart_614825 := by decide
  rcases family_descends (prefixWord ++ tailWord_614825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614862 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_614862 : Nat := 118140960795 + 614862 * 2 ^ 59
def prefixEnd_614862 : Nat := 4983230072969 + 3 ^ 40 * 614862 * 2
def baseEnd_614862 : Nat := 315719742184878583297307

theorem tailTrace_614862 : CollatzResearch.WordTrace tailWord_614862 prefixEnd_614862 315719742184878583297307 := by
  unfold tailWord_614862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803232437308432364303855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14950572998978305942953893 2803232437308432364303855)
  ·
    refine ⟨4204848655962648546455783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2803232437308432364303855 4204848655962648546455783)
    ·
      refine ⟨6307272983943972819683675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204848655962648546455783 6307272983943972819683675)
      ·
        refine ⟨9460909475915959229525513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307272983943972819683675 9460909475915959229525513)
        ·
          refine ⟨7095682106936969422144135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9460909475915959229525513 7095682106936969422144135)
          ·
            refine ⟨10643523160405454133216203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7095682106936969422144135 10643523160405454133216203)
            ·
              refine ⟨15965284740608181199824305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10643523160405454133216203 15965284740608181199824305)
              ·
                refine ⟨11973963555456135899868229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15965284740608181199824305 11973963555456135899868229)
                ·
                  refine ⟨2245118166648025481225293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11973963555456135899868229 2245118166648025481225293)
                  ·
                    refine ⟨841919312493009555459485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245118166648025481225293 841919312493009555459485)
                    ·
                      refine ⟨315719742184878583297307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 841919312493009555459485 315719742184878583297307)
                      ·
                        rfl

theorem cell23_614862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_614862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614862 prefixEnd_614862 := by exact prefixLift 614862
  have htrace : WordTrace (prefixWord ++ tailWord_614862) baseStart_614862 baseEnd_614862 := by
    simpa [prefixWord, tailWord_614862, baseEnd_614862] using wordTrace_append hprefix tailTrace_614862
  have hstable : (prefixWord ++ tailWord_614862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614862).length < 2 ^ (prefixWord ++ tailWord_614862).sum := by decide
  have hdescent : baseEnd_614862 < baseStart_614862 := by decide
  rcases family_descends (prefixWord ++ tailWord_614862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614865 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_614865 : Nat := 118140960795 + 614865 * 2 ^ 59
def prefixEnd_614865 : Nat := 4983230072969 + 3 ^ 40 * 614865 * 2
def baseEnd_614865 : Nat := 105240427542280690519931

theorem tailTrace_614865 : CollatzResearch.WordTrace tailWord_614865 prefixEnd_614865 105240427542280690519931 := by
  unfold tailWord_614865
  simp only [CollatzResearch.WordTrace]
  refine ⟨22425968917456590426790049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14950645944971060284526699 22425968917456590426790049)
  ·
    refine ⟨16819476688092442820092537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22425968917456590426790049 16819476688092442820092537)
    ·
      refine ⟨12614607516069332115069403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16819476688092442820092537 12614607516069332115069403)
      ·
        refine ⟨18921911274103998172604105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12614607516069332115069403 18921911274103998172604105)
        ·
          refine ⟨14191433455577998629453079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18921911274103998172604105 14191433455577998629453079)
          ·
            refine ⟨21287150183366997944179619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14191433455577998629453079 21287150183366997944179619)
            ·
              refine ⟨31930725275050496916269429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21287150183366997944179619 31930725275050496916269429)
              ·
                refine ⟨2993505494535984085900259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31930725275050496916269429 2993505494535984085900259)
                ·
                  refine ⟨4490258241803976128850389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993505494535984085900259 4490258241803976128850389)
                  ·
                    refine ⟨105240427542280690519931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4490258241803976128850389 105240427542280690519931)
                    ·
                      rfl

theorem cell23_614865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_614865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614865 prefixEnd_614865 := by exact prefixLift 614865
  have htrace : WordTrace (prefixWord ++ tailWord_614865) baseStart_614865 baseEnd_614865 := by
    simpa [prefixWord, tailWord_614865, baseEnd_614865] using wordTrace_append hprefix tailTrace_614865
  have hstable : (prefixWord ++ tailWord_614865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614865).length < 2 ^ (prefixWord ++ tailWord_614865).sum := by decide
  have hdescent : baseEnd_614865 < baseStart_614865 := by decide
  rcases family_descends (prefixWord ++ tailWord_614865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614895 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 8]
def baseStart_614895 : Nat := 118140960795 + 614895 * 2 ^ 59
def prefixEnd_614895 : Nat := 4983230072969 + 3 ^ 40 * 614895 * 2
def baseEnd_614895 : Nat := 105245562348825651394885

theorem tailTrace_614895 : CollatzResearch.WordTrace tailWord_614895 prefixEnd_614895 105245562348825651394885 := by
  unfold tailWord_614895
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427063107347905550382139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14951375404898603700254759 22427063107347905550382139)
  ·
    refine ⟨33640594661021858325573209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22427063107347905550382139 33640594661021858325573209)
    ·
      refine ⟨25230445995766393744179907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33640594661021858325573209 25230445995766393744179907)
      ·
        refine ⟨37845668993649590616269861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25230445995766393744179907 37845668993649590616269861)
        ·
          refine ⟨7096062936309298240550599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37845668993649590616269861 7096062936309298240550599)
          ·
            refine ⟨10644094404463947360825899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096062936309298240550599 10644094404463947360825899)
            ·
              refine ⟨15966141606695921041238849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10644094404463947360825899 15966141606695921041238849)
              ·
                refine ⟨11974606205021940780929137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15966141606695921041238849 11974606205021940780929137)
                ·
                  refine ⟨8980954653766455585696853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11974606205021940780929137 8980954653766455585696853)
                  ·
                    refine ⟨105245562348825651394885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8980954653766455585696853 105245562348825651394885)
                    ·
                      rfl

theorem cell23_614895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_614895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614895 prefixEnd_614895 := by exact prefixLift 614895
  have htrace : WordTrace (prefixWord ++ tailWord_614895) baseStart_614895 baseEnd_614895 := by
    simpa [prefixWord, tailWord_614895, baseEnd_614895] using wordTrace_append hprefix tailTrace_614895
  have hstable : (prefixWord ++ tailWord_614895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614895).length < 2 ^ (prefixWord ++ tailWord_614895).sum := by decide
  have hdescent : baseEnd_614895 < baseStart_614895 := by decide
  rcases family_descends (prefixWord ++ tailWord_614895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614916 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_614916 : Nat := 118140960795 + 614916 * 2 ^ 59
def prefixEnd_614916 : Nat := 4983230072969 + 3 ^ 40 * 614916 * 2
def baseEnd_614916 : Nat := 105249156713407124007353

theorem tailTrace_614916 : CollatzResearch.WordTrace tailWord_614916 prefixEnd_614916 105249156713407124007353 := by
  unfold tailWord_614916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213914520135913068448301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14951886026847884091264401 11213914520135913068448301)
  ·
    refine ⟨4205217945050967400668113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11213914520135913068448301 4205217945050967400668113)
    ·
      refine ⟨3153913458788225550501085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4205217945050967400668113 3153913458788225550501085)
      ·
        refine ⟨1182717547045584581437907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3153913458788225550501085 1182717547045584581437907)
        ·
          refine ⟨1774076320568376872156861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182717547045584581437907 1774076320568376872156861)
          ·
            refine ⟨665278620213141327058823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1774076320568376872156861 665278620213141327058823)
            ·
              refine ⟨997917930319711990588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665278620213141327058823 997917930319711990588235)
              ·
                refine ⟨1496876895479567985882353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997917930319711990588235 1496876895479567985882353)
                ·
                  refine ⟨1122657671609675989411765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496876895479567985882353 1122657671609675989411765)
                  ·
                    refine ⟨105249156713407124007353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1122657671609675989411765 105249156713407124007353)
                    ·
                      rfl

theorem cell23_614916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_614916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614916 prefixEnd_614916 := by exact prefixLift 614916
  have htrace : WordTrace (prefixWord ++ tailWord_614916) baseStart_614916 baseEnd_614916 := by
    simpa [prefixWord, tailWord_614916, baseEnd_614916] using wordTrace_append hprefix tailTrace_614916
  have hstable : (prefixWord ++ tailWord_614916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614916).length < 2 ^ (prefixWord ++ tailWord_614916).sum := by decide
  have hdescent : baseEnd_614916 < baseStart_614916 := by decide
  rcases family_descends (prefixWord ++ tailWord_614916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614919 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_614919 : Nat := 118140960795 + 614919 * 2 ^ 59
def prefixEnd_614919 : Nat := 4983230072969 + 3 ^ 40 * 614919 * 2
def baseEnd_614919 : Nat := 315749010582184860284545

theorem tailTrace_614919 : CollatzResearch.WordTrace tailWord_614919 prefixEnd_614919 315749010582184860284545 := by
  unfold tailWord_614919
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427938459260957649255811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14951958972840638432837207 22427938459260957649255811)
  ·
    refine ⟨33641907688891436473883717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22427938459260957649255811 33641907688891436473883717)
    ·
      refine ⟨6307857691667144338853197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33641907688891436473883717 6307857691667144338853197)
      ·
        refine ⟨2365446634375179127069949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6307857691667144338853197 2365446634375179127069949)
        ·
          refine ⟨887042487890692172651231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2365446634375179127069949 887042487890692172651231)
          ·
            refine ⟨1330563731836038258976847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887042487890692172651231 1330563731836038258976847)
            ·
              refine ⟨1995845597754057388465271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330563731836038258976847 1995845597754057388465271)
              ·
                refine ⟨2993768396631086082697907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995845597754057388465271 2993768396631086082697907)
                ·
                  refine ⟨4490652594946629124046861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993768396631086082697907 4490652594946629124046861)
                  ·
                    refine ⟨1683994723104985921517573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4490652594946629124046861 1683994723104985921517573)
                    ·
                      refine ⟨315749010582184860284545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1683994723104985921517573 315749010582184860284545)
                      ·
                        rfl

theorem cell23_614919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_614919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614919 prefixEnd_614919 := by exact prefixLift 614919
  have htrace : WordTrace (prefixWord ++ tailWord_614919) baseStart_614919 baseEnd_614919 := by
    simpa [prefixWord, tailWord_614919, baseEnd_614919] using wordTrace_append hprefix tailTrace_614919
  have hstable : (prefixWord ++ tailWord_614919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614919).length < 2 ^ (prefixWord ++ tailWord_614919).sum := by decide
  have hdescent : baseEnd_614919 < baseStart_614919 := by decide
  rcases family_descends (prefixWord ++ tailWord_614919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614979 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 6, 3, 2]
def baseStart_614979 : Nat := 118140960795 + 614979 * 2 ^ 59
def prefixEnd_614979 : Nat := 4983230072969 + 3 ^ 40 * 614979 * 2
def baseEnd_614979 : Nat := 315779819421454625534269

theorem tailTrace_614979 : CollatzResearch.WordTrace tailWord_614979 prefixEnd_614979 315779819421454625534269 := by
  unfold tailWord_614979
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430126839043587896439991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14953417892695725264293327 22430126839043587896439991)
  ·
    refine ⟨33645190258565381844659987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22430126839043587896439991 33645190258565381844659987)
    ·
      refine ⟨50467785387848072766989981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33645190258565381844659987 50467785387848072766989981)
      ·
        refine ⟨18925419520443027287621243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50467785387848072766989981 18925419520443027287621243)
        ·
          refine ⟨28388129280664540931431865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18925419520443027287621243 28388129280664540931431865)
          ·
            refine ⟨21291096960498405698573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28388129280664540931431865 21291096960498405698573899)
            ·
              refine ⟨31936645440747608547860849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21291096960498405698573899 31936645440747608547860849)
              ·
                refine ⟨23952484080560706410895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31936645440747608547860849 23952484080560706410895637)
                ·
                  refine ⟨1122772691276283113010733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23952484080560706410895637 1122772691276283113010733)
                  ·
                    refine ⟨421039759228606167379025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122772691276283113010733 421039759228606167379025)
                    ·
                      refine ⟨315779819421454625534269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421039759228606167379025 315779819421454625534269)
                      ·
                        rfl

theorem cell23_614979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_614979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614979 prefixEnd_614979 := by exact prefixLift 614979
  have htrace : WordTrace (prefixWord ++ tailWord_614979) baseStart_614979 baseEnd_614979 := by
    simpa [prefixWord, tailWord_614979, baseEnd_614979] using wordTrace_append hprefix tailTrace_614979
  have hstable : (prefixWord ++ tailWord_614979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614979).length < 2 ^ (prefixWord ++ tailWord_614979).sum := by decide
  have hdescent : baseEnd_614979 < baseStart_614979 := by decide
  rcases family_descends (prefixWord ++ tailWord_614979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614996 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_614996 : Nat := 118140960795 + 614996 * 2 ^ 59
def prefixEnd_614996 : Nat := 4983230072969 + 3 ^ 40 * 614996 * 2
def baseEnd_614996 : Nat := 315788548592581059021691

theorem tailTrace_614996 : CollatzResearch.WordTrace tailWord_614996 prefixEnd_614996 315788548592581059021691 := by
  unfold tailWord_614996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215373439990999899904421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14953831253321333199872561 11215373439990999899904421)
  ·
    refine ⟨2102882519998312481232079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11215373439990999899904421 2102882519998312481232079)
    ·
      refine ⟨3154323779997468721848119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102882519998312481232079 3154323779997468721848119)
      ·
        refine ⟨4731485669996203082772179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3154323779997468721848119 4731485669996203082772179)
        ·
          refine ⟨7097228504994304624158269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731485669996203082772179 7097228504994304624158269)
          ·
            refine ⟨2661460689372864234059351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7097228504994304624158269 2661460689372864234059351)
            ·
              refine ⟨3992191034059296351089027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661460689372864234059351 3992191034059296351089027)
              ·
                refine ⟨5988286551088944526633541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992191034059296351089027 5988286551088944526633541)
                ·
                  refine ⟨1122803728329177098743789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5988286551088944526633541 1122803728329177098743789)
                  ·
                    refine ⟨421051398123441412028921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122803728329177098743789 421051398123441412028921)
                    ·
                      refine ⟨315788548592581059021691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421051398123441412028921 315788548592581059021691)
                      ·
                        rfl

theorem cell23_614996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_614996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_614996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_614996 prefixEnd_614996 := by exact prefixLift 614996
  have htrace : WordTrace (prefixWord ++ tailWord_614996) baseStart_614996 baseEnd_614996 := by
    simpa [prefixWord, tailWord_614996, baseEnd_614996] using wordTrace_append hprefix tailTrace_614996
  have hstable : (prefixWord ++ tailWord_614996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614996).length < 2 ^ (prefixWord ++ tailWord_614996).sum := by decide
  have hdescent : baseEnd_614996 < baseStart_614996 := by decide
  rcases family_descends (prefixWord ++ tailWord_614996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615010 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_615010 : Nat := 118140960795 + 615010 * 2 ^ 59
def prefixEnd_615010 : Nat := 4983230072969 + 3 ^ 40 * 615010 * 2
def baseEnd_615010 : Nat := 35088415257971556027403

theorem tailTrace_615010 : CollatzResearch.WordTrace tailWord_615010 prefixEnd_615010 35088415257971556027403 := by
  unfold tailWord_615010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607814375482820047704621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14954171667954186793878989 5607814375482820047704621)
  ·
    refine ⟨2102930390806057517889233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5607814375482820047704621 2102930390806057517889233)
    ·
      refine ⟨1577197793104543138416925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102930390806057517889233 1577197793104543138416925)
      ·
        refine ⟨591449172414203676906347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1577197793104543138416925 591449172414203676906347)
        ·
          refine ⟨887173758621305515359521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591449172414203676906347 887173758621305515359521)
          ·
            refine ⟨665380318965979136519641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887173758621305515359521 665380318965979136519641)
            ·
              refine ⟨499035239224484352389731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665380318965979136519641 499035239224484352389731)
              ·
                refine ⟨748552858836726528584597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499035239224484352389731 748552858836726528584597)
                ·
                  refine ⟨35088415257971556027403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 748552858836726528584597 35088415257971556027403)
                  ·
                    rfl

theorem cell23_615010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_615010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615010 prefixEnd_615010 := by exact prefixLift 615010
  have htrace : WordTrace (prefixWord ++ tailWord_615010) baseStart_615010 baseEnd_615010 := by
    simpa [prefixWord, tailWord_615010, baseEnd_615010] using wordTrace_append hprefix tailTrace_615010
  have hstable : (prefixWord ++ tailWord_615010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615010).length < 2 ^ (prefixWord ++ tailWord_615010).sum := by decide
  have hdescent : baseEnd_615010 < baseStart_615010 := by decide
  rcases family_descends (prefixWord ++ tailWord_615010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615026 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_615026 : Nat := 118140960795 + 615026 * 2 ^ 59
def prefixEnd_615026 : Nat := 4983230072969 + 3 ^ 40 * 615026 * 2
def baseEnd_615026 : Nat := 315803953012215941646553

theorem tailTrace_615026 : CollatzResearch.WordTrace tailWord_615026 prefixEnd_615026 315803953012215941646553 := by
  unfold tailWord_615026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607960267468328730850233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14954560713248876615600621 5607960267468328730850233)
  ·
    refine ⟨4205970200601246548137675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5607960267468328730850233 4205970200601246548137675)
    ·
      refine ⟨6308955300901869822206513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205970200601246548137675 6308955300901869822206513)
      ·
        refine ⟨4731716475676402366654885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6308955300901869822206513 4731716475676402366654885)
        ·
          refine ⟨887196839189325443747791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4731716475676402366654885 887196839189325443747791)
          ·
            refine ⟨1330795258783988165621687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887196839189325443747791 1330795258783988165621687)
            ·
              refine ⟨1996192888175982248432531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330795258783988165621687 1996192888175982248432531)
              ·
                refine ⟨2994289332263973372648797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996192888175982248432531 2994289332263973372648797)
                ·
                  refine ⟨1122858499598990014743299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2994289332263973372648797 1122858499598990014743299)
                  ·
                    refine ⟨1684287749398485022114949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1122858499598990014743299 1684287749398485022114949)
                    ·
                      refine ⟨315803953012215941646553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1684287749398485022114949 315803953012215941646553)
                      ·
                        rfl

theorem cell23_615026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_615026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615026 prefixEnd_615026 := by exact prefixLift 615026
  have htrace : WordTrace (prefixWord ++ tailWord_615026) baseStart_615026 baseEnd_615026 := by
    simpa [prefixWord, tailWord_615026, baseEnd_615026] using wordTrace_append hprefix tailTrace_615026
  have hstable : (prefixWord ++ tailWord_615026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615026).length < 2 ^ (prefixWord ++ tailWord_615026).sum := by decide
  have hdescent : baseEnd_615026 < baseStart_615026 := by decide
  rcases family_descends (prefixWord ++ tailWord_615026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615030 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_615030 : Nat := 118140960795 + 615030 * 2 ^ 59
def prefixEnd_615030 : Nat := 4983230072969 + 3 ^ 40 * 615030 * 2
def baseEnd_615030 : Nat := 315806006934833925996535

theorem tailTrace_615030 : CollatzResearch.WordTrace tailWord_615030 prefixEnd_615030 315806006934833925996535 := by
  unfold tailWord_615030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401999185116176475409159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14954657974572549071031029 1401999185116176475409159)
  ·
    refine ⟨2102998777674264713113739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401999185116176475409159 2102998777674264713113739)
    ·
      refine ⟨3154498166511397069670609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102998777674264713113739 3154498166511397069670609)
      ·
        refine ⟨2365873624883547802252957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3154498166511397069670609 2365873624883547802252957)
        ·
          refine ⟨887202609331330425844859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2365873624883547802252957 887202609331330425844859)
          ·
            refine ⟨1330803913996995638767289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887202609331330425844859 1330803913996995638767289)
            ·
              refine ⟨998102935497746729075467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330803913996995638767289 998102935497746729075467)
              ·
                refine ⟨1497154403246620093613201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998102935497746729075467 1497154403246620093613201)
                ·
                  refine ⟨1122865802434965070209901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497154403246620093613201 1122865802434965070209901)
                  ·
                    refine ⟨421074675913111901328713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122865802434965070209901 421074675913111901328713)
                    ·
                      refine ⟨315806006934833925996535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421074675913111901328713 315806006934833925996535)
                      ·
                        rfl

theorem cell23_615030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_615030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615030 prefixEnd_615030 := by exact prefixLift 615030
  have htrace : WordTrace (prefixWord ++ tailWord_615030) baseStart_615030 baseEnd_615030 := by
    simpa [prefixWord, tailWord_615030, baseEnd_615030] using wordTrace_append hprefix tailTrace_615030
  have hstable : (prefixWord ++ tailWord_615030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615030).length < 2 ^ (prefixWord ++ tailWord_615030).sum := by decide
  have hdescent : baseEnd_615030 < baseStart_615030 := by decide
  rcases family_descends (prefixWord ++ tailWord_615030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_615052 : Nat := 118140960795 + 615052 * 2 ^ 59
def prefixEnd_615052 : Nat := 4983230072969 + 3 ^ 40 * 615052 * 2
def baseEnd_615052 : Nat := 315817303509232839921433

theorem tailTrace_615052 : CollatzResearch.WordTrace tailWord_615052 prefixEnd_615052 315817303509232839921433 := by
  unfold tailWord_615052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216394683889560681923705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14955192911852747575898273 11216394683889560681923705)
  ·
    refine ⟨8412296012917170511442779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11216394683889560681923705 8412296012917170511442779)
    ·
      refine ⟨12618444019375755767164169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8412296012917170511442779 12618444019375755767164169)
      ·
        refine ⟨9463833014531816825373127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12618444019375755767164169 9463833014531816825373127)
        ·
          refine ⟨14195749521797725238059691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463833014531816825373127 14195749521797725238059691)
          ·
            refine ⟨21293624282696587857089537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14195749521797725238059691 21293624282696587857089537)
            ·
              refine ⟨15970218212022440892817153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21293624282696587857089537 15970218212022440892817153)
              ·
                refine ⟨11977663659016830669612865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15970218212022440892817153 11977663659016830669612865)
                ·
                  refine ⟨8983247744262623002209649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11977663659016830669612865 8983247744262623002209649)
                  ·
                    refine ⟨6737435808196967251657237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8983247744262623002209649 6737435808196967251657237)
                    ·
                      refine ⟨315817303509232839921433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6737435808196967251657237 315817303509232839921433)
                      ·
                        rfl

theorem cell23_615052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_615052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615052 prefixEnd_615052 := by exact prefixLift 615052
  have htrace : WordTrace (prefixWord ++ tailWord_615052) baseStart_615052 baseEnd_615052 := by
    simpa [prefixWord, tailWord_615052, baseEnd_615052] using wordTrace_append hprefix tailTrace_615052
  have hstable : (prefixWord ++ tailWord_615052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615052).length < 2 ^ (prefixWord ++ tailWord_615052).sum := by decide
  have hdescent : baseEnd_615052 < baseStart_615052 := by decide
  rcases family_descends (prefixWord ++ tailWord_615052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615076 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_615076 : Nat := 118140960795 + 615076 * 2 ^ 59
def prefixEnd_615076 : Nat := 4983230072969 + 3 ^ 40 * 615076 * 2
def baseEnd_615076 : Nat := 315829627044940746021323

theorem tailTrace_615076 : CollatzResearch.WordTrace tailWord_615076 prefixEnd_615076 315829627044940746021323 := by
  unfold tailWord_615076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216832359846086731360541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14955776479794782308480721 11216832359846086731360541)
  ·
    refine ⟨4206312134942282524260203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11216832359846086731360541 4206312134942282524260203)
    ·
      refine ⟨6309468202413423786390305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206312134942282524260203 6309468202413423786390305)
      ·
        refine ⟨4732101151810067839792729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6309468202413423786390305 4732101151810067839792729)
        ·
          refine ⟨3549075863857550879844547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4732101151810067839792729 3549075863857550879844547)
          ·
            refine ⟨5323613795786326319766821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549075863857550879844547 5323613795786326319766821)
            ·
              refine ⟨998177586709936184956279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5323613795786326319766821 998177586709936184956279)
              ·
                refine ⟨1497266380064904277434419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998177586709936184956279 1497266380064904277434419)
                ·
                  refine ⟨2245899570097356416151629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497266380064904277434419 2245899570097356416151629)
                  ·
                    refine ⟨842212338786508656056861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245899570097356416151629 842212338786508656056861)
                    ·
                      refine ⟨315829627044940746021323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842212338786508656056861 315829627044940746021323)
                      ·
                        rfl

theorem cell23_615076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_615076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615076 prefixEnd_615076 := by exact prefixLift 615076
  have htrace : WordTrace (prefixWord ++ tailWord_615076) baseStart_615076 baseEnd_615076 := by
    simpa [prefixWord, tailWord_615076, baseEnd_615076] using wordTrace_append hprefix tailTrace_615076
  have hstable : (prefixWord ++ tailWord_615076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615076).length < 2 ^ (prefixWord ++ tailWord_615076).sum := by decide
  have hdescent : baseEnd_615076 < baseStart_615076 := by decide
  rcases family_descends (prefixWord ++ tailWord_615076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615094 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_615094 : Nat := 118140960795 + 615094 * 2 ^ 59
def prefixEnd_615094 : Nat := 4983230072969 + 3 ^ 40 * 615094 * 2
def baseEnd_615094 : Nat := 315838869696721675596241

theorem tailTrace_615094 : CollatzResearch.WordTrace tailWord_615094 prefixEnd_615094 315838869696721675596241 := by
  unfold tailWord_615094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402145077101685158554771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14956214155751308357917557 1402145077101685158554771)
  ·
    refine ⟨2103217615652527737832157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402145077101685158554771 2103217615652527737832157)
    ·
      refine ⟨788706605869697901687059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2103217615652527737832157 788706605869697901687059)
      ·
        refine ⟨1183059908804546852530589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788706605869697901687059 1183059908804546852530589)
        ·
          refine ⟨443647465801705069698971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183059908804546852530589 443647465801705069698971)
          ·
            refine ⟨665471198702557604548457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443647465801705069698971 665471198702557604548457)
            ·
              refine ⟨499103399026918203411343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665471198702557604548457 499103399026918203411343)
              ·
                refine ⟨748655098540377305117015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499103399026918203411343 748655098540377305117015)
                ·
                  refine ⟨1122982647810565957675523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748655098540377305117015 1122982647810565957675523)
                  ·
                    refine ⟨1684473971715848936513285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1122982647810565957675523 1684473971715848936513285)
                    ·
                      refine ⟨315838869696721675596241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1684473971715848936513285 315838869696721675596241)
                      ·
                        rfl

theorem cell23_615094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_615094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615094 prefixEnd_615094 := by exact prefixLift 615094
  have htrace : WordTrace (prefixWord ++ tailWord_615094) baseStart_615094 baseEnd_615094 := by
    simpa [prefixWord, tailWord_615094, baseEnd_615094] using wordTrace_append hprefix tailTrace_615094
  have hstable : (prefixWord ++ tailWord_615094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615094).length < 2 ^ (prefixWord ++ tailWord_615094).sum := by decide
  have hdescent : baseEnd_615094 < baseStart_615094 := by decide
  rcases family_descends (prefixWord ++ tailWord_615094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615103 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 1, 3, 2]
def baseStart_615103 : Nat := 118140960795 + 615103 * 2 ^ 59
def prefixEnd_615103 : Nat := 4983230072969 + 3 ^ 40 * 615103 * 2
def baseEnd_615103 : Nat := 315843491022612140383699

theorem tailTrace_615103 : CollatzResearch.WordTrace tailWord_615103 prefixEnd_615103 315843491022612140383699 := by
  unfold tailWord_615103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22434649490594357073953963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14956432993729571382635975 22434649490594357073953963)
  ·
    refine ⟨33651974235891535610930945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22434649490594357073953963 33651974235891535610930945)
    ·
      refine ⟨25238980676918651708198209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33651974235891535610930945 25238980676918651708198209)
      ·
        refine ⟨18929235507688988781148657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25238980676918651708198209 18929235507688988781148657)
        ·
          refine ⟨14196926630766741585861493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18929235507688988781148657 14196926630766741585861493)
          ·
            refine ⟨1330961871634382023674515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14196926630766741585861493 1330961871634382023674515)
            ·
              refine ⟨1996442807451573035511773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330961871634382023674515 1996442807451573035511773)
              ·
                refine ⟨748666052794339888316915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996442807451573035511773 748666052794339888316915)
                ·
                  refine ⟨1122999079191509832475373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748666052794339888316915 1122999079191509832475373)
                  ·
                    refine ⟨421124654696816187178265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122999079191509832475373 421124654696816187178265)
                    ·
                      refine ⟨315843491022612140383699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421124654696816187178265 315843491022612140383699)
                      ·
                        rfl

theorem cell23_615103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_615103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615103 prefixEnd_615103 := by exact prefixLift 615103
  have htrace : WordTrace (prefixWord ++ tailWord_615103) baseStart_615103 baseEnd_615103 := by
    simpa [prefixWord, tailWord_615103, baseEnd_615103] using wordTrace_append hprefix tailTrace_615103
  have hstable : (prefixWord ++ tailWord_615103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615103).length < 2 ^ (prefixWord ++ tailWord_615103).sum := by decide
  have hdescent : baseEnd_615103 < baseStart_615103 := by decide
  rcases family_descends (prefixWord ++ tailWord_615103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615129 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_615129 : Nat := 118140960795 + 615129 * 2 ^ 59
def prefixEnd_615129 : Nat := 4983230072969 + 3 ^ 40 * 615129 * 2
def baseEnd_615129 : Nat := 315856841519629038658579

theorem tailTrace_615129 : CollatzResearch.WordTrace tailWord_615129 prefixEnd_615129 315856841519629038658579 := by
  unfold tailWord_615129
  simp only [CollatzResearch.WordTrace]
  refine ⟨22435597788500163514400441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14957065192333442342933627 22435597788500163514400441)
  ·
    refine ⟨16826698341375122635800331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22435597788500163514400441 16826698341375122635800331)
    ·
      refine ⟨25240047512062683953700497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826698341375122635800331 25240047512062683953700497)
      ·
        refine ⟨18930035634047012965275373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25240047512062683953700497 18930035634047012965275373)
        ·
          refine ⟨7098763362767629861978265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18930035634047012965275373 7098763362767629861978265)
          ·
            refine ⟨5324072522075722396483699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7098763362767629861978265 5324072522075722396483699)
            ·
              refine ⟨7986108783113583594725549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324072522075722396483699 7986108783113583594725549)
              ·
                refine ⟨2994790793667593848022081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7986108783113583594725549 2994790793667593848022081)
                ·
                  refine ⟨2246093095250695386016561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994790793667593848022081 2246093095250695386016561)
                  ·
                    refine ⟨1684569821438021539512421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2246093095250695386016561 1684569821438021539512421)
                    ·
                      refine ⟨315856841519629038658579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1684569821438021539512421 315856841519629038658579)
                      ·
                        rfl

theorem cell23_615129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_615129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615129 prefixEnd_615129 := by exact prefixLift 615129
  have htrace : WordTrace (prefixWord ++ tailWord_615129) baseStart_615129 baseEnd_615129 := by
    simpa [prefixWord, tailWord_615129, baseEnd_615129] using wordTrace_append hprefix tailTrace_615129
  have hstable : (prefixWord ++ tailWord_615129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615129).length < 2 ^ (prefixWord ++ tailWord_615129).sum := by decide
  have hdescent : baseEnd_615129 < baseStart_615129 := by decide
  rcases family_descends (prefixWord ++ tailWord_615129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615260 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_615260 : Nat := 118140960795 + 615260 * 2 ^ 59
def prefixEnd_615260 : Nat := 4983230072969 + 3 ^ 40 * 615260 * 2
def baseEnd_615260 : Nat := 315924107485368026120477

theorem tailTrace_615260 : CollatzResearch.WordTrace tailWord_615260 prefixEnd_615260 315924107485368026120477 := by
  unfold tailWord_615260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220187875512786443709617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14960250500683715258279489 11220187875512786443709617)
  ·
    refine ⟨8415140906634589832782213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11220187875512786443709617 8415140906634589832782213)
    ·
      refine ⟨1577838919993985593646665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8415140906634589832782213 1577838919993985593646665)
      ·
        refine ⟨1183379189995489195234999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577838919993985593646665 1183379189995489195234999)
        ·
          refine ⟨1775068784993233792852499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183379189995489195234999 1775068784993233792852499)
          ·
            refine ⟨2662603177489850689278749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775068784993233792852499 2662603177489850689278749)
            ·
              refine ⟨998476191558694008479531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662603177489850689278749 998476191558694008479531)
              ·
                refine ⟨1497714287338041012719297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998476191558694008479531 1497714287338041012719297)
                ·
                  refine ⟨1123285715503530759539473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497714287338041012719297 1123285715503530759539473)
                  ·
                    refine ⟨842464286627648069654605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1123285715503530759539473 842464286627648069654605)
                    ·
                      refine ⟨315924107485368026120477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842464286627648069654605 315924107485368026120477)
                      ·
                        rfl

theorem cell23_615260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_615260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615260 prefixEnd_615260 := by exact prefixLift 615260
  have htrace : WordTrace (prefixWord ++ tailWord_615260) baseStart_615260 baseEnd_615260 := by
    simpa [prefixWord, tailWord_615260, baseEnd_615260] using wordTrace_append hprefix tailTrace_615260
  have hstable : (prefixWord ++ tailWord_615260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615260).length < 2 ^ (prefixWord ++ tailWord_615260).sum := by decide
  have hdescent : baseEnd_615260 < baseStart_615260 := by decide
  rcases family_descends (prefixWord ++ tailWord_615260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615283 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 2, 3, 2]
def baseStart_615283 : Nat := 118140960795 + 615283 * 2 ^ 59
def prefixEnd_615283 : Nat := 4983230072969 + 3 ^ 40 * 615283 * 2
def baseEnd_615283 : Nat := 315935917540421436132871

theorem tailTrace_615283 : CollatzResearch.WordTrace tailWord_615283 prefixEnd_615283 315935917540421436132871 := by
  unfold tailWord_615283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441214629942247815506503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14960809753294831877004335 22441214629942247815506503)
  ·
    refine ⟨33661821944913371723259755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22441214629942247815506503 33661821944913371723259755)
    ·
      refine ⟨50492732917370057584889633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33661821944913371723259755 50492732917370057584889633)
      ·
        refine ⟨37869549688027543188667225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50492732917370057584889633 37869549688027543188667225)
        ·
          refine ⟨28402162266020657391500419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37869549688027543188667225 28402162266020657391500419)
          ·
            refine ⟨42603243399030986087250629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28402162266020657391500419 42603243399030986087250629)
            ·
              refine ⟨7988108137318309891359493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42603243399030986087250629 7988108137318309891359493)
              ·
                refine ⟨1497770275747183104629905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7988108137318309891359493 1497770275747183104629905)
                ·
                  refine ⟨1123327706810387328472429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497770275747183104629905 1123327706810387328472429)
                  ·
                    refine ⟨421247890053895248177161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123327706810387328472429 421247890053895248177161)
                    ·
                      refine ⟨315935917540421436132871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421247890053895248177161 315935917540421436132871)
                      ·
                        rfl

theorem cell23_615283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 3, 2].length) (baseStart_615283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615283 prefixEnd_615283 := by exact prefixLift 615283
  have htrace : WordTrace (prefixWord ++ tailWord_615283) baseStart_615283 baseEnd_615283 := by
    simpa [prefixWord, tailWord_615283, baseEnd_615283] using wordTrace_append hprefix tailTrace_615283
  have hstable : (prefixWord ++ tailWord_615283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615283).length < 2 ^ (prefixWord ++ tailWord_615283).sum := by decide
  have hdescent : baseEnd_615283 < baseStart_615283 := by decide
  rcases family_descends (prefixWord ++ tailWord_615283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615296 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_615296 : Nat := 118140960795 + 615296 * 2 ^ 59
def prefixEnd_615296 : Nat := 4983230072969 + 3 ^ 40 * 615296 * 2
def baseEnd_615296 : Nat := 315942592788929885270311

theorem tailTrace_615296 : CollatzResearch.WordTrace tailWord_615296 prefixEnd_615296 315942592788929885270311 := by
  unfold tailWord_615296
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220844389447575517864871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14961125852596767357153161 11220844389447575517864871)
  ·
    refine ⟨16831266584171363276797307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11220844389447575517864871 16831266584171363276797307)
    ·
      refine ⟨25246899876257044915195961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831266584171363276797307 25246899876257044915195961)
      ·
        refine ⟨18935174907192783686396971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25246899876257044915195961 18935174907192783686396971)
        ·
          refine ⟨28402762360789175529595457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18935174907192783686396971 28402762360789175529595457)
          ·
            refine ⟨21302071770591881647196593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28402762360789175529595457 21302071770591881647196593)
            ·
              refine ⟨15976553827943911235397445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21302071770591881647196593 15976553827943911235397445)
              ·
                refine ⟨2995603842739483356637021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15976553827943911235397445 2995603842739483356637021)
                ·
                  refine ⟨1123351441027306258738883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2995603842739483356637021 1123351441027306258738883)
                  ·
                    refine ⟨1685027161540959388108325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123351441027306258738883 1685027161540959388108325)
                    ·
                      refine ⟨315942592788929885270311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1685027161540959388108325 315942592788929885270311)
                      ·
                        rfl

theorem cell23_615296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_615296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615296 prefixEnd_615296 := by exact prefixLift 615296
  have htrace : WordTrace (prefixWord ++ tailWord_615296) baseStart_615296 baseEnd_615296 := by
    simpa [prefixWord, tailWord_615296, baseEnd_615296] using wordTrace_append hprefix tailTrace_615296
  have hstable : (prefixWord ++ tailWord_615296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615296).length < 2 ^ (prefixWord ++ tailWord_615296).sum := by decide
  have hdescent : baseEnd_615296 < baseStart_615296 := by decide
  rcases family_descends (prefixWord ++ tailWord_615296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615330 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_615330 : Nat := 118140960795 + 615330 * 2 ^ 59
def prefixEnd_615330 : Nat := 4983230072969 + 3 ^ 40 * 615330 * 2
def baseEnd_615330 : Nat := 315960051131182752245155

theorem tailTrace_615330 : CollatzResearch.WordTrace tailWord_615330 prefixEnd_615330 315960051131182752245155 := by
  unfold tailWord_615330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610732215192993710616861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14961952573847983228311629 5610732215192993710616861)
  ·
    refine ⟨2104024580697372641481323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5610732215192993710616861 2104024580697372641481323)
    ·
      refine ⟨3156036871046058962221985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104024580697372641481323 3156036871046058962221985)
      ·
        refine ⟨2367027653284544221666489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156036871046058962221985 2367027653284544221666489)
        ·
          refine ⟨1775270739963408166249867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2367027653284544221666489 1775270739963408166249867)
          ·
            refine ⟨2662906109945112249374801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775270739963408166249867 2662906109945112249374801)
            ·
              refine ⟨1997179582458834187031101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2662906109945112249374801 1997179582458834187031101)
              ·
                refine ⟨748942343422062820136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1997179582458834187031101 748942343422062820136663)
                ·
                  refine ⟨1123413515133094230204995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748942343422062820136663 1123413515133094230204995)
                  ·
                    refine ⟨1685120272699641345307493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123413515133094230204995 1685120272699641345307493)
                    ·
                      refine ⟨315960051131182752245155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1685120272699641345307493 315960051131182752245155)
                      ·
                        rfl

theorem cell23_615330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_615330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615330 prefixEnd_615330 := by exact prefixLift 615330
  have htrace : WordTrace (prefixWord ++ tailWord_615330) baseStart_615330 baseEnd_615330 := by
    simpa [prefixWord, tailWord_615330, baseEnd_615330] using wordTrace_append hprefix tailTrace_615330
  have hstable : (prefixWord ++ tailWord_615330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615330).length < 2 ^ (prefixWord ++ tailWord_615330).sum := by decide
  have hdescent : baseEnd_615330 < baseStart_615330 := by decide
  rcases family_descends (prefixWord ++ tailWord_615330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615341 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_615341 : Nat := 118140960795 + 615341 * 2 ^ 59
def prefixEnd_615341 : Nat := 4983230072969 + 3 ^ 40 * 615341 * 2
def baseEnd_615341 : Nat := 315965699418382209207605

theorem tailTrace_615341 : CollatzResearch.WordTrace tailWord_615341 prefixEnd_615341 315965699418382209207605 := by
  unfold tailWord_615341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22443330063732123721117877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14962220042488082480745251 22443330063732123721117877)
  ·
    refine ⟨2104062193474886598854801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22443330063732123721117877 2104062193474886598854801)
    ·
      refine ⟨1578046645106164949141101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2104062193474886598854801 1578046645106164949141101)
      ·
        refine ⟨591767491914811855927913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1578046645106164949141101 591767491914811855927913)
        ·
          refine ⟨443825618936108891945935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591767491914811855927913 443825618936108891945935)
          ·
            refine ⟨665738428404163337918903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443825618936108891945935 665738428404163337918903)
            ·
              refine ⟨998607642606245006878355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665738428404163337918903 998607642606245006878355)
              ·
                refine ⟨1497911463909367510317533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998607642606245006878355 1497911463909367510317533)
                ·
                  refine ⟨561716798966012816369075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1497911463909367510317533 561716798966012816369075)
                  ·
                    refine ⟨842575198449019224553613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 561716798966012816369075 842575198449019224553613)
                    ·
                      refine ⟨315965699418382209207605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842575198449019224553613 315965699418382209207605)
                      ·
                        rfl

theorem cell23_615341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_615341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615341 prefixEnd_615341 := by exact prefixLift 615341
  have htrace : WordTrace (prefixWord ++ tailWord_615341) baseStart_615341 baseEnd_615341 := by
    simpa [prefixWord, tailWord_615341, baseEnd_615341] using wordTrace_append hprefix tailTrace_615341
  have hstable : (prefixWord ++ tailWord_615341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615341).length < 2 ^ (prefixWord ++ tailWord_615341).sum := by decide
  have hdescent : baseEnd_615341 < baseStart_615341 := by decide
  rcases family_descends (prefixWord ++ tailWord_615341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615364 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_615364 : Nat := 118140960795 + 615364 * 2 ^ 59
def prefixEnd_615364 : Nat := 4983230072969 + 3 ^ 40 * 615364 * 2
def baseEnd_615364 : Nat := 315977509473435619219999

theorem tailTrace_615364 : CollatzResearch.WordTrace tailWord_615364 prefixEnd_615364 315977509473435619219999 := by
  unfold tailWord_615364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222084471324399324602573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14962779295099199099470097 11222084471324399324602573)
  ·
    refine ⟨4208281676746649746725965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11222084471324399324602573 4208281676746649746725965)
    ·
      refine ⟨1578105628779993655022237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4208281676746649746725965 1578105628779993655022237)
      ·
        refine ⟨591789610792497620633339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1578105628779993655022237 591789610792497620633339)
        ·
          refine ⟨887684416188746430950009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591789610792497620633339 887684416188746430950009)
          ·
            refine ⟨665763312141559823212507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887684416188746430950009 665763312141559823212507)
            ·
              refine ⟨998644968212339734818761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665763312141559823212507 998644968212339734818761)
              ·
                refine ⟨748983726159254801114071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998644968212339734818761 748983726159254801114071)
                ·
                  refine ⟨1123475589238882201671107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748983726159254801114071 1123475589238882201671107)
                  ·
                    refine ⟨1685213383858323302506661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123475589238882201671107 1685213383858323302506661)
                    ·
                      refine ⟨315977509473435619219999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1685213383858323302506661 315977509473435619219999)
                      ·
                        rfl

theorem cell23_615364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_615364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615364 prefixEnd_615364 := by exact prefixLift 615364
  have htrace : WordTrace (prefixWord ++ tailWord_615364) baseStart_615364 baseEnd_615364 := by
    simpa [prefixWord, tailWord_615364, baseEnd_615364] using wordTrace_append hprefix tailTrace_615364
  have hstable : (prefixWord ++ tailWord_615364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615364).length < 2 ^ (prefixWord ++ tailWord_615364).sum := by decide
  have hdescent : baseEnd_615364 < baseStart_615364 := by decide
  rcases family_descends (prefixWord ++ tailWord_615364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615380 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_615380 : Nat := 118140960795 + 615380 * 2 ^ 59
def prefixEnd_615380 : Nat := 4983230072969 + 3 ^ 40 * 615380 * 2
def baseEnd_615380 : Nat := 315985725163907556619925

theorem tailTrace_615380 : CollatzResearch.WordTrace tailWord_615380 prefixEnd_615380 315985725163907556619925 := by
  unfold tailWord_615380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222376255295416690893797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14963168340393888921191729 11222376255295416690893797)
  ·
    refine ⟨2104195547867890629542587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11222376255295416690893797 2104195547867890629542587)
    ·
      refine ⟨3156293321801835944313881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104195547867890629542587 3156293321801835944313881)
      ·
        refine ⟨2367219991351376958235411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156293321801835944313881 2367219991351376958235411)
        ·
          refine ⟨3550829987027065437353117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367219991351376958235411 3550829987027065437353117)
          ·
            refine ⟨1331561245135149539007419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3550829987027065437353117 1331561245135149539007419)
            ·
              refine ⟨1997341867702724308511129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331561245135149539007419 1997341867702724308511129)
              ·
                refine ⟨1498006400777043231383347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997341867702724308511129 1498006400777043231383347)
                ·
                  refine ⟨2247009601165564847075021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498006400777043231383347 2247009601165564847075021)
                  ·
                    refine ⟨842628600437086817653133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247009601165564847075021 842628600437086817653133)
                    ·
                      refine ⟨315985725163907556619925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842628600437086817653133 315985725163907556619925)
                      ·
                        rfl

theorem cell23_615380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_615380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615380 prefixEnd_615380 := by exact prefixLift 615380
  have htrace : WordTrace (prefixWord ++ tailWord_615380) baseStart_615380 baseEnd_615380 := by
    simpa [prefixWord, tailWord_615380, baseEnd_615380] using wordTrace_append hprefix tailTrace_615380
  have hstable : (prefixWord ++ tailWord_615380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615380).length < 2 ^ (prefixWord ++ tailWord_615380).sum := by decide
  have hdescent : baseEnd_615380 < baseStart_615380 := by decide
  rcases family_descends (prefixWord ++ tailWord_615380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615420 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_615420 : Nat := 118140960795 + 615420 * 2 ^ 59
def prefixEnd_615420 : Nat := 4983230072969 + 3 ^ 40 * 615420 * 2
def baseEnd_615420 : Nat := 316006264390087400119741

theorem tailTrace_615420 : CollatzResearch.WordTrace tailWord_615420 prefixEnd_615420 316006264390087400119741 := by
  unfold tailWord_615420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223105715222960106621857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14964140953630613475495809 11223105715222960106621857)
  ·
    refine ⟨8417329286417220079966393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11223105715222960106621857 8417329286417220079966393)
    ·
      refine ⟨6312996964812915059974795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8417329286417220079966393 6312996964812915059974795)
      ·
        refine ⟨9469495447219372589962193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312996964812915059974795 9469495447219372589962193)
        ·
          refine ⟨7102121585414529442471645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9469495447219372589962193 7102121585414529442471645)
          ·
            refine ⟨2663295594530448540926867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7102121585414529442471645 2663295594530448540926867)
            ·
              refine ⟨3994943391795672811390301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663295594530448540926867 3994943391795672811390301)
              ·
                refine ⟨1498103771923377304271363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994943391795672811390301 1498103771923377304271363)
                ·
                  refine ⟨2247155657885065956407045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498103771923377304271363 2247155657885065956407045)
                  ·
                    refine ⟨421341685853449866826321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247155657885065956407045 421341685853449866826321)
                    ·
                      refine ⟨316006264390087400119741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421341685853449866826321 316006264390087400119741)
                      ·
                        rfl

theorem cell23_615420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_615420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615420 prefixEnd_615420 := by exact prefixLift 615420
  have htrace : WordTrace (prefixWord ++ tailWord_615420) baseStart_615420 baseEnd_615420 := by
    simpa [prefixWord, tailWord_615420, baseEnd_615420] using wordTrace_append hprefix tailTrace_615420
  have hstable : (prefixWord ++ tailWord_615420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615420).length < 2 ^ (prefixWord ++ tailWord_615420).sum := by decide
  have hdescent : baseEnd_615420 < baseStart_615420 := by decide
  rcases family_descends (prefixWord ++ tailWord_615420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615460 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 7]
def baseStart_615460 : Nat := 118140960795 + 615460 * 2 ^ 59
def prefixEnd_615460 : Nat := 4983230072969 + 3 ^ 40 * 615460 * 2
def baseEnd_615460 : Nat := 35114089290696360402173

theorem tailTrace_615460 : CollatzResearch.WordTrace tailWord_615460 prefixEnd_615460 35114089290696360402173 := by
  unfold tailWord_615460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223835175150503522349917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14965113566867338029799889 11223835175150503522349917)
  ·
    refine ⟨4208938190681438820881219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11223835175150503522349917 4208938190681438820881219)
    ·
      refine ⟨6313407286022158231321829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208938190681438820881219 6313407286022158231321829)
      ·
        refine ⟨1183763866129154668372843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6313407286022158231321829 1183763866129154668372843)
        ·
          refine ⟨1775645799193732002559265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183763866129154668372843 1775645799193732002559265)
          ·
            refine ⟨1331734349395299001919449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775645799193732002559265 1331734349395299001919449)
            ·
              refine ⟨998800762046474251439587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331734349395299001919449 998800762046474251439587)
              ·
                refine ⟨1498201143069711377159381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998800762046474251439587 1498201143069711377159381)
                ·
                  refine ⟨35114089290696360402173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1498201143069711377159381 35114089290696360402173)
                  ·
                    rfl

theorem cell23_615460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_615460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615460 prefixEnd_615460 := by exact prefixLift 615460
  have htrace : WordTrace (prefixWord ++ tailWord_615460) baseStart_615460 baseEnd_615460 := by
    simpa [prefixWord, tailWord_615460, baseEnd_615460] using wordTrace_append hprefix tailTrace_615460
  have hstable : (prefixWord ++ tailWord_615460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615460).length < 2 ^ (prefixWord ++ tailWord_615460).sum := by decide
  have hdescent : baseEnd_615460 < baseStart_615460 := by decide
  rcases family_descends (prefixWord ++ tailWord_615460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615470 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_615470 : Nat := 118140960795 + 615470 * 2 ^ 59
def prefixEnd_615470 : Nat := 4983230072969 + 3 ^ 40 * 615470 * 2
def baseEnd_615470 : Nat := 316031938422812204494511

theorem tailTrace_615470 : CollatzResearch.WordTrace tailWord_615470 prefixEnd_615470 316031938422812204494511 := by
  unfold tailWord_615470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806004385033097344070483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14965356720176519168375909 2806004385033097344070483)
  ·
    refine ⟨4209006577549646016105725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806004385033097344070483 4209006577549646016105725)
    ·
      refine ⟨1578377466581117256039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4209006577549646016105725 1578377466581117256039647)
      ·
        refine ⟨2367566199871675884059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578377466581117256039647 2367566199871675884059471)
        ·
          refine ⟨3551349299807513826089207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367566199871675884059471 3551349299807513826089207)
          ·
            refine ⟨5327023949711270739133811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551349299807513826089207 5327023949711270739133811)
            ·
              refine ⟨7990535924566906108700717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327023949711270739133811 7990535924566906108700717)
              ·
                refine ⟨2996450971712589790762769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990535924566906108700717 2996450971712589790762769)
                ·
                  refine ⟨2247338228784442343072077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996450971712589790762769 2247338228784442343072077)
                  ·
                    refine ⟨842751835794165878652029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247338228784442343072077 842751835794165878652029)
                    ·
                      refine ⟨316031938422812204494511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842751835794165878652029 316031938422812204494511)
                      ·
                        rfl

theorem cell23_615470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_615470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615470 prefixEnd_615470 := by exact prefixLift 615470
  have htrace : WordTrace (prefixWord ++ tailWord_615470) baseStart_615470 baseEnd_615470 := by
    simpa [prefixWord, tailWord_615470, baseEnd_615470] using wordTrace_append hprefix tailTrace_615470
  have hstable : (prefixWord ++ tailWord_615470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615470).length < 2 ^ (prefixWord ++ tailWord_615470).sum := by decide
  have hdescent : baseEnd_615470 < baseStart_615470 := by decide
  rcases family_descends (prefixWord ++ tailWord_615470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
