import V185TrunkScan23Chunk1284

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7611797 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_7611797 : Nat := 118140960795 + 7611797 * 2 ^ 59
def prefixEnd_7611797 : Nat := 4983230072969 + 3 ^ 40 * 7611797 * 2
def baseEnd_7611797 : Nat := 3908510505451460542931489

theorem tailTrace_7611797 : CollatzResearch.WordTrace tailWord_7611797 prefixEnd_7611797 3908510505451460542931489 := by
  unfold tailWord_7611797
  simp only [CollatzResearch.WordTrace]
  refine ⟨277625044404766935275105645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185083362936511290183403763 277625044404766935275105645)
  ·
    refine ⟨104109391651787600728164617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277625044404766935275105645 104109391651787600728164617)
    ·
      refine ⟨78082043738840700546123463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104109391651787600728164617 78082043738840700546123463)
      ·
        refine ⟨117123065608261050819185195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78082043738840700546123463 117123065608261050819185195)
        ·
          refine ⟨175684598412391576228777793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117123065608261050819185195 175684598412391576228777793)
          ·
            refine ⟨131763448809293682171583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175684598412391576228777793 131763448809293682171583345)
            ·
              refine ⟨98822586606970261628687509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131763448809293682171583345 98822586606970261628687509)
              ·
                refine ⟨4632308747201731013844727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98822586606970261628687509 4632308747201731013844727)
                ·
                  refine ⟨6948463120802596520767091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632308747201731013844727 6948463120802596520767091)
                  ·
                    refine ⟨10422694681203894781150637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948463120802596520767091 10422694681203894781150637)
                    ·
                      refine ⟨3908510505451460542931489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422694681203894781150637 3908510505451460542931489)
                      ·
                        rfl

theorem cell23_7611797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_7611797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611797 prefixEnd_7611797 := by exact prefixLift 7611797
  have htrace : WordTrace (prefixWord ++ tailWord_7611797) baseStart_7611797 baseEnd_7611797 := by
    simpa [prefixWord, tailWord_7611797, baseEnd_7611797] using wordTrace_append hprefix tailTrace_7611797
  have hstable : (prefixWord ++ tailWord_7611797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611797).length < 2 ^ (prefixWord ++ tailWord_7611797).sum := by decide
  have hdescent : baseEnd_7611797 < baseStart_7611797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611804 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 6]
def baseStart_7611804 : Nat := 118140960795 + 7611804 * 2 ^ 59
def prefixEnd_7611804 : Nat := 4983230072969 + 3 ^ 40 * 7611804 * 2
def baseEnd_7611804 : Nat := 434279344424004668393773

theorem tailTrace_7611804 : CollatzResearch.WordTrace tailWord_7611804 prefixEnd_7611804 434279344424004668393773 := by
  unfold tailWord_7611804
  simp only [CollatzResearch.WordTrace]
  refine ⟨138812649857870787735305233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185083533143827716980406977 138812649857870787735305233)
  ·
    refine ⟨104109487393403090801478925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138812649857870787735305233 104109487393403090801478925)
    ·
      refine ⟨39041057772526159050554597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104109487393403090801478925 39041057772526159050554597)
      ·
        refine ⟨7320198332348654821978987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39041057772526159050554597 7320198332348654821978987)
        ·
          refine ⟨10980297498522982232968481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320198332348654821978987 10980297498522982232968481)
          ·
            refine ⟨8235223123892236674726361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980297498522982232968481 8235223123892236674726361)
            ·
              refine ⟨6176417342919177506044771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235223123892236674726361 6176417342919177506044771)
              ·
                refine ⟨9264626014378766259067157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176417342919177506044771 9264626014378766259067157)
                ·
                  refine ⟨434279344424004668393773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9264626014378766259067157 434279344424004668393773)
                  ·
                    rfl

theorem cell23_7611804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_7611804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611804 prefixEnd_7611804 := by exact prefixLift 7611804
  have htrace : WordTrace (prefixWord ++ tailWord_7611804) baseStart_7611804 baseEnd_7611804 := by
    simpa [prefixWord, tailWord_7611804, baseEnd_7611804] using wordTrace_append hprefix tailTrace_7611804
  have hstable : (prefixWord ++ tailWord_7611804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611804).length < 2 ^ (prefixWord ++ tailWord_7611804).sum := by decide
  have hdescent : baseEnd_7611804 < baseStart_7611804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611813 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_7611813 : Nat := 118140960795 + 7611813 * 2 ^ 59
def prefixEnd_7611813 : Nat := 4983230072969 + 3 ^ 40 * 7611813 * 2
def baseEnd_7611813 : Nat := 1302839573713977493443805

theorem tailTrace_7611813 : CollatzResearch.WordTrace tailWord_7611813 prefixEnd_7611813 1302839573713977493443805 := by
  unfold tailWord_7611813
  simp only [CollatzResearch.WordTrace]
  refine ⟨277625627972708970007688093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185083751981805980005125395 277625627972708970007688093)
  ·
    refine ⟨104109610489765863752883035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277625627972708970007688093 104109610489765863752883035)
    ·
      refine ⟨156164415734648795629324553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104109610489765863752883035 156164415734648795629324553)
      ·
        refine ⟨117123311800986596721993415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156164415734648795629324553 117123311800986596721993415)
        ·
          refine ⟨175684967701479895082990123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117123311800986596721993415 175684967701479895082990123)
          ·
            refine ⟨263527451552219842624485185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175684967701479895082990123 263527451552219842624485185)
            ·
              refine ⟨197645588664164881968363889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263527451552219842624485185 197645588664164881968363889)
              ·
                refine ⟨148234191498123661476272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197645588664164881968363889 148234191498123661476272917)
                ·
                  refine ⟨6948477726474546631700293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148234191498123661476272917 6948477726474546631700293)
                  ·
                    refine ⟨1302839573713977493443805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948477726474546631700293 1302839573713977493443805)
                    ·
                      rfl

theorem cell23_7611813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_7611813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611813 prefixEnd_7611813 := by exact prefixLift 7611813
  have htrace : WordTrace (prefixWord ++ tailWord_7611813) baseStart_7611813 baseEnd_7611813 := by
    simpa [prefixWord, tailWord_7611813, baseEnd_7611813] using wordTrace_append hprefix tailTrace_7611813
  have hstable : (prefixWord ++ tailWord_7611813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611813).length < 2 ^ (prefixWord ++ tailWord_7611813).sum := by decide
  have hdescent : baseEnd_7611813 < baseStart_7611813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611820 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_7611820 : Nat := 118140960795 + 7611820 * 2 ^ 59
def prefixEnd_7611820 : Nat := 4983230072969 + 3 ^ 40 * 7611820 * 2
def baseEnd_7611820 : Nat := 3908522315506513952943883

theorem tailTrace_7611820 : CollatzResearch.WordTrace tailWord_7611820 prefixEnd_7611820 3908522315506513952943883 := by
  unfold tailWord_7611820
  simp only [CollatzResearch.WordTrace]
  refine ⟨138812941641841805101596457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185083922189122406802128609 138812941641841805101596457)
  ·
    refine ⟨104109706231381353826197343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138812941641841805101596457 104109706231381353826197343)
    ·
      refine ⟨156164559347072030739296015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104109706231381353826197343 156164559347072030739296015)
      ·
        refine ⟨234246839020608046108944023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156164559347072030739296015 234246839020608046108944023)
        ·
          refine ⟨351370258530912069163416035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234246839020608046108944023 351370258530912069163416035)
          ·
            refine ⟨527055387796368103745124053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351370258530912069163416035 527055387796368103745124053)
            ·
              refine ⟨12352860651477377431526345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 527055387796368103745124053 12352860651477377431526345)
              ·
                refine ⟨9264645488608033073644759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12352860651477377431526345 9264645488608033073644759)
                ·
                  refine ⟨13896968232912049610467139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264645488608033073644759 13896968232912049610467139)
                  ·
                    refine ⟨20845452349368074415700709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13896968232912049610467139 20845452349368074415700709)
                    ·
                      refine ⟨3908522315506513952943883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20845452349368074415700709 3908522315506513952943883)
                      ·
                        rfl

theorem cell23_7611820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_7611820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611820 prefixEnd_7611820 := by exact prefixLift 7611820
  have htrace : WordTrace (prefixWord ++ tailWord_7611820) baseStart_7611820 baseEnd_7611820 := by
    simpa [prefixWord, tailWord_7611820, baseEnd_7611820] using wordTrace_append hprefix tailTrace_7611820
  have hstable : (prefixWord ++ tailWord_7611820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611820).length < 2 ^ (prefixWord ++ tailWord_7611820).sum := by decide
  have hdescent : baseEnd_7611820 < baseStart_7611820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611837 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7611837 : Nat := 118140960795 + 7611837 * 2 ^ 59
def prefixEnd_7611837 : Nat := 4983230072969 + 3 ^ 40 * 7611837 * 2
def baseEnd_7611837 : Nat := 3908531044677640386431305

theorem tailTrace_7611837 : CollatzResearch.WordTrace tailWord_7611837 prefixEnd_7611837 3908531044677640386431305 := by
  unfold tailWord_7611837
  simp only [CollatzResearch.WordTrace]
  refine ⟨277626503324622022106561765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185084335549748014737707843 277626503324622022106561765)
  ·
    refine ⟨52054969373366629144980331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277626503324622022106561765 52054969373366629144980331)
    ·
      refine ⟨78082454060049943717470497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52054969373366629144980331 78082454060049943717470497)
      ·
        refine ⟨58561840545037457788102873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78082454060049943717470497 58561840545037457788102873)
        ·
          refine ⟨43921380408778093341077155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58561840545037457788102873 43921380408778093341077155)
          ·
            refine ⟨65882070613167140011615733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43921380408778093341077155 65882070613167140011615733)
            ·
              refine ⟨6176444119984419376088975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65882070613167140011615733 6176444119984419376088975)
              ·
                refine ⟨9264666179976629064133463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176444119984419376088975 9264666179976629064133463)
                ·
                  refine ⟨13896999269964943596200195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264666179976629064133463 13896999269964943596200195)
                  ·
                    refine ⟨20845498904947415394300293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13896999269964943596200195 20845498904947415394300293)
                    ·
                      refine ⟨3908531044677640386431305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20845498904947415394300293 3908531044677640386431305)
                      ·
                        rfl

theorem cell23_7611837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7611837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611837 prefixEnd_7611837 := by exact prefixLift 7611837
  have htrace : WordTrace (prefixWord ++ tailWord_7611837) baseStart_7611837 baseEnd_7611837 := by
    simpa [prefixWord, tailWord_7611837, baseEnd_7611837] using wordTrace_append hprefix tailTrace_7611837
  have hstable : (prefixWord ++ tailWord_7611837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611837).length < 2 ^ (prefixWord ++ tailWord_7611837).sum := by decide
  have hdescent : baseEnd_7611837 < baseStart_7611837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611840 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_7611840 : Nat := 118140960795 + 7611840 * 2 ^ 59
def prefixEnd_7611840 : Nat := 4983230072969 + 3 ^ 40 * 7611840 * 2
def baseEnd_7611840 : Nat := 3908532585119603874693791

theorem tailTrace_7611840 : CollatzResearch.WordTrace tailWord_7611840 prefixEnd_7611840 3908532585119603874693791 := by
  unfold tailWord_7611840
  simp only [CollatzResearch.WordTrace]
  refine ⟨138813306371805576809460487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185084408495740769079280649 138813306371805576809460487)
  ·
    refine ⟨208219959557708365214190731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138813306371805576809460487 208219959557708365214190731)
    ·
      refine ⟨312329939336562547821286097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208219959557708365214190731 312329939336562547821286097)
      ·
        refine ⟨234247454502421910865964573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312329939336562547821286097 234247454502421910865964573)
        ·
          refine ⟨87842795438408216574736715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234247454502421910865964573 87842795438408216574736715)
          ·
            refine ⟨131764193157612324862105073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87842795438408216574736715 131764193157612324862105073)
            ·
              refine ⟨98823144868209243646578805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131764193157612324862105073 98823144868209243646578805)
              ·
                refine ⟨9264669831394616591866763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98823144868209243646578805 9264669831394616591866763)
                ·
                  refine ⟨13897004747091924887800145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264669831394616591866763 13897004747091924887800145)
                  ·
                    refine ⟨10422753560318943665850109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13897004747091924887800145 10422753560318943665850109)
                    ·
                      refine ⟨3908532585119603874693791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422753560318943665850109 3908532585119603874693791)
                      ·
                        rfl

theorem cell23_7611840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_7611840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611840 prefixEnd_7611840 := by exact prefixLift 7611840
  have htrace : WordTrace (prefixWord ++ tailWord_7611840) baseStart_7611840 baseEnd_7611840 := by
    simpa [prefixWord, tailWord_7611840, baseEnd_7611840] using wordTrace_append hprefix tailTrace_7611840
  have hstable : (prefixWord ++ tailWord_7611840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611840).length < 2 ^ (prefixWord ++ tailWord_7611840).sum := by decide
  have hdescent : baseEnd_7611840 < baseStart_7611840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611842 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7611842 : Nat := 118140960795 + 7611842 * 2 ^ 59
def prefixEnd_7611842 : Nat := 4983230072969 + 3 ^ 40 * 7611842 * 2
def baseEnd_7611842 : Nat := 1302844537360304288956261

theorem tailTrace_7611842 : CollatzResearch.WordTrace tailWord_7611842 prefixEnd_7611842 1302844537360304288956261 := by
  unfold tailWord_7611842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69406671422400976990123445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185084457126402605306995853 69406671422400976990123445)
  ·
    refine ⟨6506875445850091592824073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69406671422400976990123445 6506875445850091592824073)
    ·
      refine ⟨4880156584387568694618055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506875445850091592824073 4880156584387568694618055)
      ·
        refine ⟨7320234876581353041927083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880156584387568694618055 7320234876581353041927083)
        ·
          refine ⟨10980352314872029562890625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320234876581353041927083 10980352314872029562890625)
          ·
            refine ⟨8235264236154022172167969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980352314872029562890625 8235264236154022172167969)
            ·
              refine ⟨6176448177115516629125977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235264236154022172167969 6176448177115516629125977)
              ·
                refine ⟨4632336132836637471844483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176448177115516629125977 4632336132836637471844483)
                ·
                  refine ⟨6948504199254956207766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632336132836637471844483 6948504199254956207766725)
                  ·
                    refine ⟨1302844537360304288956261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948504199254956207766725 1302844537360304288956261)
                    ·
                      rfl

theorem cell23_7611842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7611842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611842 prefixEnd_7611842 := by exact prefixLift 7611842
  have htrace : WordTrace (prefixWord ++ tailWord_7611842) baseStart_7611842 baseEnd_7611842 := by
    simpa [prefixWord, tailWord_7611842, baseEnd_7611842] using wordTrace_append hprefix tailTrace_7611842
  have hstable : (prefixWord ++ tailWord_7611842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611842).length < 2 ^ (prefixWord ++ tailWord_7611842).sum := by decide
  have hdescent : baseEnd_7611842 < baseStart_7611842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611993 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_7611993 : Nat := 118140960795 + 7611993 * 2 ^ 59
def prefixEnd_7611993 : Nat := 4983230072969 + 3 ^ 40 * 7611993 * 2
def baseEnd_7611993 : Nat := 1302870382553247258693529

theorem tailTrace_7611993 : CollatzResearch.WordTrace tailWord_7611993 prefixEnd_7611993 1302870382553247258693529 := by
  unfold tailWord_7611993
  simp only [CollatzResearch.WordTrace]
  refine ⟨277632193112056860749240633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185088128741371240499493755 277632193112056860749240633)
  ·
    refine ⟨208224144834042645561930475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277632193112056860749240633 208224144834042645561930475)
    ·
      refine ⟨312336217251063968342895713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208224144834042645561930475 312336217251063968342895713)
      ·
        refine ⟨234252162938297976257171785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312336217251063968342895713 234252162938297976257171785)
        ·
          refine ⟨175689122203723482192878839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234252162938297976257171785 175689122203723482192878839)
          ·
            refine ⟨263533683305585223289318259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175689122203723482192878839 263533683305585223289318259)
            ·
              refine ⟨395300524958377834933977389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263533683305585223289318259 395300524958377834933977389)
              ·
                refine ⟨148237696859391688100241521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395300524958377834933977389 148237696859391688100241521)
                ·
                  refine ⟨111178272644543766075181141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148237696859391688100241521 111178272644543766075181141)
                  ·
                    refine ⟨1302870382553247258693529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111178272644543766075181141 1302870382553247258693529)
                    ·
                      rfl

theorem cell23_7611993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_7611993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611993 prefixEnd_7611993 := by exact prefixLift 7611993
  have htrace : WordTrace (prefixWord ++ tailWord_7611993) baseStart_7611993 baseEnd_7611993 := by
    simpa [prefixWord, tailWord_7611993, baseEnd_7611993] using wordTrace_append hprefix tailTrace_7611993
  have hstable : (prefixWord ++ tailWord_7611993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611993).length < 2 ^ (prefixWord ++ tailWord_7611993).sum := by decide
  have hdescent : baseEnd_7611993 < baseStart_7611993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612067 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 3]
def baseStart_7612067 : Nat := 118140960795 + 7612067 * 2 ^ 59
def prefixEnd_7612067 : Nat := 4983230072969 + 3 ^ 40 * 7612067 * 2
def baseEnd_7612067 : Nat := 3908649145228174486555247

theorem tailTrace_7612067 : CollatzResearch.WordTrace tailWord_7612067 prefixEnd_7612067 3908649145228174486555247 := by
  unfold tailWord_7612067
  simp only [CollatzResearch.WordTrace]
  refine ⟨277634892113788771387434455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185089928075859180924956303 277634892113788771387434455)
  ·
    refine ⟨416452338170683157081151683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277634892113788771387434455 416452338170683157081151683)
    ·
      refine ⟨624678507256024735621727525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416452338170683157081151683 624678507256024735621727525)
      ·
        refine ⟨117127220110504637929073911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624678507256024735621727525 117127220110504637929073911)
        ·
          refine ⟨175690830165756956893610867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117127220110504637929073911 175690830165756956893610867)
          ·
            refine ⟨263536245248635435340416301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175690830165756956893610867 263536245248635435340416301)
            ·
              refine ⟨98826091968238288252656113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263536245248635435340416301 98826091968238288252656113)
              ·
                refine ⟨74119568976178716189492085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98826091968238288252656113 74119568976178716189492085)
                ·
                  refine ⟨6948709591516754642764883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74119568976178716189492085 6948709591516754642764883)
                  ·
                    refine ⟨10423064387275131964147325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948709591516754642764883 10423064387275131964147325)
                    ·
                      refine ⟨3908649145228174486555247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423064387275131964147325 3908649145228174486555247)
                      ·
                        rfl

theorem cell23_7612067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_7612067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612067 prefixEnd_7612067 := by exact prefixLift 7612067
  have htrace : WordTrace (prefixWord ++ tailWord_7612067) baseStart_7612067 baseEnd_7612067 := by
    simpa [prefixWord, tailWord_7612067, baseEnd_7612067] using wordTrace_append hprefix tailTrace_7612067
  have hstable : (prefixWord ++ tailWord_7612067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612067).length < 2 ^ (prefixWord ++ tailWord_7612067).sum := by decide
  have hdescent : baseEnd_7612067 < baseStart_7612067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612094 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_7612094 : Nat := 118140960795 + 7612094 * 2 ^ 59
def prefixEnd_7612094 : Nat := 4983230072969 + 3 ^ 40 * 7612094 * 2
def baseEnd_7612094 : Nat := 3908663009205845880917623

theorem tailTrace_7612094 : CollatzResearch.WordTrace tailWord_7612094 prefixEnd_7612094 3908663009205845880917623 := by
  unfold tailWord_7612094
  simp only [CollatzResearch.WordTrace]
  refine ⟨34704484610586369374833417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185090584589793969999111557 34704484610586369374833417)
  ·
    refine ⟨26028363457939777031125063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34704484610586369374833417 26028363457939777031125063)
    ·
      refine ⟨39042545186909665546687595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26028363457939777031125063 39042545186909665546687595)
      ·
        refine ⟨58563817780364498320031393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39042545186909665546687595 58563817780364498320031393)
        ·
          refine ⟨43922863335273373740023545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58563817780364498320031393 43922863335273373740023545)
          ·
            refine ⟨32942147501455030305017659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43922863335273373740023545 32942147501455030305017659)
            ·
              refine ⟨49413221252182545457526489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32942147501455030305017659 49413221252182545457526489)
              ·
                refine ⟨37059915939136909093144867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49413221252182545457526489 37059915939136909093144867)
                ·
                  refine ⟨55589873908705363639717301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37059915939136909093144867 55589873908705363639717301)
                  ·
                    refine ⟨5211550678941127841223497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55589873908705363639717301 5211550678941127841223497)
                    ·
                      refine ⟨3908663009205845880917623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211550678941127841223497 3908663009205845880917623)
                      ·
                        rfl

theorem cell23_7612094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_7612094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612094 prefixEnd_7612094 := by exact prefixLift 7612094
  have htrace : WordTrace (prefixWord ++ tailWord_7612094) baseStart_7612094 baseEnd_7612094 := by
    simpa [prefixWord, tailWord_7612094, baseEnd_7612094] using wordTrace_append hprefix tailTrace_7612094
  have hstable : (prefixWord ++ tailWord_7612094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612094).length < 2 ^ (prefixWord ++ tailWord_7612094).sum := by decide
  have hdescent : baseEnd_7612094 < baseStart_7612094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612127 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_7612127 : Nat := 118140960795 + 7612127 * 2 ^ 59
def prefixEnd_7612127 : Nat := 4983230072969 + 3 ^ 40 * 7612127 * 2
def baseEnd_7612127 : Nat := 3908679954067444251804971

theorem tailTrace_7612127 : CollatzResearch.WordTrace tailWord_7612127 prefixEnd_7612127 3908679954067444251804971 := by
  unfold tailWord_7612127
  simp only [CollatzResearch.WordTrace]
  refine ⟨277637080493571401634618635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185091386995714267756412423 277637080493571401634618635)
  ·
    refine ⟨416455620740357102451927953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277637080493571401634618635 416455620740357102451927953)
    ·
      refine ⟨312341715555267826838945965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416455620740357102451927953 312341715555267826838945965)
      ·
        refine ⟨117128143333225435064604737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312341715555267826838945965 117128143333225435064604737)
        ·
          refine ⟨87846107499919076298453553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117128143333225435064604737 87846107499919076298453553)
          ·
            refine ⟨65884580624939307223840165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87846107499919076298453553 65884580624939307223840165)
            ·
              refine ⟨12353358867176120104470031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65884580624939307223840165 12353358867176120104470031)
              ·
                refine ⟨18530038300764180156705047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353358867176120104470031 18530038300764180156705047)
                ·
                  refine ⟨27795057451146270235057571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18530038300764180156705047 27795057451146270235057571)
                  ·
                    refine ⟨41692586176719405352586357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27795057451146270235057571 41692586176719405352586357)
                    ·
                      refine ⟨3908679954067444251804971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41692586176719405352586357 3908679954067444251804971)
                      ·
                        rfl

theorem cell23_7612127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_7612127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612127 prefixEnd_7612127 := by exact prefixLift 7612127
  have htrace : WordTrace (prefixWord ++ tailWord_7612127) baseStart_7612127 baseEnd_7612127 := by
    simpa [prefixWord, tailWord_7612127, baseEnd_7612127] using wordTrace_append hprefix tailTrace_7612127
  have hstable : (prefixWord ++ tailWord_7612127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612127).length < 2 ^ (prefixWord ++ tailWord_7612127).sum := by decide
  have hdescent : baseEnd_7612127 < baseStart_7612127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612135 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7612135 : Nat := 118140960795 + 7612135 * 2 ^ 59
def prefixEnd_7612135 : Nat := 4983230072969 + 3 ^ 40 * 7612135 * 2
def baseEnd_7612135 : Nat := 3908684061912680220504935

theorem tailTrace_7612135 : CollatzResearch.WordTrace tailWord_7612135 prefixEnd_7612135 3908684061912680220504935 := by
  unfold tailWord_7612135
  simp only [CollatzResearch.WordTrace]
  refine ⟨277637372277542419000909859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185091581518361612667273239 277637372277542419000909859)
  ·
    refine ⟨416456058416313628501364789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277637372277542419000909859 416456058416313628501364789)
    ·
      refine ⟨39042755476529402672002949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416456058416313628501364789 39042755476529402672002949)
      ·
        refine ⟨7320516651849263001000553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39042755476529402672002949 7320516651849263001000553)
        ·
          refine ⟨5490387488886947250750415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7320516651849263001000553 5490387488886947250750415)
          ·
            refine ⟨8235581233330420876125623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490387488886947250750415 8235581233330420876125623)
            ·
              refine ⟨12353371849995631314188435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235581233330420876125623 12353371849995631314188435)
              ·
                refine ⟨18530057774993446971282653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353371849995631314188435 18530057774993446971282653)
                ·
                  refine ⟨6948771665622542614230995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18530057774993446971282653 6948771665622542614230995)
                  ·
                    refine ⟨10423157498433813921346493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948771665622542614230995 10423157498433813921346493)
                    ·
                      refine ⟨3908684061912680220504935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423157498433813921346493 3908684061912680220504935)
                      ·
                        rfl

theorem cell23_7612135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7612135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612135 prefixEnd_7612135 := by exact prefixLift 7612135
  have htrace : WordTrace (prefixWord ++ tailWord_7612135) baseStart_7612135 baseEnd_7612135 := by
    simpa [prefixWord, tailWord_7612135, baseEnd_7612135] using wordTrace_append hprefix tailTrace_7612135
  have hstable : (prefixWord ++ tailWord_7612135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612135).length < 2 ^ (prefixWord ++ tailWord_7612135).sum := by decide
  have hdescent : baseEnd_7612135 < baseStart_7612135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612158 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7612158 : Nat := 118140960795 + 7612158 * 2 ^ 59
def prefixEnd_7612158 : Nat := 4983230072969 + 3 ^ 40 * 7612158 * 2
def baseEnd_7612158 : Nat := 3908695871967733630517329

theorem tailTrace_7612158 : CollatzResearch.WordTrace tailWord_7612158 prefixEnd_7612158 3908695871967733630517329 := by
  unfold tailWord_7612158
  simp only [CollatzResearch.WordTrace]
  refine ⟨34704776394557386741124641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185092140770972729285998085 34704776394557386741124641)
  ·
    refine ⟨26028582295918040055843481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34704776394557386741124641 26028582295918040055843481)
    ·
      refine ⟨19521436721938530041882611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26028582295918040055843481 19521436721938530041882611)
      ·
        refine ⟨29282155082907795062823917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19521436721938530041882611 29282155082907795062823917)
        ·
          refine ⟨10980808156090423148558969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29282155082907795062823917 10980808156090423148558969)
          ·
            refine ⟨8235606117067817361419227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980808156090423148558969 8235606117067817361419227)
            ·
              refine ⟨12353409175601726042128841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235606117067817361419227 12353409175601726042128841)
              ·
                refine ⟨9265056881701294531596631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12353409175601726042128841 9265056881701294531596631)
                ·
                  refine ⟨13897585322551941797394947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265056881701294531596631 13897585322551941797394947)
                  ·
                    refine ⟨20846377983827912696092421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13897585322551941797394947 20846377983827912696092421)
                    ·
                      refine ⟨3908695871967733630517329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20846377983827912696092421 3908695871967733630517329)
                      ·
                        rfl

theorem cell23_7612158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7612158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612158 prefixEnd_7612158 := by exact prefixLift 7612158
  have htrace : WordTrace (prefixWord ++ tailWord_7612158) baseStart_7612158 baseEnd_7612158 := by
    simpa [prefixWord, tailWord_7612158, baseEnd_7612158] using wordTrace_append hprefix tailTrace_7612158
  have hstable : (prefixWord ++ tailWord_7612158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612158).length < 2 ^ (prefixWord ++ tailWord_7612158).sum := by decide
  have hdescent : baseEnd_7612158 < baseStart_7612158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612160 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_7612160 : Nat := 118140960795 + 7612160 * 2 ^ 59
def prefixEnd_7612160 : Nat := 4983230072969 + 3 ^ 40 * 7612160 * 2
def baseEnd_7612160 : Nat := 1302898966309680874230773

theorem tailTrace_7612160 : CollatzResearch.WordTrace tailWord_7612160 prefixEnd_7612160 1302898966309680874230773 := by
  unfold tailWord_7612160
  simp only [CollatzResearch.WordTrace]
  refine ⟨138819142051225924135284967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185092189401634565513713289 138819142051225924135284967)
  ·
    refine ⟨208228713076838886202927451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138819142051225924135284967 208228713076838886202927451)
    ·
      refine ⟨312343069615258329304391177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208228713076838886202927451 312343069615258329304391177)
      ·
        refine ⟨234257302211443746978293383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312343069615258329304391177 234257302211443746978293383)
        ·
          refine ⟨351385953317165620467440075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234257302211443746978293383 351385953317165620467440075)
          ·
            refine ⟨527078929975748430701160113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351385953317165620467440075 527078929975748430701160113)
            ·
              refine ⟨395309197481811323025870085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527078929975748430701160113 395309197481811323025870085)
              ·
                refine ⟨74120474527839623067350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395309197481811323025870085 74120474527839623067350641)
                ·
                  refine ⟨55590355895879717300512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74120474527839623067350641 55590355895879717300512981)
                  ·
                    refine ⟨1302898966309680874230773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55590355895879717300512981 1302898966309680874230773)
                    ·
                      rfl

theorem cell23_7612160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_7612160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612160 prefixEnd_7612160 := by exact prefixLift 7612160
  have htrace : WordTrace (prefixWord ++ tailWord_7612160) baseStart_7612160 baseEnd_7612160 := by
    simpa [prefixWord, tailWord_7612160, baseEnd_7612160] using wordTrace_append hprefix tailTrace_7612160
  have hstable : (prefixWord ++ tailWord_7612160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612160).length < 2 ^ (prefixWord ++ tailWord_7612160).sum := by decide
  have hdescent : baseEnd_7612160 < baseStart_7612160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612174 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7612174 : Nat := 118140960795 + 7612174 * 2 ^ 59
def prefixEnd_7612174 : Nat := 4983230072969 + 3 ^ 40 * 7612174 * 2
def baseEnd_7612174 : Nat := 3908704087658205567917255

theorem tailTrace_7612174 : CollatzResearch.WordTrace tailWord_7612174 prefixEnd_7612174 3908704087658205567917255 := by
  unfold tailWord_7612174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34704849340550141082697447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185092529816267419107719717 34704849340550141082697447)
  ·
    refine ⟨52057274010825211624046171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34704849340550141082697447 52057274010825211624046171)
    ·
      refine ⟨78085911016237817436069257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52057274010825211624046171 78085911016237817436069257)
      ·
        refine ⟨58564433262178363077051943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78085911016237817436069257 58564433262178363077051943)
        ·
          refine ⟨87846649893267544615577915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58564433262178363077051943 87846649893267544615577915)
          ·
            refine ⟨131769974839901316923366873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87846649893267544615577915 131769974839901316923366873)
            ·
              refine ⟨98827481129925987692525155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131769974839901316923366873 98827481129925987692525155)
              ·
                refine ⟨148241221694888981538787733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98827481129925987692525155 148241221694888981538787733)
                ·
                  refine ⟨6948807266947921009630675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148241221694888981538787733 6948807266947921009630675)
                  ·
                    refine ⟨10423210900421881514446013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948807266947921009630675 10423210900421881514446013)
                    ·
                      refine ⟨3908704087658205567917255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423210900421881514446013 3908704087658205567917255)
                      ·
                        rfl

theorem cell23_7612174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7612174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612174 prefixEnd_7612174 := by exact prefixLift 7612174
  have htrace : WordTrace (prefixWord ++ tailWord_7612174) baseStart_7612174 baseEnd_7612174 := by
    simpa [prefixWord, tailWord_7612174, baseEnd_7612174] using wordTrace_append hprefix tailTrace_7612174
  have hstable : (prefixWord ++ tailWord_7612174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612174).length < 2 ^ (prefixWord ++ tailWord_7612174).sum := by decide
  have hdescent : baseEnd_7612174 < baseStart_7612174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612191 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_7612191 : Nat := 118140960795 + 7612191 * 2 ^ 59
def prefixEnd_7612191 : Nat := 4983230072969 + 3 ^ 40 * 7612191 * 2
def baseEnd_7612191 : Nat := 3908712816829332001404677

theorem tailTrace_7612191 : CollatzResearch.WordTrace tailWord_7612191 prefixEnd_7612191 3908712816829332001404677 := by
  unfold tailWord_7612191
  simp only [CollatzResearch.WordTrace]
  refine ⟨277639414765339540564948427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185092943176893027043298951 277639414765339540564948427)
  ·
    refine ⟨416459122148009310847422641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277639414765339540564948427 416459122148009310847422641)
    ·
      refine ⟨312344341611006983135566981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416459122148009310847422641 312344341611006983135566981)
      ·
        refine ⟨58564564052063809337918809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312344341611006983135566981 58564564052063809337918809)
        ·
          refine ⟨43923423039047857003439107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58564564052063809337918809 43923423039047857003439107)
          ·
            refine ⟨65885134558571785505158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43923423039047857003439107 65885134558571785505158661)
            ·
              refine ⟨12353462729732209782217249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65885134558571785505158661 12353462729732209782217249)
              ·
                refine ⟨9265097047299157336662937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12353462729732209782217249 9265097047299157336662937)
                ·
                  refine ⟨6948822785474368002497203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265097047299157336662937 6948822785474368002497203)
                  ·
                    refine ⟨10423234178211552003745805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948822785474368002497203 10423234178211552003745805)
                    ·
                      refine ⟨3908712816829332001404677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423234178211552003745805 3908712816829332001404677)
                      ·
                        rfl

theorem cell23_7612191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_7612191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612191 prefixEnd_7612191 := by exact prefixLift 7612191
  have htrace : WordTrace (prefixWord ++ tailWord_7612191) baseStart_7612191 baseEnd_7612191 := by
    simpa [prefixWord, tailWord_7612191, baseEnd_7612191] using wordTrace_append hprefix tailTrace_7612191
  have hstable : (prefixWord ++ tailWord_7612191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612191).length < 2 ^ (prefixWord ++ tailWord_7612191).sum := by decide
  have hdescent : baseEnd_7612191 < baseStart_7612191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612197 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7612197 : Nat := 118140960795 + 7612197 * 2 ^ 59
def prefixEnd_7612197 : Nat := 4983230072969 + 3 ^ 40 * 7612197 * 2
def baseEnd_7612197 : Nat := 3908715897713258977929649

theorem tailTrace_7612197 : CollatzResearch.WordTrace tailWord_7612197 prefixEnd_7612197 3908715897713258977929649 := by
  unfold tailWord_7612197
  simp only [CollatzResearch.WordTrace]
  refine ⟨277639633603317803589666845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185093089068878535726444563 277639633603317803589666845)
  ·
    refine ⟨104114862601244176346125067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277639633603317803589666845 104114862601244176346125067)
    ·
      refine ⟨156172293901866264519187601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104114862601244176346125067 156172293901866264519187601)
      ·
        refine ⟨117129220426399698389390701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156172293901866264519187601 117129220426399698389390701)
        ·
          refine ⟨43923457659899886896021513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117129220426399698389390701 43923457659899886896021513)
          ·
            refine ⟨32942593244924915172016135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43923457659899886896021513 32942593244924915172016135)
            ·
              refine ⟨49413889867387372758024203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32942593244924915172016135 49413889867387372758024203)
              ·
                refine ⟨74120834801081059137036305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49413889867387372758024203 74120834801081059137036305)
                ·
                  refine ⟨55590626100810794352777229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74120834801081059137036305 55590626100810794352777229)
                  ·
                    refine ⟨20846484787804047882291461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55590626100810794352777229 20846484787804047882291461)
                    ·
                      refine ⟨3908715897713258977929649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20846484787804047882291461 3908715897713258977929649)
                      ·
                        rfl

theorem cell23_7612197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7612197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612197 prefixEnd_7612197 := by exact prefixLift 7612197
  have htrace : WordTrace (prefixWord ++ tailWord_7612197) baseStart_7612197 baseEnd_7612197 := by
    simpa [prefixWord, tailWord_7612197, baseEnd_7612197] using wordTrace_append hprefix tailTrace_7612197
  have hstable : (prefixWord ++ tailWord_7612197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612197).length < 2 ^ (prefixWord ++ tailWord_7612197).sum := by decide
  have hdescent : baseEnd_7612197 < baseStart_7612197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612244 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_7612244 : Nat := 118140960795 + 7612244 * 2 ^ 59
def prefixEnd_7612244 : Nat := 4983230072969 + 3 ^ 40 * 7612244 * 2
def baseEnd_7612244 : Nat := 3908740031304020294041933

theorem tailTrace_7612244 : CollatzResearch.WordTrace tailWord_7612244 prefixEnd_7612244 3908740031304020294041933 := by
  unfold tailWord_7612244
  simp only [CollatzResearch.WordTrace]
  refine ⟨138820673917073765308313893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185094231889431687077751857 138820673917073765308313893)
  ·
    refine ⟨26028876359451330995308855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138820673917073765308313893 26028876359451330995308855)
    ·
      refine ⟨39043314539176996492963283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26028876359451330995308855 39043314539176996492963283)
      ·
        refine ⟨58564971808765494739444925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39043314539176996492963283 58564971808765494739444925)
        ·
          refine ⟨21961864428287060527291847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58564971808765494739444925 21961864428287060527291847)
          ·
            refine ⟨32942796642430590790937771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21961864428287060527291847 32942796642430590790937771)
            ·
              refine ⟨49414194963645886186406657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32942796642430590790937771 49414194963645886186406657)
              ·
                refine ⟨37060646222734414639804993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49414194963645886186406657 37060646222734414639804993)
                ·
                  refine ⟨27795484667050810979853745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37060646222734414639804993 27795484667050810979853745)
                  ·
                    refine ⟨20846613500288108234890309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27795484667050810979853745 20846613500288108234890309)
                    ·
                      refine ⟨3908740031304020294041933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20846613500288108234890309 3908740031304020294041933)
                      ·
                        rfl

theorem cell23_7612244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_7612244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612244 prefixEnd_7612244 := by exact prefixLift 7612244
  have htrace : WordTrace (prefixWord ++ tailWord_7612244) baseStart_7612244 baseEnd_7612244 := by
    simpa [prefixWord, tailWord_7612244, baseEnd_7612244] using wordTrace_append hprefix tailTrace_7612244
  have hstable : (prefixWord ++ tailWord_7612244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612244).length < 2 ^ (prefixWord ++ tailWord_7612244).sum := by decide
  have hdescent : baseEnd_7612244 < baseStart_7612244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612264 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7612264 : Nat := 118140960795 + 7612264 * 2 ^ 59
def prefixEnd_7612264 : Nat := 4983230072969 + 3 ^ 40 * 7612264 * 2
def baseEnd_7612264 : Nat := 3908750300917110215791841

theorem tailTrace_7612264 : CollatzResearch.WordTrace tailWord_7612264 prefixEnd_7612264 3908750300917110215791841 := by
  unfold tailWord_7612264
  simp only [CollatzResearch.WordTrace]
  refine ⟨138821038647037537016177923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185094718196050049354903897 138821038647037537016177923)
  ·
    refine ⟨208231557970556305524266885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138821038647037537016177923 208231557970556305524266885)
    ·
      refine ⟨39043417119479307285800041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208231557970556305524266885 39043417119479307285800041)
      ·
        refine ⟨29282562839609480464350031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39043417119479307285800041 29282562839609480464350031)
        ·
          refine ⟨43923844259414220696525047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282562839609480464350031 43923844259414220696525047)
          ·
            refine ⟨65885766389121331044787571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43923844259414220696525047 65885766389121331044787571)
            ·
              refine ⟨98828649583681996567181357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65885766389121331044787571 98828649583681996567181357)
              ·
                refine ⟨37060743593880748712693009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98828649583681996567181357 37060743593880748712693009)
                ·
                  refine ⟨27795557695410561534519757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37060743593880748712693009 27795557695410561534519757)
                  ·
                    refine ⟨10423334135778960575444909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27795557695410561534519757 10423334135778960575444909)
                    ·
                      refine ⟨3908750300917110215791841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423334135778960575444909 3908750300917110215791841)
                      ·
                        rfl

theorem cell23_7612264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7612264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612264 prefixEnd_7612264 := by exact prefixLift 7612264
  have htrace : WordTrace (prefixWord ++ tailWord_7612264) baseStart_7612264 baseEnd_7612264 := by
    simpa [prefixWord, tailWord_7612264, baseEnd_7612264] using wordTrace_append hprefix tailTrace_7612264
  have hstable : (prefixWord ++ tailWord_7612264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612264).length < 2 ^ (prefixWord ++ tailWord_7612264).sum := by decide
  have hdescent : baseEnd_7612264 < baseStart_7612264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612341 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7612341 : Nat := 118140960795 + 7612341 * 2 ^ 59
def prefixEnd_7612341 : Nat := 4983230072969 + 3 ^ 40 * 7612341 * 2
def baseEnd_7612341 : Nat := 3908789838927506414528987

theorem tailTrace_7612341 : CollatzResearch.WordTrace tailWord_7612341 prefixEnd_7612341 3908789838927506414528987 := by
  unfold tailWord_7612341
  simp only [CollatzResearch.WordTrace]
  refine ⟨277644885714796116182908877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185096590476530744121939251 277644885714796116182908877)
  ·
    refine ⟨104116832143048543568590829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277644885714796116182908877 104116832143048543568590829)
    ·
      refine ⟨39043812053643203838221561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104116832143048543568590829 39043812053643203838221561)
      ·
        refine ⟨29282859040232402878666171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39043812053643203838221561 29282859040232402878666171)
        ·
          refine ⟨43924288560348604317999257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282859040232402878666171 43924288560348604317999257)
          ·
            refine ⟨32943216420261453238499443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43924288560348604317999257 32943216420261453238499443)
            ·
              refine ⟨49414824630392179857749165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32943216420261453238499443 49414824630392179857749165)
              ·
                refine ⟨18530559236397067446655937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49414824630392179857749165 18530559236397067446655937)
                ·
                  refine ⟨13897919427297800584991953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18530559236397067446655937 13897919427297800584991953)
                  ·
                    refine ⟨10423439570473350438743965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13897919427297800584991953 10423439570473350438743965)
                    ·
                      refine ⟨3908789838927506414528987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423439570473350438743965 3908789838927506414528987)
                      ·
                        rfl

theorem cell23_7612341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7612341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612341 prefixEnd_7612341 := by exact prefixLift 7612341
  have htrace : WordTrace (prefixWord ++ tailWord_7612341) baseStart_7612341 baseEnd_7612341 := by
    simpa [prefixWord, tailWord_7612341, baseEnd_7612341] using wordTrace_append hprefix tailTrace_7612341
  have hstable : (prefixWord ++ tailWord_7612341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612341).length < 2 ^ (prefixWord ++ tailWord_7612341).sum := by decide
  have hdescent : baseEnd_7612341 < baseStart_7612341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612398 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_7612398 : Nat := 118140960795 + 7612398 * 2 ^ 59
def prefixEnd_7612398 : Nat := 4983230072969 + 3 ^ 40 * 7612398 * 2
def baseEnd_7612398 : Nat := 3908819107324812691516225

theorem tailTrace_7612398 : CollatzResearch.WordTrace tailWord_7612398 prefixEnd_7612398 3908819107324812691516225 := by
  unfold tailWord_7612398
  simp only [CollatzResearch.WordTrace]
  refine ⟨34705870584448701864716731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185097976450393076611822565 34705870584448701864716731)
  ·
    refine ⟨52058805876673052797075097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34705870584448701864716731 52058805876673052797075097)
    ·
      refine ⟨39044104407504789597806323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52058805876673052797075097 39044104407504789597806323)
      ·
        refine ⟨58566156611257184396709485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39044104407504789597806323 58566156611257184396709485)
        ·
          refine ⟨21962308729221444148766057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58566156611257184396709485 21962308729221444148766057)
          ·
            refine ⟨16471731546916083111574543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21962308729221444148766057 16471731546916083111574543)
            ·
              refine ⟨24707597320374124667361815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471731546916083111574543 24707597320374124667361815)
              ·
                refine ⟨37061395980561187001042723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24707597320374124667361815 37061395980561187001042723)
                ·
                  refine ⟨55592093970841780501564085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37061395980561187001042723 55592093970841780501564085)
                  ·
                    refine ⟨5211758809766416922021633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55592093970841780501564085 5211758809766416922021633)
                    ·
                      refine ⟨3908819107324812691516225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211758809766416922021633 3908819107324812691516225)
                      ·
                        rfl

theorem cell23_7612398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_7612398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612398 prefixEnd_7612398 := by exact prefixLift 7612398
  have htrace : WordTrace (prefixWord ++ tailWord_7612398) baseStart_7612398 baseEnd_7612398 := by
    simpa [prefixWord, tailWord_7612398, baseEnd_7612398] using wordTrace_append hprefix tailTrace_7612398
  have hstable : (prefixWord ++ tailWord_7612398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612398).length < 2 ^ (prefixWord ++ tailWord_7612398).sum := by decide
  have hdescent : baseEnd_7612398 < baseStart_7612398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612421 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_7612421 : Nat := 118140960795 + 7612421 * 2 ^ 59
def prefixEnd_7612421 : Nat := 4983230072969 + 3 ^ 40 * 7612421 * 2
def baseEnd_7612421 : Nat := 1302943639126622033842873

theorem tailTrace_7612421 : CollatzResearch.WordTrace tailWord_7612421 prefixEnd_7612421 1302943639126622033842873 := by
  unfold tailWord_7612421
  simp only [CollatzResearch.WordTrace]
  refine ⟨277647803554506289845821117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185098535703004193230547411 277647803554506289845821117)
  ·
    refine ⟨104117926332939858692182919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277647803554506289845821117 104117926332939858692182919)
    ·
      refine ⟨156176889499409788038274379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104117926332939858692182919 156176889499409788038274379)
      ·
        refine ⟨234265334249114682057411569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156176889499409788038274379 234265334249114682057411569)
        ·
          refine ⟨175699000686836011543058677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234265334249114682057411569 175699000686836011543058677)
          ·
            refine ⟨16471781314390876082161751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175699000686836011543058677 16471781314390876082161751)
            ·
              refine ⟨24707671971586314123242627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471781314390876082161751 24707671971586314123242627)
              ·
                refine ⟨37061507957379471184863941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24707671971586314123242627 37061507957379471184863941)
                ·
                  refine ⟨6949032742008650847161989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37061507957379471184863941 6949032742008650847161989)
                  ·
                    refine ⟨1302943639126622033842873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949032742008650847161989 1302943639126622033842873)
                    ·
                      rfl

theorem cell23_7612421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_7612421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612421 prefixEnd_7612421 := by exact prefixLift 7612421
  have htrace : WordTrace (prefixWord ++ tailWord_7612421) baseStart_7612421 baseEnd_7612421 := by
    simpa [prefixWord, tailWord_7612421, baseEnd_7612421] using wordTrace_append hprefix tailTrace_7612421
  have hstable : (prefixWord ++ tailWord_7612421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612421).length < 2 ^ (prefixWord ++ tailWord_7612421).sum := by decide
  have hdescent : baseEnd_7612421 < baseStart_7612421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612424 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7612424 : Nat := 118140960795 + 7612424 * 2 ^ 59
def prefixEnd_7612424 : Nat := 4983230072969 + 3 ^ 40 * 7612424 * 2
def baseEnd_7612424 : Nat := 3908832457821829589791105

theorem tailTrace_7612424 : CollatzResearch.WordTrace tailWord_7612424 prefixEnd_7612424 3908832457821829589791105 := by
  unfold tailWord_7612424
  simp only [CollatzResearch.WordTrace]
  refine ⟨138823956486747710679090163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185098608648996947572120217 138823956486747710679090163)
  ·
    refine ⟨208235934730121566018635245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138823956486747710679090163 208235934730121566018635245)
    ·
      refine ⟨78088475523795587256988217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208235934730121566018635245 78088475523795587256988217)
      ·
        refine ⟨58566356642846690442741163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78088475523795587256988217 58566356642846690442741163)
        ·
          refine ⟨87849534964270035664111745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58566356642846690442741163 87849534964270035664111745)
          ·
            refine ⟨65887151223202526748083809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87849534964270035664111745 65887151223202526748083809)
            ·
              refine ⟨49415363417401895061062857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65887151223202526748083809 49415363417401895061062857)
              ·
                refine ⟨37061522563051421295797143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49415363417401895061062857 37061522563051421295797143)
                ·
                  refine ⟨55592283844577131943695715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37061522563051421295797143 55592283844577131943695715)
                  ·
                    refine ⟨83388425766865697915543573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55592283844577131943695715 83388425766865697915543573)
                    ·
                      refine ⟨3908832457821829589791105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83388425766865697915543573 3908832457821829589791105)
                      ·
                        rfl

theorem cell23_7612424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7612424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612424 prefixEnd_7612424 := by exact prefixLift 7612424
  have htrace : WordTrace (prefixWord ++ tailWord_7612424) baseStart_7612424 baseEnd_7612424 := by
    simpa [prefixWord, tailWord_7612424, baseEnd_7612424] using wordTrace_append hprefix tailTrace_7612424
  have hstable : (prefixWord ++ tailWord_7612424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612424).length < 2 ^ (prefixWord ++ tailWord_7612424).sum := by decide
  have hdescent : baseEnd_7612424 < baseStart_7612424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612445 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_7612445 : Nat := 118140960795 + 7612445 * 2 ^ 59
def prefixEnd_7612445 : Nat := 4983230072969 + 3 ^ 40 * 7612445 * 2
def baseEnd_7612445 : Nat := 3908843240915574007628509

theorem tailTrace_7612445 : CollatzResearch.WordTrace tailWord_7612445 prefixEnd_7612445 3908843240915574007628509 := by
  unfold tailWord_7612445
  simp only [CollatzResearch.WordTrace]
  refine ⟨277648678906419341944694789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185099119270946227963129859 277648678906419341944694789)
  ·
    refine ⟨52059127294953626614630273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277648678906419341944694789 52059127294953626614630273)
    ·
      refine ⟨39044345471215219960972705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52059127294953626614630273 39044345471215219960972705)
      ·
        refine ⟨29283259103411414970729529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39044345471215219960972705 29283259103411414970729529)
        ·
          refine ⟨21962444327558561228047147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29283259103411414970729529 21962444327558561228047147)
          ·
            refine ⟨32943666491337841842070721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21962444327558561228047147 32943666491337841842070721)
            ·
              refine ⟨24707749868503381381553041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32943666491337841842070721 24707749868503381381553041)
              ·
                refine ⟨18530812401377536036164781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24707749868503381381553041 18530812401377536036164781)
                ·
                  refine ⟨6949054650516576013561793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18530812401377536036164781 6949054650516576013561793)
                  ·
                    refine ⟨5211790987887432010171345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949054650516576013561793 5211790987887432010171345)
                    ·
                      refine ⟨3908843240915574007628509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211790987887432010171345 3908843240915574007628509)
                      ·
                        rfl

theorem cell23_7612445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_7612445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612445 prefixEnd_7612445 := by exact prefixLift 7612445
  have htrace : WordTrace (prefixWord ++ tailWord_7612445) baseStart_7612445 baseEnd_7612445 := by
    simpa [prefixWord, tailWord_7612445, baseEnd_7612445] using wordTrace_append hprefix tailTrace_7612445
  have hstable : (prefixWord ++ tailWord_7612445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612445).length < 2 ^ (prefixWord ++ tailWord_7612445).sum := by decide
  have hdescent : baseEnd_7612445 < baseStart_7612445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612456 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7612456 : Nat := 118140960795 + 7612456 * 2 ^ 59
def prefixEnd_7612456 : Nat := 4983230072969 + 3 ^ 40 * 7612456 * 2
def baseEnd_7612456 : Nat := 3908848889202773464590959

theorem tailTrace_7612456 : CollatzResearch.WordTrace tailWord_7612456 prefixEnd_7612456 3908848889202773464590959 := by
  unfold tailWord_7612456
  simp only [CollatzResearch.WordTrace]
  refine ⟨138824540054689745411672611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185099386739586327215563481 138824540054689745411672611)
  ·
    refine ⟨208236810082034618117508917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138824540054689745411672611 208236810082034618117508917)
    ·
      refine ⟨19522200945190745448516461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208236810082034618117508917 19522200945190745448516461)
      ·
        refine ⟨7320825354446529543193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19522200945190745448516461 7320825354446529543193673)
        ·
          refine ⟨5490619015834897157395255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7320825354446529543193673 5490619015834897157395255)
          ·
            refine ⟨8235928523752345736092883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490619015834897157395255 8235928523752345736092883)
            ·
              refine ⟨12353892785628518604139325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235928523752345736092883 12353892785628518604139325)
              ·
                refine ⟨4632709794610694476552247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12353892785628518604139325 4632709794610694476552247)
                ·
                  refine ⟨6949064691916041714828371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632709794610694476552247 6949064691916041714828371)
                  ·
                    refine ⟨10423597037874062572242557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949064691916041714828371 10423597037874062572242557)
                    ·
                      refine ⟨3908848889202773464590959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423597037874062572242557 3908848889202773464590959)
                      ·
                        rfl

theorem cell23_7612456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7612456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612456 prefixEnd_7612456 := by exact prefixLift 7612456
  have htrace : WordTrace (prefixWord ++ tailWord_7612456) baseStart_7612456 baseEnd_7612456 := by
    simpa [prefixWord, tailWord_7612456, baseEnd_7612456] using wordTrace_append hprefix tailTrace_7612456
  have hstable : (prefixWord ++ tailWord_7612456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612456).length < 2 ^ (prefixWord ++ tailWord_7612456).sum := by decide
  have hdescent : baseEnd_7612456 < baseStart_7612456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612468 : List Nat := [2, 5, 1, 2, 2, 2, 9]
def baseStart_7612468 : Nat := 118140960795 + 7612468 * 2 ^ 59
def prefixEnd_7612468 : Nat := 4983230072969 + 3 ^ 40 * 7612468 * 2
def baseEnd_7612468 : Nat := 48257469765069474291863

theorem tailTrace_7612468 : CollatzResearch.WordTrace tailWord_7612468 prefixEnd_7612468 48257469765069474291863 := by
  unfold tailWord_7612468
  simp only [CollatzResearch.WordTrace]
  refine ⟨138824758892668008436391029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185099678523557344581854705 138824758892668008436391029)
  ·
    refine ⟨13014821146187625790911659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138824758892668008436391029 13014821146187625790911659)
    ·
      refine ⟨19522231719281438686367489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014821146187625790911659 19522231719281438686367489)
      ·
        refine ⟨14641673789461079014775617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19522231719281438686367489 14641673789461079014775617)
        ·
          refine ⟨10981255342095809261081713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14641673789461079014775617 10981255342095809261081713)
          ·
            refine ⟨8235941506571856945811285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981255342095809261081713 8235941506571856945811285)
            ·
              refine ⟨48257469765069474291863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8235941506571856945811285 48257469765069474291863)
              ·
                rfl

theorem cell23_7612468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 9].length) (baseStart_7612468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612468 prefixEnd_7612468 := by exact prefixLift 7612468
  have htrace : WordTrace (prefixWord ++ tailWord_7612468) baseStart_7612468 baseEnd_7612468 := by
    simpa [prefixWord, tailWord_7612468, baseEnd_7612468] using wordTrace_append hprefix tailTrace_7612468
  have hstable : (prefixWord ++ tailWord_7612468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612468).length < 2 ^ (prefixWord ++ tailWord_7612468).sum := by decide
  have hdescent : baseEnd_7612468 < baseStart_7612468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612474 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_7612474 : Nat := 118140960795 + 7612474 * 2 ^ 59
def prefixEnd_7612474 : Nat := 4983230072969 + 3 ^ 40 * 7612474 * 2
def baseEnd_7612474 : Nat := 3908858131854554394165875

theorem tailTrace_7612474 : CollatzResearch.WordTrace tailWord_7612474 prefixEnd_7612474 3908858131854554394165875 := by
  unfold tailWord_7612474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412434155828569974375119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185099824415542853265000317 69412434155828569974375119)
  ·
    refine ⟨104118651233742854961562679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69412434155828569974375119 104118651233742854961562679)
    ·
      refine ⟨156177976850614282442344019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104118651233742854961562679 156177976850614282442344019)
      ·
        refine ⟨234266965275921423663516029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156177976850614282442344019 234266965275921423663516029)
        ·
          refine ⟨87850111978470533873818511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234266965275921423663516029 87850111978470533873818511)
          ·
            refine ⟨131775167967705800810727767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87850111978470533873818511 131775167967705800810727767)
            ·
              refine ⟨197662751951558701216091651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131775167967705800810727767 197662751951558701216091651)
              ·
                refine ⟨296494127927338051824137477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197662751951558701216091651 296494127927338051824137477)
                ·
                  refine ⟨55592648986375884717025777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296494127927338051824137477 55592648986375884717025777)
                  ·
                    refine ⟨41694486739781913537769333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55592648986375884717025777 41694486739781913537769333)
                    ·
                      refine ⟨3908858131854554394165875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41694486739781913537769333 3908858131854554394165875)
                      ·
                        rfl

theorem cell23_7612474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_7612474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612474 prefixEnd_7612474 := by exact prefixLift 7612474
  have htrace : WordTrace (prefixWord ++ tailWord_7612474) baseStart_7612474 baseEnd_7612474 := by
    simpa [prefixWord, tailWord_7612474, baseEnd_7612474] using wordTrace_append hprefix tailTrace_7612474
  have hstable : (prefixWord ++ tailWord_7612474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612474).length < 2 ^ (prefixWord ++ tailWord_7612474).sum := by decide
  have hdescent : baseEnd_7612474 < baseStart_7612474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612535 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_7612535 : Nat := 118140960795 + 7612535 * 2 ^ 59
def prefixEnd_7612535 : Nat := 4983230072969 + 3 ^ 40 * 7612535 * 2
def baseEnd_7612535 : Nat := 3908889454174478655503095

theorem tailTrace_7612535 : CollatzResearch.WordTrace tailWord_7612535 prefixEnd_7612535 3908889454174478655503095 := by
  unfold tailWord_7612535
  simp only [CollatzResearch.WordTrace]
  refine ⟨277651961476093287315471059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185101307650728858210314039 277651961476093287315471059)
  ·
    refine ⟨416477942214139930973206589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277651961476093287315471059 416477942214139930973206589)
    ·
      refine ⟨156179228330302474114952471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416477942214139930973206589 156179228330302474114952471)
      ·
        refine ⟨234268842495453711172428707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156179228330302474114952471 234268842495453711172428707)
        ·
          refine ⟨351403263743180566758643061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234268842495453711172428707 351403263743180566758643061)
          ·
            refine ⟨32944055975923178133622787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351403263743180566758643061 32944055975923178133622787)
            ·
              refine ⟨49416083963884767200434181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32944055975923178133622787 49416083963884767200434181)
              ·
                refine ⟨9265515743228393850081409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49416083963884767200434181 9265515743228393850081409)
                ·
                  refine ⟨6949136807421295387561057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265515743228393850081409 6949136807421295387561057)
                  ·
                    refine ⟨5211852605565971540670793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949136807421295387561057 5211852605565971540670793)
                    ·
                      refine ⟨3908889454174478655503095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211852605565971540670793 3908889454174478655503095)
                      ·
                        rfl

theorem cell23_7612535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_7612535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612535 prefixEnd_7612535 := by exact prefixLift 7612535
  have htrace : WordTrace (prefixWord ++ tailWord_7612535) baseStart_7612535 baseEnd_7612535 := by
    simpa [prefixWord, tailWord_7612535, baseEnd_7612535] using wordTrace_append hprefix tailTrace_7612535
  have hstable : (prefixWord ++ tailWord_7612535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612535).length < 2 ^ (prefixWord ++ tailWord_7612535).sum := by decide
  have hdescent : baseEnd_7612535 < baseStart_7612535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_7612544 : Nat := 118140960795 + 7612544 * 2 ^ 59
def prefixEnd_7612544 : Nat := 4983230072969 + 3 ^ 40 * 7612544 * 2
def baseEnd_7612544 : Nat := 3908894075500369120290553

theorem tailTrace_7612544 : CollatzResearch.WordTrace tailWord_7612544 prefixEnd_7612544 3908894075500369120290553 := by
  unfold tailWord_7612544
  simp only [CollatzResearch.WordTrace]
  refine ⟨138826144866530340926274343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185101526488707121235032457 138826144866530340926274343)
  ·
    refine ⟨208239217299795511389411515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138826144866530340926274343 208239217299795511389411515)
    ·
      refine ⟨312358825949693267084117273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208239217299795511389411515 312358825949693267084117273)
      ·
        refine ⟨234269119462269950313087955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312358825949693267084117273 234269119462269950313087955)
        ·
          refine ⟨351403679193404925469631933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234269119462269950313087955 351403679193404925469631933)
          ·
            refine ⟨131776379697526847051111975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351403679193404925469631933 131776379697526847051111975)
            ·
              refine ⟨197664569546290270576667963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131776379697526847051111975 197664569546290270576667963)
              ·
                refine ⟨296496854319435405865001945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197664569546290270576667963 296496854319435405865001945)
                ·
                  refine ⟨222372640739576554398751459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296496854319435405865001945 222372640739576554398751459)
                  ·
                    refine ⟨333558961109364831598127189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222372640739576554398751459 333558961109364831598127189)
                    ·
                      refine ⟨3908894075500369120290553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333558961109364831598127189 3908894075500369120290553)
                      ·
                        rfl

theorem cell23_7612544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_7612544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612544 prefixEnd_7612544 := by exact prefixLift 7612544
  have htrace : WordTrace (prefixWord ++ tailWord_7612544) baseStart_7612544 baseEnd_7612544 := by
    simpa [prefixWord, tailWord_7612544, baseEnd_7612544] using wordTrace_append hprefix tailTrace_7612544
  have hstable : (prefixWord ++ tailWord_7612544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612544).length < 2 ^ (prefixWord ++ tailWord_7612544).sum := by decide
  have hdescent : baseEnd_7612544 < baseStart_7612544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612551 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_7612551 : Nat := 118140960795 + 7612551 * 2 ^ 59
def prefixEnd_7612551 : Nat := 4983230072969 + 3 ^ 40 * 7612551 * 2
def baseEnd_7612551 : Nat := 3908897669864950592903021

theorem tailTrace_7612551 : CollatzResearch.WordTrace tailWord_7612551 prefixEnd_7612551 3908897669864950592903021 := by
  unfold tailWord_7612551
  simp only [CollatzResearch.WordTrace]
  refine ⟨277652545044035322048053507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185101696696023548032035671 277652545044035322048053507)
  ·
    refine ⟨416478817566052983072080261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277652545044035322048053507 416478817566052983072080261)
    ·
      refine ⟨78089778293634934326015049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416478817566052983072080261 78089778293634934326015049)
      ·
        refine ⟨58567333720226200744511287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78089778293634934326015049 58567333720226200744511287)
        ·
          refine ⟨87851000580339301116766931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58567333720226200744511287 87851000580339301116766931)
          ·
            refine ⟨131776500870508951675150397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87851000580339301116766931 131776500870508951675150397)
            ·
              refine ⟨49416187826440856878181399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131776500870508951675150397 49416187826440856878181399)
              ·
                refine ⟨74124281739661285317272099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49416187826440856878181399 74124281739661285317272099)
                ·
                  refine ⟨111186422609491927975908149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74124281739661285317272099 111186422609491927975908149)
                  ·
                    refine ⟨10423727119639868247741389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111186422609491927975908149 10423727119639868247741389)
                    ·
                      refine ⟨3908897669864950592903021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423727119639868247741389 3908897669864950592903021)
                      ·
                        rfl

theorem cell23_7612551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_7612551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612551 prefixEnd_7612551 := by exact prefixLift 7612551
  have htrace : WordTrace (prefixWord ++ tailWord_7612551) baseStart_7612551 baseEnd_7612551 := by
    simpa [prefixWord, tailWord_7612551, baseEnd_7612551] using wordTrace_append hprefix tailTrace_7612551
  have hstable : (prefixWord ++ tailWord_7612551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612551).length < 2 ^ (prefixWord ++ tailWord_7612551).sum := by decide
  have hdescent : baseEnd_7612551 < baseStart_7612551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612552 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7612552 : Nat := 118140960795 + 7612552 * 2 ^ 59
def prefixEnd_7612552 : Nat := 4983230072969 + 3 ^ 40 * 7612552 * 2
def baseEnd_7612552 : Nat := 3908898183345605088990517

theorem tailTrace_7612552 : CollatzResearch.WordTrace tailWord_7612552 prefixEnd_7612552 3908898183345605088990517 := by
  unfold tailWord_7612552
  simp only [CollatzResearch.WordTrace]
  refine ⟨138826290758515849609419955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185101721011354466145893273 138826290758515849609419955)
  ·
    refine ⟨208239436137773774414129933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138826290758515849609419955 208239436137773774414129933)
    ·
      refine ⟨78089788551665165405298725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208239436137773774414129933 78089788551665165405298725)
      ·
        refine ⟨14641835353437218513493511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78089788551665165405298725 14641835353437218513493511)
        ·
          refine ⟨21962753030155827770240267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14641835353437218513493511 21962753030155827770240267)
          ·
            refine ⟨32944129545233741655360401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21962753030155827770240267 32944129545233741655360401)
            ·
              refine ⟨24708097158925306241520301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32944129545233741655360401 24708097158925306241520301)
              ·
                refine ⟨9265536434596989840570113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24708097158925306241520301 9265536434596989840570113)
                ·
                  refine ⟨6949152325947742380427585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265536434596989840570113 6949152325947742380427585)
                  ·
                    refine ⟨5211864244460806785320689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949152325947742380427585 5211864244460806785320689)
                    ·
                      refine ⟨3908898183345605088990517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211864244460806785320689 3908898183345605088990517)
                      ·
                        rfl

theorem cell23_7612552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7612552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612552 prefixEnd_7612552 := by exact prefixLift 7612552
  have htrace : WordTrace (prefixWord ++ tailWord_7612552) baseStart_7612552 baseEnd_7612552 := by
    simpa [prefixWord, tailWord_7612552, baseEnd_7612552] using wordTrace_append hprefix tailTrace_7612552
  have hstable : (prefixWord ++ tailWord_7612552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612552).length < 2 ^ (prefixWord ++ tailWord_7612552).sum := by decide
  have hdescent : baseEnd_7612552 < baseStart_7612552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612558 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_7612558 : Nat := 118140960795 + 7612558 * 2 ^ 59
def prefixEnd_7612558 : Nat := 4983230072969 + 3 ^ 40 * 7612558 * 2
def baseEnd_7612558 : Nat := 434322362692170229501721

theorem tailTrace_7612558 : CollatzResearch.WordTrace tailWord_7612558 prefixEnd_7612558 434322362692170229501721 := by
  unfold tailWord_7612558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706600044376245280444791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185101866903339974829038885 34706600044376245280444791)
  ·
    refine ⟨52059900066564367920667187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34706600044376245280444791 52059900066564367920667187)
    ·
      refine ⟨78089850099846551881000781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52059900066564367920667187 78089850099846551881000781)
      ·
        refine ⟨29283693787442456955375293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78089850099846551881000781 29283693787442456955375293)
        ·
          refine ⟨10981385170290921358265735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29283693787442456955375293 10981385170290921358265735)
          ·
            refine ⟨16472077755436382037398603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981385170290921358265735 16472077755436382037398603)
            ·
              refine ⟨24708116633154573056097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472077755436382037398603 24708116633154573056097905)
              ·
                refine ⟨18531087474865929792073429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24708116633154573056097905 18531087474865929792073429)
                ·
                  refine ⟨434322362692170229501721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18531087474865929792073429 434322362692170229501721)
                  ·
                    rfl

theorem cell23_7612558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_7612558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612558 prefixEnd_7612558 := by exact prefixLift 7612558
  have htrace : WordTrace (prefixWord ++ tailWord_7612558) baseStart_7612558 baseEnd_7612558 := by
    simpa [prefixWord, tailWord_7612558, baseEnd_7612558] using wordTrace_append hprefix tailTrace_7612558
  have hstable : (prefixWord ++ tailWord_7612558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612558).length < 2 ^ (prefixWord ++ tailWord_7612558).sum := by decide
  have hdescent : baseEnd_7612558 < baseStart_7612558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612575 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 5]
def baseStart_7612575 : Nat := 118140960795 + 7612575 * 2 ^ 59
def prefixEnd_7612575 : Nat := 4983230072969 + 3 ^ 40 * 7612575 * 2
def baseEnd_7612575 : Nat := 434323332600073166555879

theorem tailTrace_7612575 : CollatzResearch.WordTrace tailWord_7612575 prefixEnd_7612575 434323332600073166555879 := by
  unfold tailWord_7612575
  simp only [CollatzResearch.WordTrace]
  refine ⟨277653420395948374146927179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185102280263965582764618119 277653420395948374146927179)
  ·
    refine ⟨416480130593922561220390769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277653420395948374146927179 416480130593922561220390769)
    ·
      refine ⟨312360097945441920915293077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416480130593922561220390769 312360097945441920915293077)
      ·
        refine ⟨14641879591192590042904363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312360097945441920915293077 14641879591192590042904363)
        ·
          refine ⟨21962819386788885064356545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14641879591192590042904363 21962819386788885064356545)
          ·
            refine ⟨16472114540091663798267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21962819386788885064356545 16472114540091663798267409)
            ·
              refine ⟨12354085905068747848700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16472114540091663798267409 12354085905068747848700557)
              ·
                refine ⟨4632782214400780443262709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12354085905068747848700557 4632782214400780443262709)
                ·
                  refine ⟨434323332600073166555879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4632782214400780443262709 434323332600073166555879)
                  ·
                    rfl

theorem cell23_7612575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 5].length) (baseStart_7612575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612575 prefixEnd_7612575 := by exact prefixLift 7612575
  have htrace : WordTrace (prefixWord ++ tailWord_7612575) baseStart_7612575 baseEnd_7612575 := by
    simpa [prefixWord, tailWord_7612575, baseEnd_7612575] using wordTrace_append hprefix tailTrace_7612575
  have hstable : (prefixWord ++ tailWord_7612575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612575).length < 2 ^ (prefixWord ++ tailWord_7612575).sum := by decide
  have hdescent : baseEnd_7612575 < baseStart_7612575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612586 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7612586 : Nat := 118140960795 + 7612586 * 2 ^ 59
def prefixEnd_7612586 : Nat := 4983230072969 + 3 ^ 40 * 7612586 * 2
def baseEnd_7612586 : Nat := 3908915641687857955965361

theorem tailTrace_7612586 : CollatzResearch.WordTrace tailWord_7612586 prefixEnd_7612586 3908915641687857955965361 := by
  unfold tailWord_7612586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69413455399727130756394403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185102547732605682017051741 69413455399727130756394403)
  ·
    refine ⟨104120183099590696134591605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69413455399727130756394403 104120183099590696134591605)
    ·
      refine ⟨9761267165586627762617963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104120183099590696134591605 9761267165586627762617963)
      ·
        refine ⟨14641900748379941643926945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9761267165586627762617963 14641900748379941643926945)
        ·
          refine ⟨10981425561284956232945209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14641900748379941643926945 10981425561284956232945209)
          ·
            refine ⟨8236069170963717174708907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981425561284956232945209 8236069170963717174708907)
            ·
              refine ⟨12354103756445575762063361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236069170963717174708907 12354103756445575762063361)
              ·
                refine ⟨9265577817334181821547521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12354103756445575762063361 9265577817334181821547521)
                ·
                  refine ⟨6949183363000636366160641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265577817334181821547521 6949183363000636366160641)
                  ·
                    refine ⟨5211887522250477274620481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949183363000636366160641 5211887522250477274620481)
                    ·
                      refine ⟨3908915641687857955965361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211887522250477274620481 3908915641687857955965361)
                      ·
                        rfl

theorem cell23_7612586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7612586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612586 prefixEnd_7612586 := by exact prefixLift 7612586
  have htrace : WordTrace (prefixWord ++ tailWord_7612586) baseStart_7612586 baseEnd_7612586 := by
    simpa [prefixWord, tailWord_7612586, baseEnd_7612586] using wordTrace_append hprefix tailTrace_7612586
  have hstable : (prefixWord ++ tailWord_7612586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612586).length < 2 ^ (prefixWord ++ tailWord_7612586).sum := by decide
  have hdescent : baseEnd_7612586 < baseStart_7612586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612591 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_7612591 : Nat := 118140960795 + 7612591 * 2 ^ 59
def prefixEnd_7612591 : Nat := 4983230072969 + 3 ^ 40 * 7612591 * 2
def baseEnd_7612591 : Nat := 3908918209091130436402837

theorem tailTrace_7612591 : CollatzResearch.WordTrace tailWord_7612591 prefixEnd_7612591 3908918209091130436402837 := by
  unfold tailWord_7612591
  simp only [CollatzResearch.WordTrace]
  refine ⟨277654003963890408879509627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185102669309260272586339751 277654003963890408879509627)
  ·
    refine ⟨416481005945835613319264441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277654003963890408879509627 416481005945835613319264441)
    ·
      refine ⟨312360754459376709989448331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416481005945835613319264441 312360754459376709989448331)
      ·
        refine ⟨468541131689065064984172497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312360754459376709989448331 468541131689065064984172497)
        ·
          refine ⟨351405848766798798738129373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468541131689065064984172497 351405848766798798738129373)
          ·
            refine ⟨131777193287549549526798515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351405848766798798738129373 131777193287549549526798515)
            ·
              refine ⟨197665789931324324290197773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131777193287549549526798515 197665789931324324290197773)
              ·
                refine ⟨74124671224246621608824165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197665789931324324290197773 74124671224246621608824165)
                ·
                  refine ⟨13898375854546241551654531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74124671224246621608824165 13898375854546241551654531)
                  ·
                    refine ⟨20847563781819362327481797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13898375854546241551654531 20847563781819362327481797)
                    ·
                      refine ⟨3908918209091130436402837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20847563781819362327481797 3908918209091130436402837)
                      ·
                        rfl

theorem cell23_7612591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_7612591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612591 prefixEnd_7612591 := by exact prefixLift 7612591
  have htrace : WordTrace (prefixWord ++ tailWord_7612591) baseStart_7612591 baseEnd_7612591 := by
    simpa [prefixWord, tailWord_7612591, baseEnd_7612591] using wordTrace_append hprefix tailTrace_7612591
  have hstable : (prefixWord ++ tailWord_7612591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612591).length < 2 ^ (prefixWord ++ tailWord_7612591).sum := by decide
  have hdescent : baseEnd_7612591 < baseStart_7612591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612618 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_7612618 : Nat := 118140960795 + 7612618 * 2 ^ 59
def prefixEnd_7612618 : Nat := 4983230072969 + 3 ^ 40 * 7612618 * 2
def baseEnd_7612618 : Nat := 1302977357689600610255071

theorem tailTrace_7612618 : CollatzResearch.WordTrace tailWord_7612618 prefixEnd_7612618 1302977357689600610255071 := by
  unfold tailWord_7612618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69413747183698148122685627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185103325823195061660495005 69413747183698148122685627)
  ·
    refine ⟨104120620775547222184028441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69413747183698148122685627 104120620775547222184028441)
    ·
      refine ⟨78090465581660416638021331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104120620775547222184028441 78090465581660416638021331)
      ·
        refine ⟨117135698372490624957031997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78090465581660416638021331 117135698372490624957031997)
        ·
          refine ⟨43925886889683984358886999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117135698372490624957031997 43925886889683984358886999)
          ·
            refine ⟨65888830334525976538330499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43925886889683984358886999 65888830334525976538330499)
            ·
              refine ⟨98833245501788964807495749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65888830334525976538330499 98833245501788964807495749)
              ·
                refine ⟨18531233531585430901405453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98833245501788964807495749 18531233531585430901405453)
                ·
                  refine ⟨6949212574344536588027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18531233531585430901405453 6949212574344536588027045)
                  ·
                    refine ⟨1302977357689600610255071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949212574344536588027045 1302977357689600610255071)
                    ·
                      rfl

theorem cell23_7612618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_7612618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612618 prefixEnd_7612618 := by exact prefixLift 7612618
  have htrace : WordTrace (prefixWord ++ tailWord_7612618) baseStart_7612618 baseEnd_7612618 := by
    simpa [prefixWord, tailWord_7612618, baseEnd_7612618] using wordTrace_append hprefix tailTrace_7612618
  have hstable : (prefixWord ++ tailWord_7612618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612618).length < 2 ^ (prefixWord ++ tailWord_7612618).sum := by decide
  have hdescent : baseEnd_7612618 < baseStart_7612618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612645 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7612645 : Nat := 118140960795 + 7612645 * 2 ^ 59
def prefixEnd_7612645 : Nat := 4983230072969 + 3 ^ 40 * 7612645 * 2
def baseEnd_7612645 : Nat := 3908945937046473225127589

theorem tailTrace_7612645 : CollatzResearch.WordTrace tailWord_7612645 prefixEnd_7612645 3908945937046473225127589 := by
  unfold tailWord_7612645
  simp only [CollatzResearch.WordTrace]
  refine ⟨277655973505694776101975389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185103982337129850734650259 277655973505694776101975389)
  ·
    refine ⟨104120990064635541038240771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277655973505694776101975389 104120990064635541038240771)
    ·
      refine ⟨156181485096953311557361157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104120990064635541038240771 156181485096953311557361157)
      ·
        refine ⟨29284028455678745917005217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156181485096953311557361157 29284028455678745917005217)
        ·
          refine ⟨21963021341759059437753913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29284028455678745917005217 21963021341759059437753913)
          ·
            refine ⟨16472266006319294578315435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21963021341759059437753913 16472266006319294578315435)
            ·
              refine ⟨24708399009478941867473153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472266006319294578315435 24708399009478941867473153)
              ·
                refine ⟨18531299257109206400604865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24708399009478941867473153 18531299257109206400604865)
                ·
                  refine ⟨13898474442831904800453649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18531299257109206400604865 13898474442831904800453649)
                  ·
                    refine ⟨10423855832123928600340237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898474442831904800453649 10423855832123928600340237)
                    ·
                      refine ⟨3908945937046473225127589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423855832123928600340237 3908945937046473225127589)
                      ·
                        rfl

theorem cell23_7612645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7612645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612645 prefixEnd_7612645 := by exact prefixLift 7612645
  have htrace : WordTrace (prefixWord ++ tailWord_7612645) baseStart_7612645 baseEnd_7612645 := by
    simpa [prefixWord, tailWord_7612645, baseEnd_7612645] using wordTrace_append hprefix tailTrace_7612645
  have hstable : (prefixWord ++ tailWord_7612645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612645).length < 2 ^ (prefixWord ++ tailWord_7612645).sum := by decide
  have hdescent : baseEnd_7612645 < baseStart_7612645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612652 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_7612652 : Nat := 118140960795 + 7612652 * 2 ^ 59
def prefixEnd_7612652 : Nat := 4983230072969 + 3 ^ 40 * 7612652 * 2
def baseEnd_7612652 : Nat := 1302983177137018232580019

theorem tailTrace_7612652 : CollatzResearch.WordTrace tailWord_7612652 prefixEnd_7612652 1302983177137018232580019 := by
  unfold tailWord_7612652
  simp only [CollatzResearch.WordTrace]
  refine ⟨138828114408334708148740105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185104152544446277531653473 138828114408334708148740105)
  ·
    refine ⟨104121085806251031111555079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138828114408334708148740105 104121085806251031111555079)
    ·
      refine ⟨156181628709376546667332619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104121085806251031111555079 156181628709376546667332619)
      ·
        refine ⟨234272443064064820000998929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156181628709376546667332619 234272443064064820000998929)
        ·
          refine ⟨175704332298048615000749197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234272443064064820000998929 175704332298048615000749197)
          ·
            refine ⟨65889124611768230625280949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175704332298048615000749197 65889124611768230625280949)
            ·
              refine ⟨6177105432353271621120089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65889124611768230625280949 6177105432353271621120089)
              ·
                refine ⟨4632829074264953715840067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177105432353271621120089 4632829074264953715840067)
                ·
                  refine ⟨6949243611397430573760101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632829074264953715840067 6949243611397430573760101)
                  ·
                    refine ⟨1302983177137018232580019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949243611397430573760101 1302983177137018232580019)
                    ·
                      rfl

theorem cell23_7612652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_7612652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612652 prefixEnd_7612652 := by exact prefixLift 7612652
  have htrace : WordTrace (prefixWord ++ tailWord_7612652) baseStart_7612652 baseEnd_7612652 := by
    simpa [prefixWord, tailWord_7612652, baseEnd_7612652] using wordTrace_append hprefix tailTrace_7612652
  have hstable : (prefixWord ++ tailWord_7612652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612652).length < 2 ^ (prefixWord ++ tailWord_7612652).sum := by decide
  have hdescent : baseEnd_7612652 < baseStart_7612652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612709 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_7612709 : Nat := 118140960795 + 7612709 * 2 ^ 59
def prefixEnd_7612709 : Nat := 4983230072969 + 3 ^ 40 * 7612709 * 2
def baseEnd_7612709 : Nat := 3908978799808360974727295

theorem tailTrace_7612709 : CollatzResearch.WordTrace tailWord_7612709 prefixEnd_7612709 3908978799808360974727295 := by
  unfold tailWord_7612709
  simp only [CollatzResearch.WordTrace]
  refine ⟨277658307777462915032305181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185105538518308610021536787 277658307777462915032305181)
  ·
    refine ⟨104121865416548593137114443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277658307777462915032305181 104121865416548593137114443)
    ·
      refine ⟨156182798124822889705671665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104121865416548593137114443 156182798124822889705671665)
      ·
        refine ⟨117137098593617167279253749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156182798124822889705671665 117137098593617167279253749)
        ·
          refine ⟨10981602993151609432430039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117137098593617167279253749 10981602993151609432430039)
          ·
            refine ⟨16472404489727414148645059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981602993151609432430039 16472404489727414148645059)
            ·
              refine ⟨24708606734591121222967589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472404489727414148645059 24708606734591121222967589)
              ·
                refine ⟨4632863762735835229306423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24708606734591121222967589 4632863762735835229306423)
                ·
                  refine ⟨6949295644103752843959635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632863762735835229306423 6949295644103752843959635)
                  ·
                    refine ⟨10423943466155629265939453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949295644103752843959635 10423943466155629265939453)
                    ·
                      refine ⟨3908978799808360974727295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423943466155629265939453 3908978799808360974727295)
                      ·
                        rfl

theorem cell23_7612709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_7612709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612709 prefixEnd_7612709 := by exact prefixLift 7612709
  have htrace : WordTrace (prefixWord ++ tailWord_7612709) baseStart_7612709 baseEnd_7612709 := by
    simpa [prefixWord, tailWord_7612709, baseEnd_7612709] using wordTrace_append hprefix tailTrace_7612709
  have hstable : (prefixWord ++ tailWord_7612709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612709).length < 2 ^ (prefixWord ++ tailWord_7612709).sum := by decide
  have hdescent : baseEnd_7612709 < baseStart_7612709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612725 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7612725 : Nat := 118140960795 + 7612725 * 2 ^ 59
def prefixEnd_7612725 : Nat := 4983230072969 + 3 ^ 40 * 7612725 * 2
def baseEnd_7612725 : Nat := 1302995671832944304042407

theorem tailTrace_7612725 : CollatzResearch.WordTrace tailWord_7612725 prefixEnd_7612725 1302995671832944304042407 := by
  unfold tailWord_7612725
  simp only [CollatzResearch.WordTrace]
  refine ⟨277658891345404949764887629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185105927563603299843258419 277658891345404949764887629)
  ·
    refine ⟨104122084254526856161832861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277658891345404949764887629 104122084254526856161832861)
    ·
      refine ⟨39045781595447571060687323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104122084254526856161832861 39045781595447571060687323)
      ·
        refine ⟨58568672393171356591030985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39045781595447571060687323 58568672393171356591030985)
        ·
          refine ⟨43926504294878517443273239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58568672393171356591030985 43926504294878517443273239)
          ·
            refine ⟨65889756442317776164909859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43926504294878517443273239 65889756442317776164909859)
            ·
              refine ⟨98834634663476664247364789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65889756442317776164909859 98834634663476664247364789)
              ·
                refine ⟨9265746999700937273190449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98834634663476664247364789 9265746999700937273190449)
                ·
                  refine ⟨6949310249775702954892837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265746999700937273190449 6949310249775702954892837)
                  ·
                    refine ⟨1302995671832944304042407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949310249775702954892837 1302995671832944304042407)
                    ·
                      rfl

theorem cell23_7612725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7612725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612725 prefixEnd_7612725 := by exact prefixLift 7612725
  have htrace : WordTrace (prefixWord ++ tailWord_7612725) baseStart_7612725 baseEnd_7612725 := by
    simpa [prefixWord, tailWord_7612725, baseEnd_7612725] using wordTrace_append hprefix tailTrace_7612725
  have hstable : (prefixWord ++ tailWord_7612725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612725).length < 2 ^ (prefixWord ++ tailWord_7612725).sum := by decide
  have hdescent : baseEnd_7612725 < baseStart_7612725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612728 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_7612728 : Nat := 118140960795 + 7612728 * 2 ^ 59
def prefixEnd_7612728 : Nat := 4983230072969 + 3 ^ 40 * 7612728 * 2
def baseEnd_7612728 : Nat := 3908988555940796400389707

theorem tailTrace_7612728 : CollatzResearch.WordTrace tailWord_7612728 prefixEnd_7612728 3908988555940796400389707 := by
  unfold tailWord_7612728
  simp only [CollatzResearch.WordTrace]
  refine ⟨138829500382197040638623419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185106000509596054184831225 138829500382197040638623419)
  ·
    refine ⟨208244250573295560957935129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138829500382197040638623419 208244250573295560957935129)
    ·
      refine ⟨156183187929971670718451347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208244250573295560957935129 156183187929971670718451347)
      ·
        refine ⟨234274781894957506077677021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156183187929971670718451347 234274781894957506077677021)
        ·
          refine ⟨87853043210609064779128883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234274781894957506077677021 87853043210609064779128883)
          ·
            refine ⟨131779564815913597168693325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87853043210609064779128883 131779564815913597168693325)
            ·
              refine ⟨49417336805967598938259997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131779564815913597168693325 49417336805967598938259997)
              ·
                refine ⟨18531501302237849601847499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49417336805967598938259997 18531501302237849601847499)
                ·
                  refine ⟨27797251953356774402771249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18531501302237849601847499 27797251953356774402771249)
                  ·
                    refine ⟨20847938965017580802078437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27797251953356774402771249 20847938965017580802078437)
                    ·
                      refine ⟨3908988555940796400389707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20847938965017580802078437 3908988555940796400389707)
                      ·
                        rfl

theorem cell23_7612728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_7612728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612728 prefixEnd_7612728 := by exact prefixLift 7612728
  have htrace : WordTrace (prefixWord ++ tailWord_7612728) baseStart_7612728 baseEnd_7612728 := by
    simpa [prefixWord, tailWord_7612728, baseEnd_7612728] using wordTrace_append hprefix tailTrace_7612728
  have hstable : (prefixWord ++ tailWord_7612728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612728).length < 2 ^ (prefixWord ++ tailWord_7612728).sum := by decide
  have hdescent : baseEnd_7612728 < baseStart_7612728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612732 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_7612732 : Nat := 118140960795 + 7612732 * 2 ^ 59
def prefixEnd_7612732 : Nat := 4983230072969 + 3 ^ 40 * 7612732 * 2
def baseEnd_7612732 : Nat := 3908990609863414384739689

theorem tailTrace_7612732 : CollatzResearch.WordTrace tailWord_7612732 prefixEnd_7612732 3908990609863414384739689 := by
  unfold tailWord_7612732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138829573328189794980196225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185106097770919726640261633 138829573328189794980196225)
  ·
    refine ⟨104122179996142346235147169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138829573328189794980196225 104122179996142346235147169)
    ·
      refine ⟨78091634997106759676360377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104122179996142346235147169 78091634997106759676360377)
      ·
        refine ⟨58568726247830069757270283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78091634997106759676360377 58568726247830069757270283)
        ·
          refine ⟨87853089371745104635905425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58568726247830069757270283 87853089371745104635905425)
          ·
            refine ⟨65889817028808828476929069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87853089371745104635905425 65889817028808828476929069)
            ·
              refine ⟨24708681385803310678848401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65889817028808828476929069 24708681385803310678848401)
              ·
                refine ⟨18531511039352483009136301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24708681385803310678848401 18531511039352483009136301)
                ·
                  refine ⟨6949316639757181128426113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18531511039352483009136301 6949316639757181128426113)
                  ·
                    refine ⟨5211987479817885846319585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949316639757181128426113 5211987479817885846319585)
                    ·
                      refine ⟨3908990609863414384739689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211987479817885846319585 3908990609863414384739689)
                      ·
                        rfl

theorem cell23_7612732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_7612732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612732 prefixEnd_7612732 := by exact prefixLift 7612732
  have htrace : WordTrace (prefixWord ++ tailWord_7612732) baseStart_7612732 baseEnd_7612732 := by
    simpa [prefixWord, tailWord_7612732, baseEnd_7612732] using wordTrace_append hprefix tailTrace_7612732
  have hstable : (prefixWord ++ tailWord_7612732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612732).length < 2 ^ (prefixWord ++ tailWord_7612732).sum := by decide
  have hdescent : baseEnd_7612732 < baseStart_7612732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612735 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_7612735 : Nat := 118140960795 + 7612735 * 2 ^ 59
def prefixEnd_7612735 : Nat := 4983230072969 + 3 ^ 40 * 7612735 * 2
def baseEnd_7612735 : Nat := 3908992150305377873002175

theorem tailTrace_7612735 : CollatzResearch.WordTrace tailWord_7612735 prefixEnd_7612735 3908992150305377873002175 := by
  unfold tailWord_7612735
  simp only [CollatzResearch.WordTrace]
  refine ⟨277659256075368721472751659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185106170716912480981834439 277659256075368721472751659)
  ·
    refine ⟨416488884113053082209127489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277659256075368721472751659 416488884113053082209127489)
    ·
      refine ⟨312366663084789811656845617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416488884113053082209127489 312366663084789811656845617)
      ·
        refine ⟨234274997313592358742634213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312366663084789811656845617 234274997313592358742634213)
        ·
          refine ⟨43926561996298567264243915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234274997313592358742634213 43926561996298567264243915)
          ·
            refine ⟨65889842994447850896365873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43926561996298567264243915 65889842994447850896365873)
            ·
              refine ⟨49417382245835888172274405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65889842994447850896365873 49417382245835888172274405)
              ·
                refine ⟨9265759171094229032301451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49417382245835888172274405 9265759171094229032301451)
                ·
                  refine ⟨13898638756641343548452177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265759171094229032301451 13898638756641343548452177)
                  ·
                    refine ⟨10423979067481007661339133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898638756641343548452177 10423979067481007661339133)
                    ·
                      refine ⟨3908992150305377873002175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10423979067481007661339133 3908992150305377873002175)
                      ·
                        rfl

theorem cell23_7612735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_7612735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612735 prefixEnd_7612735 := by exact prefixLift 7612735
  have htrace : WordTrace (prefixWord ++ tailWord_7612735) baseStart_7612735 baseEnd_7612735 := by
    simpa [prefixWord, tailWord_7612735, baseEnd_7612735] using wordTrace_append hprefix tailTrace_7612735
  have hstable : (prefixWord ++ tailWord_7612735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612735).length < 2 ^ (prefixWord ++ tailWord_7612735).sum := by decide
  have hdescent : baseEnd_7612735 < baseStart_7612735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612751 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 9]
def baseStart_7612751 : Nat := 118140960795 + 7612751 * 2 ^ 59
def prefixEnd_7612751 : Nat := 4983230072969 + 3 ^ 40 * 7612751 * 2
def baseEnd_7612751 : Nat := 1303000121998616603467367

theorem tailTrace_7612751 : CollatzResearch.WordTrace tailWord_7612751 prefixEnd_7612751 1303000121998616603467367 := by
  unfold tailWord_7612751
  simp only [CollatzResearch.WordTrace]
  refine ⟨277659839643310756205334107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185106559762207170803556071 277659839643310756205334107)
  ·
    refine ⟨416489759464966134308001161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277659839643310756205334107 416489759464966134308001161)
    ·
      refine ⟨312367319598724600731000871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416489759464966134308001161 312367319598724600731000871)
      ·
        refine ⟨468550979398086901096501307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312367319598724600731000871 468550979398086901096501307)
        ·
          refine ⟨702826469097130351644751961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468550979398086901096501307 702826469097130351644751961)
          ·
            refine ⟨527119851822847763733563971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702826469097130351644751961 527119851822847763733563971)
            ·
              refine ⟨790679777734271645600345957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527119851822847763733563971 790679777734271645600345957)
              ·
                refine ⟨148252458325175933550064867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790679777734271645600345957 148252458325175933550064867)
                ·
                  refine ⟨222378687487763900325097301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148252458325175933550064867 222378687487763900325097301)
                  ·
                    refine ⟨1303000121998616603467367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222378687487763900325097301 1303000121998616603467367)
                    ·
                      rfl

theorem cell23_7612751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_7612751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612751 prefixEnd_7612751 := by exact prefixLift 7612751
  have htrace : WordTrace (prefixWord ++ tailWord_7612751) baseStart_7612751 baseEnd_7612751 := by
    simpa [prefixWord, tailWord_7612751, baseEnd_7612751] using wordTrace_append hprefix tailTrace_7612751
  have hstable : (prefixWord ++ tailWord_7612751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612751).length < 2 ^ (prefixWord ++ tailWord_7612751).sum := by decide
  have hdescent : baseEnd_7612751 < baseStart_7612751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612752 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3]
def baseStart_7612752 : Nat := 118140960795 + 7612752 * 2 ^ 59
def prefixEnd_7612752 : Nat := 4983230072969 + 3 ^ 40 * 7612752 * 2
def baseEnd_7612752 : Nat := 3909000879476504306489597

theorem tailTrace_7612752 : CollatzResearch.WordTrace tailWord_7612752 prefixEnd_7612752 3909000879476504306489597 := by
  unfold tailWord_7612752
  simp only [CollatzResearch.WordTrace]
  refine ⟨138829938058153566688060255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185106584077538088917413673 138829938058153566688060255)
  ·
    refine ⟨208244907087230350032090383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138829938058153566688060255 208244907087230350032090383)
    ·
      refine ⟨312367360630845525048135575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208244907087230350032090383 312367360630845525048135575)
      ·
        refine ⟨468551040946268287572203363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312367360630845525048135575 468551040946268287572203363)
        ·
          refine ⟨702826561419402431358305045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468551040946268287572203363 702826561419402431358305045)
          ·
            refine ⟨32944995066534488969920549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 702826561419402431358305045 32944995066534488969920549)
            ·
              refine ⟨6177186574975216681860103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32944995066534488969920549 6177186574975216681860103)
              ·
                refine ⟨9265779862462825022790155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177186574975216681860103 9265779862462825022790155)
                ·
                  refine ⟨13898669793694237534185233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265779862462825022790155 13898669793694237534185233)
                  ·
                    refine ⟨10424002345270678150638925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898669793694237534185233 10424002345270678150638925)
                    ·
                      refine ⟨3909000879476504306489597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424002345270678150638925 3909000879476504306489597)
                      ·
                        rfl

theorem cell23_7612752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3].length) (baseStart_7612752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612752 prefixEnd_7612752 := by exact prefixLift 7612752
  have htrace : WordTrace (prefixWord ++ tailWord_7612752) baseStart_7612752 baseEnd_7612752 := by
    simpa [prefixWord, tailWord_7612752, baseEnd_7612752] using wordTrace_append hprefix tailTrace_7612752
  have hstable : (prefixWord ++ tailWord_7612752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612752).length < 2 ^ (prefixWord ++ tailWord_7612752).sum := by decide
  have hdescent : baseEnd_7612752 < baseStart_7612752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612805 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_7612805 : Nat := 118140960795 + 7612805 * 2 ^ 59
def prefixEnd_7612805 : Nat := 4983230072969 + 3 ^ 40 * 7612805 * 2
def baseEnd_7612805 : Nat := 3909028093951192599126853

theorem tailTrace_7612805 : CollatzResearch.WordTrace tailWord_7612805 prefixEnd_7612805 3909028093951192599126853 := by
  unfold tailWord_7612805
  simp only [CollatzResearch.WordTrace]
  refine ⟨277661809185115123427799869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185107872790076748951866579 277661809185115123427799869)
  ·
    refine ⟨104123178444418171285424951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277661809185115123427799869 104123178444418171285424951)
    ·
      refine ⟨156184767666627256928137427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104123178444418171285424951 156184767666627256928137427)
      ·
        refine ⟨234277151499940885392206141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156184767666627256928137427 234277151499940885392206141)
        ·
          refine ⟨87853931812477832022077303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234277151499940885392206141 87853931812477832022077303)
          ·
            refine ⟨131780897718716748033115955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87853931812477832022077303 131780897718716748033115955)
            ·
              refine ⟨197671346578075122049673933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131780897718716748033115955 197671346578075122049673933)
              ·
                refine ⟨74126754966778170768627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197671346578075122049673933 74126754966778170768627725)
                ·
                  refine ⟨27797533112541814038235397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74126754966778170768627725 27797533112541814038235397)
                  ·
                    refine ⟨5212037458601590132169137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27797533112541814038235397 5212037458601590132169137)
                    ·
                      refine ⟨3909028093951192599126853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212037458601590132169137 3909028093951192599126853)
                      ·
                        rfl

theorem cell23_7612805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_7612805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612805 prefixEnd_7612805 := by exact prefixLift 7612805
  have htrace : WordTrace (prefixWord ++ tailWord_7612805) baseStart_7612805 baseEnd_7612805 := by
    simpa [prefixWord, tailWord_7612805, baseEnd_7612805] using wordTrace_append hprefix tailTrace_7612805
  have hstable : (prefixWord ++ tailWord_7612805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612805).length < 2 ^ (prefixWord ++ tailWord_7612805).sum := by decide
  have hdescent : baseEnd_7612805 < baseStart_7612805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612833 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7612833 : Nat := 118140960795 + 7612833 * 2 ^ 59
def prefixEnd_7612833 : Nat := 4983230072969 + 3 ^ 40 * 7612833 * 2
def baseEnd_7612833 : Nat := 3909042471409518489576725

theorem tailTrace_7612833 : CollatzResearch.WordTrace tailWord_7612833 prefixEnd_7612833 3909042471409518489576725 := by
  unfold tailWord_7612833
  simp only [CollatzResearch.WordTrace]
  refine ⟨277662830429013684209819153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185108553619342456139879435 277662830429013684209819153)
  ·
    refine ⟨208247122821760263157364365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277662830429013684209819153 208247122821760263157364365)
    ·
      refine ⟨78092671058160098684011637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208247122821760263157364365 78092671058160098684011637)
      ·
        refine ⟨7321187911702509251626091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78092671058160098684011637 7321187911702509251626091)
        ·
          refine ⟨10981781867553763877439137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321187911702509251626091 10981781867553763877439137)
          ·
            refine ⟨8236336400665322908079353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981781867553763877439137 8236336400665322908079353)
            ·
              refine ⟨6177252300498992181059515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236336400665322908079353 6177252300498992181059515)
              ·
                refine ⟨9265878450748488271589273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177252300498992181059515 9265878450748488271589273)
                ·
                  refine ⟨6949408838061366203691955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9265878450748488271589273 6949408838061366203691955)
                  ·
                    refine ⟨10424113257092049305537933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949408838061366203691955 10424113257092049305537933)
                    ·
                      refine ⟨3909042471409518489576725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424113257092049305537933 3909042471409518489576725)
                      ·
                        rfl

theorem cell23_7612833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7612833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612833 prefixEnd_7612833 := by exact prefixLift 7612833
  have htrace : WordTrace (prefixWord ++ tailWord_7612833) baseStart_7612833 baseEnd_7612833 := by
    simpa [prefixWord, tailWord_7612833, baseEnd_7612833] using wordTrace_append hprefix tailTrace_7612833
  have hstable : (prefixWord ++ tailWord_7612833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612833).length < 2 ^ (prefixWord ++ tailWord_7612833).sum := by decide
  have hdescent : baseEnd_7612833 < baseStart_7612833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612858 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_7612858 : Nat := 118140960795 + 7612858 * 2 ^ 59
def prefixEnd_7612858 : Nat := 4983230072969 + 3 ^ 40 * 7612858 * 2
def baseEnd_7612858 : Nat := 1303018436141960297254703

theorem tailTrace_7612858 : CollatzResearch.WordTrace tailWord_7612858 prefixEnd_7612858 1303018436141960297254703 := by
  unfold tailWord_7612858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69415935563480778369869807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185109161502615408986319485 69415935563480778369869807)
  ·
    refine ⟨104123903345221167554804711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69415935563480778369869807 104123903345221167554804711)
    ·
      refine ⟨156185855017831751332207067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104123903345221167554804711 156185855017831751332207067)
      ·
        refine ⟨234278782526747626998310601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156185855017831751332207067 234278782526747626998310601)
        ·
          refine ⟨175709086895060720248732951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234278782526747626998310601 175709086895060720248732951)
          ·
            refine ⟨263563630342591080373099427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175709086895060720248732951 263563630342591080373099427)
            ·
              refine ⟨395345445513886620559649141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263563630342591080373099427 395345445513886620559649141)
              ·
                refine ⟨37063635516926870677467107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395345445513886620559649141 37063635516926870677467107)
                ·
                  refine ⟨55595453275390306016200661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37063635516926870677467107 55595453275390306016200661)
                  ·
                    refine ⟨1303018436141960297254703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55595453275390306016200661 1303018436141960297254703)
                    ·
                      rfl

theorem cell23_7612858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_7612858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612858 prefixEnd_7612858 := by exact prefixLift 7612858
  have htrace : WordTrace (prefixWord ++ tailWord_7612858) baseStart_7612858 baseEnd_7612858 := by
    simpa [prefixWord, tailWord_7612858, baseEnd_7612858] using wordTrace_append hprefix tailTrace_7612858
  have hstable : (prefixWord ++ tailWord_7612858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612858).length < 2 ^ (prefixWord ++ tailWord_7612858).sum := by decide
  have hdescent : baseEnd_7612858 < baseStart_7612858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612885 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7612885 : Nat := 118140960795 + 7612885 * 2 ^ 59
def prefixEnd_7612885 : Nat := 4983230072969 + 3 ^ 40 * 7612885 * 2
def baseEnd_7612885 : Nat := 3909069172403552286126485

theorem tailTrace_7612885 : CollatzResearch.WordTrace tailWord_7612885 prefixEnd_7612885 3909069172403552286126485 := by
  unfold tailWord_7612885
  simp only [CollatzResearch.WordTrace]
  refine ⟨277664727024825297090712109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185109818016550198060474739 277664727024825297090712109)
  ·
    refine ⟨104124272634309486409017041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277664727024825297090712109 104124272634309486409017041)
    ·
      refine ⟨78093204475732114806762781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104124272634309486409017041 78093204475732114806762781)
      ·
        refine ⟨29284951678399543052536043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78093204475732114806762781 29284951678399543052536043)
        ·
          refine ⟨43927427517599314578804065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29284951678399543052536043 43927427517599314578804065)
          ·
            refine ⟨32945570638199485934103049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43927427517599314578804065 32945570638199485934103049)
            ·
              refine ⟨24709177978649614450577287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32945570638199485934103049 24709177978649614450577287)
              ·
                refine ⟨37063766967974421675865931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24709177978649614450577287 37063766967974421675865931)
                ·
                  refine ⟨55595650451961632513798897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37063766967974421675865931 55595650451961632513798897)
                  ·
                    refine ⟨41696737838971224385349173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55595650451961632513798897 41696737838971224385349173)
                    ·
                      refine ⟨3909069172403552286126485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41696737838971224385349173 3909069172403552286126485)
                      ·
                        rfl

theorem cell23_7612885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7612885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612885 prefixEnd_7612885 := by exact prefixLift 7612885
  have htrace : WordTrace (prefixWord ++ tailWord_7612885) baseStart_7612885 baseEnd_7612885 := by
    simpa [prefixWord, tailWord_7612885, baseEnd_7612885] using wordTrace_append hprefix tailTrace_7612885
  have hstable : (prefixWord ++ tailWord_7612885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612885).length < 2 ^ (prefixWord ++ tailWord_7612885).sum := by decide
  have hdescent : baseEnd_7612885 < baseStart_7612885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612888 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_7612888 : Nat := 118140960795 + 7612888 * 2 ^ 59
def prefixEnd_7612888 : Nat := 4983230072969 + 3 ^ 40 * 7612888 * 2
def baseEnd_7612888 : Nat := 1303023570948505258129657

theorem tailTrace_7612888 : CollatzResearch.WordTrace tailWord_7612888 prefixEnd_7612888 1303023570948505258129657 := by
  unfold tailWord_7612888
  simp only [CollatzResearch.WordTrace]
  refine ⟨138832418221907214301535659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185109890962542952402047545 138832418221907214301535659)
  ·
    refine ⟨208248627332860821452303489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138832418221907214301535659 208248627332860821452303489)
    ·
      refine ⟨156186470499645616089227617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208248627332860821452303489 156186470499645616089227617)
      ·
        refine ⟨117139852874734212066920713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156186470499645616089227617 117139852874734212066920713)
        ·
          refine ⟨87854889656050659050190535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117139852874734212066920713 87854889656050659050190535)
          ·
            refine ⟨131782334484075988575285803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87854889656050659050190535 131782334484075988575285803)
            ·
              refine ⟨197673501726113982862928705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131782334484075988575285803 197673501726113982862928705)
              ·
                refine ⟨148255126294585487147196529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197673501726113982862928705 148255126294585487147196529)
                ·
                  refine ⟨111191344720939115360397397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148255126294585487147196529 111191344720939115360397397)
                  ·
                    refine ⟨1303023570948505258129657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111191344720939115360397397 1303023570948505258129657)
                    ·
                      rfl

theorem cell23_7612888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_7612888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612888 prefixEnd_7612888 := by exact prefixLift 7612888
  have htrace : WordTrace (prefixWord ++ tailWord_7612888) baseStart_7612888 baseEnd_7612888 := by
    simpa [prefixWord, tailWord_7612888, baseEnd_7612888] using wordTrace_append hprefix tailTrace_7612888
  have hstable : (prefixWord ++ tailWord_7612888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612888).length < 2 ^ (prefixWord ++ tailWord_7612888).sum := by decide
  have hdescent : baseEnd_7612888 < baseStart_7612888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612909 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7612909 : Nat := 118140960795 + 7612909 * 2 ^ 59
def prefixEnd_7612909 : Nat := 4983230072969 + 3 ^ 40 * 7612909 * 2
def baseEnd_7612909 : Nat := 1303027165313086730742125

theorem tailTrace_7612909 : CollatzResearch.WordTrace tailWord_7612909 prefixEnd_7612909 1303027165313086730742125 := by
  unfold tailWord_7612909
  simp only [CollatzResearch.WordTrace]
  refine ⟨277665602376738349189585781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185110401584492232793057187 277665602376738349189585781)
  ·
    refine ⟨26031150222819220236523667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277665602376738349189585781 26031150222819220236523667)
    ·
      refine ⟨39046725334228830354785501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26031150222819220236523667 39046725334228830354785501)
      ·
        refine ⟨14642522000335811383044563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39046725334228830354785501 14642522000335811383044563)
        ·
          refine ⟨21963783000503717074566845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642522000335811383044563 21963783000503717074566845)
          ·
            refine ⟨8236418625188893902962567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21963783000503717074566845 8236418625188893902962567)
            ·
              refine ⟨12354627937783340854443851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236418625188893902962567 12354627937783340854443851)
              ·
                refine ⟨18531941906675011281665777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12354627937783340854443851 18531941906675011281665777)
                ·
                  refine ⟨13898956430006258461249333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18531941906675011281665777 13898956430006258461249333)
                  ·
                    refine ⟨1303027165313086730742125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13898956430006258461249333 1303027165313086730742125)
                    ·
                      rfl

theorem cell23_7612909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7612909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612909 prefixEnd_7612909 := by exact prefixLift 7612909
  have htrace : WordTrace (prefixWord ++ tailWord_7612909) baseStart_7612909 baseEnd_7612909 := by
    simpa [prefixWord, tailWord_7612909, baseEnd_7612909] using wordTrace_append hprefix tailTrace_7612909
  have hstable : (prefixWord ++ tailWord_7612909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612909).length < 2 ^ (prefixWord ++ tailWord_7612909).sum := by decide
  have hdescent : baseEnd_7612909 < baseStart_7612909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612915 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3]
def baseStart_7612915 : Nat := 118140960795 + 7612915 * 2 ^ 59
def prefixEnd_7612915 : Nat := 4983230072969 + 3 ^ 40 * 7612915 * 2
def baseEnd_7612915 : Nat := 3909084576823187168751347

theorem tailTrace_7612915 : CollatzResearch.WordTrace tailWord_7612915 prefixEnd_7612915 3909084576823187168751347 := by
  unfold tailWord_7612915
  simp only [CollatzResearch.WordTrace]
  refine ⟨277665821214716612214304199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185110547476477741476202799 277665821214716612214304199)
  ·
    refine ⟨416498731822074918321456299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277665821214716612214304199 416498731822074918321456299)
    ·
      refine ⟨624748097733112377482184449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416498731822074918321456299 624748097733112377482184449)
      ·
        refine ⟨468561073299834283111638337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624748097733112377482184449 468561073299834283111638337)
        ·
          refine ⟨351420804974875712333728753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468561073299834283111638337 351420804974875712333728753)
          ·
            refine ⟨263565603731156784250296565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351420804974875712333728753 263565603731156784250296565)
            ·
              refine ⟨24709275349795948523465303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263565603731156784250296565 24709275349795948523465303)
              ·
                refine ⟨37063913024693922785197955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24709275349795948523465303 37063913024693922785197955)
                ·
                  refine ⟨55595869537040884177796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37063913024693922785197955 55595869537040884177796933)
                  ·
                    refine ⟨10424225538195165783336925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55595869537040884177796933 10424225538195165783336925)
                    ·
                      refine ⟨3909084576823187168751347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424225538195165783336925 3909084576823187168751347)
                      ·
                        rfl

theorem cell23_7612915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_7612915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612915 prefixEnd_7612915 := by exact prefixLift 7612915
  have htrace : WordTrace (prefixWord ++ tailWord_7612915) baseStart_7612915 baseEnd_7612915 := by
    simpa [prefixWord, tailWord_7612915, baseEnd_7612915] using wordTrace_append hprefix tailTrace_7612915
  have hstable : (prefixWord ++ tailWord_7612915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612915).length < 2 ^ (prefixWord ++ tailWord_7612915).sum := by decide
  have hdescent : baseEnd_7612915 < baseStart_7612915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612928 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_7612928 : Nat := 118140960795 + 7612928 * 2 ^ 59
def prefixEnd_7612928 : Nat := 4983230072969 + 3 ^ 40 * 7612928 * 2
def baseEnd_7612928 : Nat := 3909091252071695617888787

theorem tailTrace_7612928 : CollatzResearch.WordTrace tailWord_7612928 prefixEnd_7612928 3909091252071695617888787 := by
  unfold tailWord_7612928
  simp only [CollatzResearch.WordTrace]
  refine ⟨138833147681834757717263719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185110863575779676956351625 138833147681834757717263719)
  ·
    refine ⟨208249721522752136575895579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138833147681834757717263719 208249721522752136575895579)
    ·
      refine ⟨312374582284128204863843369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208249721522752136575895579 312374582284128204863843369)
      ·
        refine ⟨234280936713096153647882527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312374582284128204863843369 234280936713096153647882527)
        ·
          refine ⟨351421405069644230471823791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234280936713096153647882527 351421405069644230471823791)
          ·
            refine ⟨527132107604466345707735687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351421405069644230471823791 527132107604466345707735687)
            ·
              refine ⟨790698161406699518561603531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527132107604466345707735687 790698161406699518561603531)
              ·
                refine ⟨1186047242110049277842405297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790698161406699518561603531 1186047242110049277842405297)
                ·
                  refine ⟨889535431582536958381803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1186047242110049277842405297 889535431582536958381803973)
                  ·
                    refine ⟨166787893421725679696588245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889535431582536958381803973 166787893421725679696588245)
                    ·
                      refine ⟨3909091252071695617888787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166787893421725679696588245 3909091252071695617888787)
                      ·
                        rfl

theorem cell23_7612928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_7612928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612928 prefixEnd_7612928 := by exact prefixLift 7612928
  have htrace : WordTrace (prefixWord ++ tailWord_7612928) baseStart_7612928 baseEnd_7612928 := by
    simpa [prefixWord, tailWord_7612928, baseEnd_7612928] using wordTrace_append hprefix tailTrace_7612928
  have hstable : (prefixWord ++ tailWord_7612928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612928).length < 2 ^ (prefixWord ++ tailWord_7612928).sum := by decide
  have hdescent : baseEnd_7612928 < baseStart_7612928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612939 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 1, 4]
def baseStart_7612939 : Nat := 118140960795 + 7612939 * 2 ^ 59
def prefixEnd_7612939 : Nat := 4983230072969 + 3 ^ 40 * 7612939 * 2
def baseEnd_7612939 : Nat := 1303032300119631691617079

theorem tailTrace_7612939 : CollatzResearch.WordTrace tailWord_7612939 prefixEnd_7612939 1303032300119631691617079 := by
  unfold tailWord_7612939
  simp only [CollatzResearch.WordTrace]
  refine ⟨277666696566629664313177871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185111131044419776208785247 277666696566629664313177871)
  ·
    refine ⟨416500044849944496469766807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277666696566629664313177871 416500044849944496469766807)
    ·
      refine ⟨624750067274916744704650211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416500044849944496469766807 624750067274916744704650211)
      ·
        refine ⟨937125100912375117056975317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624750067274916744704650211 937125100912375117056975317)
        ·
          refine ⟨21963869552633791806022859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 937125100912375117056975317 21963869552633791806022859)
          ·
            refine ⟨32945804328950687709034289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21963869552633791806022859 32945804328950687709034289)
            ·
              refine ⟨24709353246713015781775717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32945804328950687709034289 24709353246713015781775717)
              ·
                refine ⟨4633003733758690459082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24709353246713015781775717 4633003733758690459082947)
                ·
                  refine ⟨6949505600638035688624421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633003733758690459082947 6949505600638035688624421)
                  ·
                    refine ⟨1303032300119631691617079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949505600638035688624421 1303032300119631691617079)
                    ·
                      rfl

theorem cell23_7612939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 4].length) (baseStart_7612939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612939 prefixEnd_7612939 := by exact prefixLift 7612939
  have htrace : WordTrace (prefixWord ++ tailWord_7612939) baseStart_7612939 baseEnd_7612939 := by
    simpa [prefixWord, tailWord_7612939, baseEnd_7612939] using wordTrace_append hprefix tailTrace_7612939
  have hstable : (prefixWord ++ tailWord_7612939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612939).length < 2 ^ (prefixWord ++ tailWord_7612939).sum := by decide
  have hdescent : baseEnd_7612939 < baseStart_7612939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612965 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_7612965 : Nat := 118140960795 + 7612965 * 2 ^ 59
def prefixEnd_7612965 : Nat := 4983230072969 + 3 ^ 40 * 7612965 * 2
def baseEnd_7612965 : Nat := 1303036750285303991042039

theorem tailTrace_7612965 : CollatzResearch.WordTrace tailWord_7612965 prefixEnd_7612965 1303036750285303991042039 := by
  unfold tailWord_7612965
  simp only [CollatzResearch.WordTrace]
  refine ⟨277667644864535470753624349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185111763243023647169082899 277667644864535470753624349)
  ·
    refine ⟨104125366824200801532609131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277667644864535470753624349 104125366824200801532609131)
    ·
      refine ⟨156188050236301202298913697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104125366824200801532609131 156188050236301202298913697)
      ·
        refine ⟨117141037677225901724185273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156188050236301202298913697 117141037677225901724185273)
        ·
          refine ⟨87855778257919426293138955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117141037677225901724185273 87855778257919426293138955)
          ·
            refine ⟨131783667386879139439708433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87855778257919426293138955 131783667386879139439708433)
            ·
              refine ⟨98837750540159354579781325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131783667386879139439708433 98837750540159354579781325)
              ·
                refine ⟨37064156452559757967417997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98837750540159354579781325 37064156452559757967417997)
                ·
                  refine ⟨13899058669709909237781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37064156452559757967417997 13899058669709909237781749)
                  ·
                    refine ⟨1303036750285303991042039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13899058669709909237781749 1303036750285303991042039)
                    ·
                      rfl

theorem cell23_7612965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_7612965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612965 prefixEnd_7612965 := by exact prefixLift 7612965
  have htrace : WordTrace (prefixWord ++ tailWord_7612965) baseStart_7612965 baseEnd_7612965 := by
    simpa [prefixWord, tailWord_7612965, baseEnd_7612965] using wordTrace_append hprefix tailTrace_7612965
  have hstable : (prefixWord ++ tailWord_7612965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612965).length < 2 ^ (prefixWord ++ tailWord_7612965).sum := by decide
  have hdescent : baseEnd_7612965 < baseStart_7612965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_7612972 : Nat := 118140960795 + 7612972 * 2 ^ 59
def prefixEnd_7612972 : Nat := 4983230072969 + 3 ^ 40 * 7612972 * 2
def baseEnd_7612972 : Nat := 3909113845220493445738585

theorem tailTrace_7612972 : CollatzResearch.WordTrace tailWord_7612972 prefixEnd_7612972 3909113845220493445738585 := by
  unfold tailWord_7612972
  simp only [CollatzResearch.WordTrace]
  refine ⟨138833950087755055474564585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185111933450340073966086113 138833950087755055474564585)
  ·
    refine ⟨104125462565816291605923439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138833950087755055474564585 104125462565816291605923439)
    ·
      refine ⟨156188193848724437408885159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104125462565816291605923439 156188193848724437408885159)
      ·
        refine ⟨234282290773086656113327739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156188193848724437408885159 234282290773086656113327739)
        ·
          refine ⟨351423436159629984169991609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234282290773086656113327739 351423436159629984169991609)
          ·
            refine ⟨263567577119722488127493707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351423436159629984169991609 263567577119722488127493707)
            ·
              refine ⟨395351365679583732191240561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263567577119722488127493707 395351365679583732191240561)
              ·
                refine ⟨296513524259687799143430421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395351365679583732191240561 296513524259687799143430421)
                ·
                  refine ⟨13899071449672865584848301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296513524259687799143430421 13899071449672865584848301)
                  ·
                    refine ⟨5212151793627324594318113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13899071449672865584848301 5212151793627324594318113)
                    ·
                      refine ⟨3909113845220493445738585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212151793627324594318113 3909113845220493445738585)
                      ·
                        rfl

theorem cell23_7612972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_7612972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612972 prefixEnd_7612972 := by exact prefixLift 7612972
  have htrace : WordTrace (prefixWord ++ tailWord_7612972) baseStart_7612972 baseEnd_7612972 := by
    simpa [prefixWord, tailWord_7612972, baseEnd_7612972] using wordTrace_append hprefix tailTrace_7612972
  have hstable : (prefixWord ++ tailWord_7612972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612972).length < 2 ^ (prefixWord ++ tailWord_7612972).sum := by decide
  have hdescent : baseEnd_7612972 < baseStart_7612972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612989 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7612989 : Nat := 118140960795 + 7612989 * 2 ^ 59
def prefixEnd_7612989 : Nat := 4983230072969 + 3 ^ 40 * 7612989 * 2
def baseEnd_7612989 : Nat := 3909122574391619879226007

theorem tailTrace_7612989 : CollatzResearch.WordTrace tailWord_7612989 prefixEnd_7612989 3909122574391619879226007 := by
  unfold tailWord_7612989
  simp only [CollatzResearch.WordTrace]
  refine ⟨277668520216448522852498021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185112346810965681901665347 277668520216448522852498021)
  ·
    refine ⟨52062847540584098034843379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277668520216448522852498021 52062847540584098034843379)
    ·
      refine ⟨78094271310876147052265069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52062847540584098034843379 78094271310876147052265069)
      ·
        refine ⟨29285351741578555144599401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78094271310876147052265069 29285351741578555144599401)
        ·
          refine ⟨21964013806183916358449551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29285351741578555144599401 21964013806183916358449551)
          ·
            refine ⟨32946020709275874537674327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21964013806183916358449551 32946020709275874537674327)
            ·
              refine ⟨49419031063913811806511491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32946020709275874537674327 49419031063913811806511491)
              ·
                refine ⟨74128546595870717709767237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49419031063913811806511491 74128546595870717709767237)
                ·
                  refine ⟨13899102486725759570581357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74128546595870717709767237 13899102486725759570581357)
                  ·
                    refine ⟨5212163432522159838968009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13899102486725759570581357 5212163432522159838968009)
                    ·
                      refine ⟨3909122574391619879226007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212163432522159838968009 3909122574391619879226007)
                      ·
                        rfl

theorem cell23_7612989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7612989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612989 prefixEnd_7612989 := by exact prefixLift 7612989
  have htrace : WordTrace (prefixWord ++ tailWord_7612989) baseStart_7612989 baseEnd_7612989 := by
    simpa [prefixWord, tailWord_7612989, baseEnd_7612989] using wordTrace_append hprefix tailTrace_7612989
  have hstable : (prefixWord ++ tailWord_7612989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612989).length < 2 ^ (prefixWord ++ tailWord_7612989).sum := by decide
  have hdescent : baseEnd_7612989 < baseStart_7612989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7612990 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7612990 : Nat := 118140960795 + 7612990 * 2 ^ 59
def prefixEnd_7612990 : Nat := 4983230072969 + 3 ^ 40 * 7612990 * 2
def baseEnd_7612990 : Nat := 1303041029290758125104501

theorem tailTrace_7612990 : CollatzResearch.WordTrace tailWord_7612990 prefixEnd_7612990 1303041029290758125104501 := by
  unfold tailWord_7612990
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708569586180612502910553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185112371126296600015522949 34708569586180612502910553)
  ·
    refine ⟨26031427189635459377182915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34708569586180612502910553 26031427189635459377182915)
    ·
      refine ⟨39047140784453189065774373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26031427189635459377182915 39047140784453189065774373)
      ·
        refine ⟨7321338897084972949832695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39047140784453189065774373 7321338897084972949832695)
        ·
          refine ⟨10982008345627459424749043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321338897084972949832695 10982008345627459424749043)
          ·
            refine ⟨16473012518441189137123565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982008345627459424749043 16473012518441189137123565)
            ·
              refine ⟨6177379694415445926421337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16473012518441189137123565 6177379694415445926421337)
              ·
                refine ⟨4633034770811584444816003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177379694415445926421337 4633034770811584444816003)
                ·
                  refine ⟨6949552156217376667224005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633034770811584444816003 6949552156217376667224005)
                  ·
                    refine ⟨1303041029290758125104501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949552156217376667224005 1303041029290758125104501)
                    ·
                      rfl

theorem cell23_7612990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7612990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7612990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7612990 prefixEnd_7612990 := by exact prefixLift 7612990
  have htrace : WordTrace (prefixWord ++ tailWord_7612990) baseStart_7612990 baseEnd_7612990 := by
    simpa [prefixWord, tailWord_7612990, baseEnd_7612990] using wordTrace_append hprefix tailTrace_7612990
  have hstable : (prefixWord ++ tailWord_7612990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7612990).length < 2 ^ (prefixWord ++ tailWord_7612990).sum := by decide
  have hdescent : baseEnd_7612990 < baseStart_7612990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7612990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613015 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_7613015 : Nat := 118140960795 + 7613015 * 2 ^ 59
def prefixEnd_7613015 : Nat := 4983230072969 + 3 ^ 40 * 7613015 * 2
def baseEnd_7613015 : Nat := 3909135924888636777500887

theorem tailTrace_7613015 : CollatzResearch.WordTrace tailWord_7613015 prefixEnd_7613015 3909135924888636777500887 := by
  unfold tailWord_7613015
  simp only [CollatzResearch.WordTrace]
  refine ⟨277669468514354329292944499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185112979009569552861962999 277669468514354329292944499)
  ·
    refine ⟨416504202771531493939416749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277669468514354329292944499 416504202771531493939416749)
    ·
      refine ⟨156189076039324310227281281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416504202771531493939416749 156189076039324310227281281)
      ·
        refine ⟨117141807029493232670460961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156189076039324310227281281 117141807029493232670460961)
        ·
          refine ⟨87856355272119924502845721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117141807029493232670460961 87856355272119924502845721)
          ·
            refine ⟨65892266454089943377134291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87856355272119924502845721 65892266454089943377134291)
            ·
              refine ⟨98838399681134915065701437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65892266454089943377134291 98838399681134915065701437)
              ·
                refine ⟨37064399880425593149638039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98838399681134915065701437 37064399880425593149638039)
                ·
                  refine ⟨55596599820638389724457059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37064399880425593149638039 55596599820638389724457059)
                  ·
                    refine ⟨83394899730957584586685589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55596599820638389724457059 83394899730957584586685589)
                    ·
                      refine ⟨3909135924888636777500887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83394899730957584586685589 3909135924888636777500887)
                      ·
                        rfl

theorem cell23_7613015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_7613015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613015 prefixEnd_7613015 := by exact prefixLift 7613015
  have htrace : WordTrace (prefixWord ++ tailWord_7613015) baseStart_7613015 baseEnd_7613015 := by
    simpa [prefixWord, tailWord_7613015, baseEnd_7613015] using wordTrace_append hprefix tailTrace_7613015
  have hstable : (prefixWord ++ tailWord_7613015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613015).length < 2 ^ (prefixWord ++ tailWord_7613015).sum := by decide
  have hdescent : baseEnd_7613015 < baseStart_7613015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613025 : List Nat := [1, 2, 3, 1, 1, 4, 2, 9]
def baseStart_7613025 : Nat := 118140960795 + 7613025 * 2 ^ 59
def prefixEnd_7613025 : Nat := 4983230072969 + 3 ^ 40 * 7613025 * 2
def baseEnd_7613025 : Nat := 144783002210932656976883

theorem tailTrace_7613025 : CollatzResearch.WordTrace tailWord_7613025 prefixEnd_7613025 144783002210932656976883 := by
  unfold tailWord_7613025
  simp only [CollatzResearch.WordTrace]
  refine ⟨277669833244318101000808529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185113222162878734000539019 277669833244318101000808529)
  ·
    refine ⟨208252374933238575750606397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277669833244318101000808529 208252374933238575750606397)
    ·
      refine ⟨78094640599964465906477399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208252374933238575750606397 78094640599964465906477399)
      ·
        refine ⟨117141960899946698859716099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78094640599964465906477399 117141960899946698859716099)
        ·
          refine ⟨175712941349920048289574149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117141960899946698859716099 175712941349920048289574149)
          ·
            refine ⟨32946176503110009054295153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175712941349920048289574149 32946176503110009054295153)
            ·
              refine ⟨24709632377332506790721365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32946176503110009054295153 24709632377332506790721365)
              ·
                refine ⟨144783002210932656976883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24709632377332506790721365 144783002210932656976883)
                ·
                  rfl

theorem cell23_7613025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 9].length) (baseStart_7613025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613025 prefixEnd_7613025 := by exact prefixLift 7613025
  have htrace : WordTrace (prefixWord ++ tailWord_7613025) baseStart_7613025 baseEnd_7613025 := by
    simpa [prefixWord, tailWord_7613025, baseEnd_7613025] using wordTrace_append hprefix tailTrace_7613025
  have hstable : (prefixWord ++ tailWord_7613025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613025).length < 2 ^ (prefixWord ++ tailWord_7613025).sum := by decide
  have hdescent : baseEnd_7613025 < baseStart_7613025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613042 : List Nat := [3, 2, 1, 2, 5, 10]
def baseStart_7613042 : Nat := 118140960795 + 7613042 * 2 ^ 59
def prefixEnd_7613042 : Nat := 4983230072969 + 3 ^ 40 * 7613042 * 2
def baseEnd_7613042 : Nat := 16087036168174107703141

theorem tailTrace_7613042 : CollatzResearch.WordTrace tailWord_7613042 prefixEnd_7613042 16087036168174107703141 := by
  unfold tailWord_7613042
  simp only [CollatzResearch.WordTrace]
  refine ⟨69417613321314128226044345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185113635523504341936118253 69417613321314128226044345)
  ·
    refine ⟨52063209990985596169533259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69417613321314128226044345 52063209990985596169533259)
    ·
      refine ⟨78094814986478394254299889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52063209990985596169533259 78094814986478394254299889)
      ·
        refine ⟨58571111239858795690724917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78094814986478394254299889 58571111239858795690724917)
        ·
          refine ⟨5491041678736762096005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58571111239858795690724917 5491041678736762096005461)
          ·
            refine ⟨16087036168174107703141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5491041678736762096005461 16087036168174107703141)
            ·
              rfl

theorem cell23_7613042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 10].length) (baseStart_7613042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613042 prefixEnd_7613042 := by exact prefixLift 7613042
  have htrace : WordTrace (prefixWord ++ tailWord_7613042) baseStart_7613042 baseEnd_7613042 := by
    simpa [prefixWord, tailWord_7613042, baseEnd_7613042] using wordTrace_append hprefix tailTrace_7613042
  have hstable : (prefixWord ++ tailWord_7613042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613042).length < 2 ^ (prefixWord ++ tailWord_7613042).sum := by decide
  have hdescent : baseEnd_7613042 < baseStart_7613042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613065 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_7613065 : Nat := 118140960795 + 7613065 * 2 ^ 59
def prefixEnd_7613065 : Nat := 4983230072969 + 3 ^ 40 * 7613065 * 2
def baseEnd_7613065 : Nat := 3909161598921361581875657

theorem tailTrace_7613065 : CollatzResearch.WordTrace tailWord_7613065 prefixEnd_7613065 3909161598921361581875657 := by
  unfold tailWord_7613065
  simp only [CollatzResearch.WordTrace]
  refine ⟨277671292164173187832264649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185114194776115458554843099 277671292164173187832264649)
  ·
    refine ⟨208253469123129890874198487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277671292164173187832264649 208253469123129890874198487)
    ·
      refine ⟨312380203684694836311297731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208253469123129890874198487 312380203684694836311297731)
      ·
        refine ⟨468570305527042254466946597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312380203684694836311297731 468570305527042254466946597)
        ·
          refine ⟨87856932286320422712552487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468570305527042254466946597 87856932286320422712552487)
          ·
            refine ⟨131785398429480634068828731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87856932286320422712552487 131785398429480634068828731)
            ·
              refine ⟨197678097644220951103243097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131785398429480634068828731 197678097644220951103243097)
              ·
                refine ⟨148258573233165713327432323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197678097644220951103243097 148258573233165713327432323)
                ·
                  refine ⟨222387859849748569991148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148258573233165713327432323 222387859849748569991148485)
                  ·
                    refine ⟨41697723721827856873340341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222387859849748569991148485 41697723721827856873340341)
                    ·
                      refine ⟨3909161598921361581875657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41697723721827856873340341 3909161598921361581875657)
                      ·
                        rfl

theorem cell23_7613065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_7613065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613065 prefixEnd_7613065 := by exact prefixLift 7613065
  have htrace : WordTrace (prefixWord ++ tailWord_7613065) baseStart_7613065 baseEnd_7613065 := by
    simpa [prefixWord, tailWord_7613065, baseEnd_7613065] using wordTrace_append hprefix tailTrace_7613065
  have hstable : (prefixWord ++ tailWord_7613065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613065).length < 2 ^ (prefixWord ++ tailWord_7613065).sum := by decide
  have hdescent : baseEnd_7613065 < baseStart_7613065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613079 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_7613079 : Nat := 118140960795 + 7613079 * 2 ^ 59
def prefixEnd_7613079 : Nat := 4983230072969 + 3 ^ 40 * 7613079 * 2
def baseEnd_7613079 : Nat := 3909168787650524527100593

theorem tailTrace_7613079 : CollatzResearch.WordTrace tailWord_7613079 prefixEnd_7613079 3909168787650524527100593 := by
  unfold tailWord_7613079
  simp only [CollatzResearch.WordTrace]
  refine ⟨277671802786122468223274291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185114535190748312148849527 277671802786122468223274291)
  ·
    refine ⟨416507704179183702334911437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277671802786122468223274291 416507704179183702334911437)
    ·
      refine ⟨156190389067193888375591789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416507704179183702334911437 156190389067193888375591789)
      ·
        refine ⟨58571395900197708140846921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156190389067193888375591789 58571395900197708140846921)
        ·
          refine ⟨43928546925148281105635191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58571395900197708140846921 43928546925148281105635191)
          ·
            refine ⟨65892820387722421658452787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43928546925148281105635191 65892820387722421658452787)
            ·
              refine ⟨98839230581583632487679181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65892820387722421658452787 98839230581583632487679181)
              ·
                refine ⟨37064711468093862182879693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98839230581583632487679181 37064711468093862182879693)
                ·
                  refine ⟨13899266800535198318579885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37064711468093862182879693 13899266800535198318579885)
                  ·
                    refine ⟨5212225050200699369467457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13899266800535198318579885 5212225050200699369467457)
                    ·
                      refine ⟨3909168787650524527100593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212225050200699369467457 3909168787650524527100593)
                      ·
                        rfl

theorem cell23_7613079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_7613079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613079 prefixEnd_7613079 := by exact prefixLift 7613079
  have htrace : WordTrace (prefixWord ++ tailWord_7613079) baseStart_7613079 baseEnd_7613079 := by
    simpa [prefixWord, tailWord_7613079, baseEnd_7613079] using wordTrace_append hprefix tailTrace_7613079
  have hstable : (prefixWord ++ tailWord_7613079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613079).length < 2 ^ (prefixWord ++ tailWord_7613079).sum := by decide
  have hdescent : baseEnd_7613079 < baseStart_7613079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613086 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7613086 : Nat := 118140960795 + 7613086 * 2 ^ 59
def prefixEnd_7613086 : Nat := 4983230072969 + 3 ^ 40 * 7613086 * 2
def baseEnd_7613086 : Nat := 3909172382015105999713061

theorem tailTrace_7613086 : CollatzResearch.WordTrace tailWord_7613086 prefixEnd_7613086 3909172382015105999713061 := by
  unfold tailWord_7613086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34709007262137138552347389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185114705398064738945852741 34709007262137138552347389)
  ·
    refine ⟨13015877723301426957130271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34709007262137138552347389 13015877723301426957130271)
    ·
      refine ⟨19523816584952140435695407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015877723301426957130271 19523816584952140435695407)
      ·
        refine ⟨29285724877428210653543111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19523816584952140435695407 29285724877428210653543111)
        ·
          refine ⟨43928587316142315980314667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29285724877428210653543111 43928587316142315980314667)
          ·
            refine ⟨65892880974213473970472001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43928587316142315980314667 65892880974213473970472001)
            ·
              refine ⟨49419660730660105477854001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65892880974213473970472001 49419660730660105477854001)
              ·
                refine ⟨37064745547995079108390501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49419660730660105477854001 37064745547995079108390501)
                ·
                  refine ⟨6949639790249077332823219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37064745547995079108390501 6949639790249077332823219)
                  ·
                    refine ⟨10424459685373615999234829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949639790249077332823219 10424459685373615999234829)
                    ·
                      refine ⟨3909172382015105999713061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424459685373615999234829 3909172382015105999713061)
                      ·
                        rfl

theorem cell23_7613086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7613086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613086 prefixEnd_7613086 := by exact prefixLift 7613086
  have htrace : WordTrace (prefixWord ++ tailWord_7613086) baseStart_7613086 baseEnd_7613086 := by
    simpa [prefixWord, tailWord_7613086, baseEnd_7613086] using wordTrace_append hprefix tailTrace_7613086
  have hstable : (prefixWord ++ tailWord_7613086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613086).length < 2 ^ (prefixWord ++ tailWord_7613086).sum := by decide
  have hdescent : baseEnd_7613086 < baseStart_7613086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613169 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_7613169 : Nat := 118140960795 + 7613169 * 2 ^ 59
def prefixEnd_7613169 : Nat := 4983230072969 + 3 ^ 40 * 7613169 * 2
def baseEnd_7613169 : Nat := 3909215000909429174975179

theorem tailTrace_7613169 : CollatzResearch.WordTrace tailWord_7613169 prefixEnd_7613169 3909215000909429174975179 := by
  unfold tailWord_7613169
  simp only [CollatzResearch.WordTrace]
  refine ⟨277675085355796413594050561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185116723570530942396033707 277675085355796413594050561)
  ·
    refine ⟨208256314016847310195537921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277675085355796413594050561 208256314016847310195537921)
    ·
      refine ⟨156192235512635482646653441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208256314016847310195537921 156192235512635482646653441)
      ·
        refine ⟨117144176634476611984990081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156192235512635482646653441 117144176634476611984990081)
        ·
          refine ⟨87858132475857458988742561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117144176634476611984990081 87858132475857458988742561)
          ·
            refine ⟨65893599356893094241556921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87858132475857458988742561 65893599356893094241556921)
            ·
              refine ⟨49420199517669820681167691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65893599356893094241556921 49420199517669820681167691)
              ·
                refine ⟨74130299276504731021751537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49420199517669820681167691 74130299276504731021751537)
                ·
                  refine ⟨55597724457378548266313653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74130299276504731021751537 55597724457378548266313653)
                  ·
                    refine ⟨5212286667879238899966905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55597724457378548266313653 5212286667879238899966905)
                    ·
                      refine ⟨3909215000909429174975179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212286667879238899966905 3909215000909429174975179)
                      ·
                        rfl

theorem cell23_7613169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_7613169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613169 prefixEnd_7613169 := by exact prefixLift 7613169
  have htrace : WordTrace (prefixWord ++ tailWord_7613169) baseStart_7613169 baseEnd_7613169 := by
    simpa [prefixWord, tailWord_7613169, baseEnd_7613169] using wordTrace_append hprefix tailTrace_7613169
  have hstable : (prefixWord ++ tailWord_7613169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613169).length < 2 ^ (prefixWord ++ tailWord_7613169).sum := by decide
  have hdescent : baseEnd_7613169 < baseStart_7613169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613199 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_7613199 : Nat := 118140960795 + 7613199 * 2 ^ 59
def prefixEnd_7613199 : Nat := 4983230072969 + 3 ^ 40 * 7613199 * 2
def baseEnd_7613199 : Nat := 3909230405329064057600041

theorem tailTrace_7613199 : CollatzResearch.WordTrace tailWord_7613199 prefixEnd_7613199 3909230405329064057600041 := by
  unfold tailWord_7613199
  simp only [CollatzResearch.WordTrace]
  refine ⟨277676179545687728717642651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185117453030458485811761767 277676179545687728717642651)
  ·
    refine ⟨416514269318531593076463977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277676179545687728717642651 416514269318531593076463977)
    ·
      refine ⟨312385701988898694807347983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416514269318531593076463977 312385701988898694807347983)
      ·
        refine ⟨468578552983348042211021975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312385701988898694807347983 468578552983348042211021975)
        ·
          refine ⟨702867829475022063316532963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468578552983348042211021975 702867829475022063316532963)
          ·
            refine ⟨1054301744212533094974799445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702867829475022063316532963 1054301744212533094974799445)
            ·
              refine ⟨12355098564990622206735931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1054301744212533094974799445 12355098564990622206735931)
              ·
                refine ⟨18532647847485933310103897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355098564990622206735931 18532647847485933310103897)
                ·
                  refine ⟨13899485885614449982577923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18532647847485933310103897 13899485885614449982577923)
                  ·
                    refine ⟨20849228828421674973866885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13899485885614449982577923 20849228828421674973866885)
                    ·
                      refine ⟨3909230405329064057600041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20849228828421674973866885 3909230405329064057600041)
                      ·
                        rfl

theorem cell23_7613199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_7613199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613199 prefixEnd_7613199 := by exact prefixLift 7613199
  have htrace : WordTrace (prefixWord ++ tailWord_7613199) baseStart_7613199 baseEnd_7613199 := by
    simpa [prefixWord, tailWord_7613199, baseEnd_7613199] using wordTrace_append hprefix tailTrace_7613199
  have hstable : (prefixWord ++ tailWord_7613199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613199).length < 2 ^ (prefixWord ++ tailWord_7613199).sum := by decide
  have hdescent : baseEnd_7613199 < baseStart_7613199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613266 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_7613266 : Nat := 118140960795 + 7613266 * 2 ^ 59
def prefixEnd_7613266 : Nat := 4983230072969 + 3 ^ 40 * 7613266 * 2
def baseEnd_7613266 : Nat := 3909264808532915295462233

theorem tailTrace_7613266 : CollatzResearch.WordTrace tailWord_7613266 prefixEnd_7613266 3909264808532915295462233 := by
  unfold tailWord_7613266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69419655809111249790082913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185119082157629999440221101 69419655809111249790082913)
  ·
    refine ⟨52064741856833437342562185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69419655809111249790082913 52064741856833437342562185)
    ·
      refine ⟨39048556392625078006921639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52064741856833437342562185 39048556392625078006921639)
      ·
        refine ⟨58572834588937617010382459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39048556392625078006921639 58572834588937617010382459)
        ·
          refine ⟨87859251883406425515573689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58572834588937617010382459 87859251883406425515573689)
          ·
            refine ⟨65894438912554819136680267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87859251883406425515573689 65894438912554819136680267)
            ·
              refine ⟨98841658368832228705020401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65894438912554819136680267 98841658368832228705020401)
              ·
                refine ⟨74131243776624171528765301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98841658368832228705020401 74131243776624171528765301)
                ·
                  refine ⟨6949804104058516080821747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74131243776624171528765301 6949804104058516080821747)
                  ·
                    refine ⟨10424706156087774121232621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949804104058516080821747 10424706156087774121232621)
                    ·
                      refine ⟨3909264808532915295462233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424706156087774121232621 3909264808532915295462233)
                      ·
                        rfl

theorem cell23_7613266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_7613266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613266 prefixEnd_7613266 := by exact prefixLift 7613266
  have htrace : WordTrace (prefixWord ++ tailWord_7613266) baseStart_7613266 baseEnd_7613266 := by
    simpa [prefixWord, tailWord_7613266, baseEnd_7613266] using wordTrace_append hprefix tailTrace_7613266
  have hstable : (prefixWord ++ tailWord_7613266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613266).length < 2 ^ (prefixWord ++ tailWord_7613266).sum := by decide
  have hdescent : baseEnd_7613266 < baseStart_7613266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613283 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7613283 : Nat := 118140960795 + 7613283 * 2 ^ 59
def prefixEnd_7613283 : Nat := 4983230072969 + 3 ^ 40 * 7613283 * 2
def baseEnd_7613283 : Nat := 3909273537704041728949655

theorem tailTrace_7613283 : CollatzResearch.WordTrace tailWord_7613283 prefixEnd_7613283 3909273537704041728949655 := by
  unfold tailWord_7613283
  simp only [CollatzResearch.WordTrace]
  refine ⟨277679243277383411063700503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185119495518255607375800335 277679243277383411063700503)
  ·
    refine ⟨416518864916075116595550755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277679243277383411063700503 416518864916075116595550755)
    ·
      refine ⟨624778297374112674893326133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416518864916075116595550755 624778297374112674893326133)
      ·
        refine ⟨58572965378823063271249325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624778297374112674893326133 58572965378823063271249325)
        ·
          refine ⟨21964862017058648726718497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58572965378823063271249325 21964862017058648726718497)
          ·
            refine ⟨16473646512793986545038873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21964862017058648726718497 16473646512793986545038873)
            ·
              refine ⟨12355234884595489908779155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16473646512793986545038873 12355234884595489908779155)
              ·
                refine ⟨18532852326893234863168733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355234884595489908779155 18532852326893234863168733)
                ·
                  refine ⟨6949819622584963073688275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18532852326893234863168733 6949819622584963073688275)
                  ·
                    refine ⟨10424729433877444610532413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949819622584963073688275 10424729433877444610532413)
                    ·
                      refine ⟨3909273537704041728949655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424729433877444610532413 3909273537704041728949655)
                      ·
                        rfl

theorem cell23_7613283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7613283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613283 prefixEnd_7613283 := by exact prefixLift 7613283
  have htrace : WordTrace (prefixWord ++ tailWord_7613283) baseStart_7613283 baseEnd_7613283 := by
    simpa [prefixWord, tailWord_7613283, baseEnd_7613283] using wordTrace_append hprefix tailTrace_7613283
  have hstable : (prefixWord ++ tailWord_7613283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613283).length < 2 ^ (prefixWord ++ tailWord_7613283).sum := by decide
  have hdescent : baseEnd_7613283 < baseStart_7613283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613299 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 6]
def baseStart_7613299 : Nat := 118140960795 + 7613299 * 2 ^ 59
def prefixEnd_7613299 : Nat := 4983230072969 + 3 ^ 40 * 7613299 * 2
def baseEnd_7613299 : Nat := 1303093917798171222116527

theorem tailTrace_7613299 : CollatzResearch.WordTrace tailWord_7613299 prefixEnd_7613299 1303093917798171222116527 := by
  unfold tailWord_7613299
  simp only [CollatzResearch.WordTrace]
  refine ⟨277679826845325445796282951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185119884563550297197521967 277679826845325445796282951)
  ·
    refine ⟨416519740267988168694424427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277679826845325445796282951 416519740267988168694424427)
    ·
      refine ⟨624779610401982253041636641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416519740267988168694424427 624779610401982253041636641)
      ·
        refine ⟨468584707801486689781227481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624779610401982253041636641 468584707801486689781227481)
        ·
          refine ⟨351438530851115017335920611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468584707801486689781227481 351438530851115017335920611)
          ·
            refine ⟨527157796276672526003880917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351438530851115017335920611 527157796276672526003880917)
            ·
              refine ⟨12355260850234512328215959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 527157796276672526003880917 12355260850234512328215959)
              ·
                refine ⟨18532891275351768492323939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355260850234512328215959 18532891275351768492323939)
                ·
                  refine ⟨27799336913027652738485909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18532891275351768492323939 27799336913027652738485909)
                  ·
                    refine ⟨1303093917798171222116527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27799336913027652738485909 1303093917798171222116527)
                    ·
                      rfl

theorem cell23_7613299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].length) (baseStart_7613299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613299 prefixEnd_7613299 := by exact prefixLift 7613299
  have htrace : WordTrace (prefixWord ++ tailWord_7613299) baseStart_7613299 baseEnd_7613299 := by
    simpa [prefixWord, tailWord_7613299, baseEnd_7613299] using wordTrace_append hprefix tailTrace_7613299
  have hstable : (prefixWord ++ tailWord_7613299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613299).length < 2 ^ (prefixWord ++ tailWord_7613299).sum := by decide
  have hdescent : baseEnd_7613299 < baseStart_7613299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613334 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7613334 : Nat := 118140960795 + 7613334 * 2 ^ 59
def prefixEnd_7613334 : Nat := 4983230072969 + 3 ^ 40 * 7613334 * 2
def baseEnd_7613334 : Nat := 3909299725217421029411921

theorem tailTrace_7613334 : CollatzResearch.WordTrace tailWord_7613334 prefixEnd_7613334 3909299725217421029411921 := by
  unfold tailWord_7613334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355068962512415423362941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185120735600132431182538037 17355068962512415423362941)
  ·
    refine ⟨6508150860942155783761103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17355068962512415423362941 6508150860942155783761103)
    ·
      refine ⟨9762226291413233675641655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508150860942155783761103 9762226291413233675641655)
      ·
        refine ⟨14643339437119850513462483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762226291413233675641655 14643339437119850513462483)
        ·
          refine ⟨21965009155679775770193725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643339437119850513462483 21965009155679775770193725)
          ·
            refine ⟨8236878433379915913822647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21965009155679775770193725 8236878433379915913822647)
            ·
              refine ⟨12355317650069873870733971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236878433379915913822647 12355317650069873870733971)
              ·
                refine ⟨18532976475104810806100957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355317650069873870733971 18532976475104810806100957)
                ·
                  refine ⟨6949866178164304052287859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18532976475104810806100957 6949866178164304052287859)
                  ·
                    refine ⟨10424799267246456078431789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949866178164304052287859 10424799267246456078431789)
                    ·
                      refine ⟨3909299725217421029411921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424799267246456078431789 3909299725217421029411921)
                      ·
                        rfl

theorem cell23_7613334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7613334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613334 prefixEnd_7613334 := by exact prefixLift 7613334
  have htrace : WordTrace (prefixWord ++ tailWord_7613334) baseStart_7613334 baseEnd_7613334 := by
    simpa [prefixWord, tailWord_7613334, baseEnd_7613334] using wordTrace_append hprefix tailTrace_7613334
  have hstable : (prefixWord ++ tailWord_7613334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613334).length < 2 ^ (prefixWord ++ tailWord_7613334).sum := by decide
  have hdescent : baseEnd_7613334 < baseStart_7613334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613346 : List Nat := [3, 3, 1, 2, 2, 2, 2, 8]
def baseStart_7613346 : Nat := 118140960795 + 7613346 * 2 ^ 59
def prefixEnd_7613346 : Nat := 4983230072969 + 3 ^ 40 * 7613346 * 2
def baseEnd_7613346 : Nat := 144789106925380554905995

theorem tailTrace_7613346 : CollatzResearch.WordTrace tailWord_7613346 prefixEnd_7613346 144789106925380554905995 := by
  unfold tailWord_7613346
  simp only [CollatzResearch.WordTrace]
  refine ⟨69420385269038793205810973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185121027384103448548829261 69420385269038793205810973)
  ·
    refine ⟨26032644475889547452179115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69420385269038793205810973 26032644475889547452179115)
    ·
      refine ⟨39048966713834321178268673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26032644475889547452179115 39048966713834321178268673)
      ·
        refine ⟨29286725035375740883701505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39048966713834321178268673 29286725035375740883701505)
        ·
          refine ⟨21965043776531805662776129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29286725035375740883701505 21965043776531805662776129)
          ·
            refine ⟨16473782832398854247082097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21965043776531805662776129 16473782832398854247082097)
            ·
              refine ⟨12355337124299140685311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16473782832398854247082097 12355337124299140685311573)
              ·
                refine ⟨144789106925380554905995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12355337124299140685311573 144789106925380554905995)
                ·
                  rfl

theorem cell23_7613346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_7613346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613346 prefixEnd_7613346 := by exact prefixLift 7613346
  have htrace : WordTrace (prefixWord ++ tailWord_7613346) baseStart_7613346 baseEnd_7613346 := by
    simpa [prefixWord, tailWord_7613346, baseEnd_7613346] using wordTrace_append hprefix tailTrace_7613346
  have hstable : (prefixWord ++ tailWord_7613346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613346).length < 2 ^ (prefixWord ++ tailWord_7613346).sum := by decide
  have hdescent : baseEnd_7613346 < baseStart_7613346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613357 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7613357 : Nat := 118140960795 + 7613357 * 2 ^ 59
def prefixEnd_7613357 : Nat := 4983230072969 + 3 ^ 40 * 7613357 * 2
def baseEnd_7613357 : Nat := 3909311535272474439424315

theorem tailTrace_7613357 : CollatzResearch.WordTrace tailWord_7613357 prefixEnd_7613357 3909311535272474439424315 := by
  unfold tailWord_7613357
  simp only [CollatzResearch.WordTrace]
  refine ⟨277681942279115321701894325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185121294852743547801262883 277681942279115321701894325)
  ·
    refine ⟨26032682088667061409552593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277681942279115321701894325 26032682088667061409552593)
    ·
      refine ⟨19524511566500296057164445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26032682088667061409552593 19524511566500296057164445)
      ·
        refine ⟨7321691837437611021436667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19524511566500296057164445 7321691837437611021436667)
        ·
          refine ⟨10982537756156416532155001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321691837437611021436667 10982537756156416532155001)
          ·
            refine ⟨8236903317117312399116251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982537756156416532155001 8236903317117312399116251)
            ·
              refine ⟨12355354975675968598674377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236903317117312399116251 12355354975675968598674377)
              ·
                refine ⟨9266516231756976449005783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12355354975675968598674377 9266516231756976449005783)
                ·
                  refine ⟨13899774347635464673508675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266516231756976449005783 13899774347635464673508675)
                  ·
                    refine ⟨20849661521453197010263013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13899774347635464673508675 20849661521453197010263013)
                    ·
                      refine ⟨3909311535272474439424315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20849661521453197010263013 3909311535272474439424315)
                      ·
                        rfl

theorem cell23_7613357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7613357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613357 prefixEnd_7613357 := by exact prefixLift 7613357
  have htrace : WordTrace (prefixWord ++ tailWord_7613357) baseStart_7613357 baseEnd_7613357 := by
    simpa [prefixWord, tailWord_7613357, baseEnd_7613357] using wordTrace_append hprefix tailTrace_7613357
  have hstable : (prefixWord ++ tailWord_7613357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613357).length < 2 ^ (prefixWord ++ tailWord_7613357).sum := by decide
  have hdescent : baseEnd_7613357 < baseStart_7613357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613373 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7613373 : Nat := 118140960795 + 7613373 * 2 ^ 59
def prefixEnd_7613373 : Nat := 4983230072969 + 3 ^ 40 * 7613373 * 2
def baseEnd_7613373 : Nat := 3909319750962946376824241

theorem tailTrace_7613373 : CollatzResearch.WordTrace tailWord_7613373 prefixEnd_7613373 3909319750962946376824241 := by
  unfold tailWord_7613373
  simp only [CollatzResearch.WordTrace]
  refine ⟨277682525847057356434476773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185121683898038237622984515 277682525847057356434476773)
  ·
    refine ⟨52065473596323254331464395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277682525847057356434476773 52065473596323254331464395)
    ·
      refine ⟨78098210394484881497196593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52065473596323254331464395 78098210394484881497196593)
      ·
        refine ⟨58573657795863661122897445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78098210394484881497196593 58573657795863661122897445)
        ·
          refine ⟨10982560836724436460543271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58573657795863661122897445 10982560836724436460543271)
          ·
            refine ⟨16473841255086654690814907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982560836724436460543271 16473841255086654690814907)
            ·
              refine ⟨24710761882629982036222361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16473841255086654690814907 24710761882629982036222361)
              ·
                refine ⟨18533071411972486527166771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24710761882629982036222361 18533071411972486527166771)
                ·
                  refine ⟨27799607117958729790750157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533071411972486527166771 27799607117958729790750157)
                  ·
                    refine ⟨10424852669234523671531309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27799607117958729790750157 10424852669234523671531309)
                    ·
                      refine ⟨3909319750962946376824241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424852669234523671531309 3909319750962946376824241)
                      ·
                        rfl

theorem cell23_7613373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7613373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613373 prefixEnd_7613373 := by exact prefixLift 7613373
  have htrace : WordTrace (prefixWord ++ tailWord_7613373) baseStart_7613373 baseEnd_7613373 := by
    simpa [prefixWord, tailWord_7613373, baseEnd_7613373] using wordTrace_append hprefix tailTrace_7613373
  have hstable : (prefixWord ++ tailWord_7613373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613373).length < 2 ^ (prefixWord ++ tailWord_7613373).sum := by decide
  have hdescent : baseEnd_7613373 < baseStart_7613373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613383 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_7613383 : Nat := 118140960795 + 7613383 * 2 ^ 59
def prefixEnd_7613383 : Nat := 4983230072969 + 3 ^ 40 * 7613383 * 2
def baseEnd_7613383 : Nat := 3909324885769491337699195

theorem tailTrace_7613383 : CollatzResearch.WordTrace tailWord_7613383 prefixEnd_7613383 3909324885769491337699195 := by
  unfold tailWord_7613383
  simp only [CollatzResearch.WordTrace]
  refine ⟨277682890577021128142340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185121927051347418761560535 277682890577021128142340803)
  ·
    refine ⟨416524335865531692213511205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277682890577021128142340803 416524335865531692213511205)
    ·
      refine ⟨78098312974787192290033351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416524335865531692213511205 78098312974787192290033351)
      ·
        refine ⟨117147469462180788435050027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78098312974787192290033351 117147469462180788435050027)
        ·
          refine ⟨175721204193271182652575041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117147469462180788435050027 175721204193271182652575041)
          ·
            refine ⟨131790903144953386989431281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175721204193271182652575041 131790903144953386989431281)
            ·
              refine ⟨98843177358715040242073461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131790903144953386989431281 98843177358715040242073461)
              ·
                refine ⟨9266547877379535022694387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98843177358715040242073461 9266547877379535022694387)
                ·
                  refine ⟨13899821816069302534041581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266547877379535022694387 13899821816069302534041581)
                  ·
                    refine ⟨5212433181025988450265593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13899821816069302534041581 5212433181025988450265593)
                    ·
                      refine ⟨3909324885769491337699195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212433181025988450265593 3909324885769491337699195)
                      ·
                        rfl

theorem cell23_7613383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_7613383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613383 prefixEnd_7613383 := by exact prefixLift 7613383
  have htrace : WordTrace (prefixWord ++ tailWord_7613383) baseStart_7613383 baseEnd_7613383 := by
    simpa [prefixWord, tailWord_7613383, baseEnd_7613383] using wordTrace_append hprefix tailTrace_7613383
  have hstable : (prefixWord ++ tailWord_7613383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613383).length < 2 ^ (prefixWord ++ tailWord_7613383).sum := by decide
  have hdescent : baseEnd_7613383 < baseStart_7613383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613390 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_7613390 : Nat := 118140960795 + 7613390 * 2 ^ 59
def prefixEnd_7613390 : Nat := 4983230072969 + 3 ^ 40 * 7613390 * 2
def baseEnd_7613390 : Nat := 3909328480134072810311663

theorem tailTrace_7613390 : CollatzResearch.WordTrace tailWord_7613390 prefixEnd_7613390 3909328480134072810311663 := by
  unfold tailWord_7613390
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710393235999471042230703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185122097258663845558563749 34710393235999471042230703)
  ·
    refine ⟨52065589853999206563346055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34710393235999471042230703 52065589853999206563346055)
    ·
      refine ⟨78098384780998809845019083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52065589853999206563346055 78098384780998809845019083)
      ·
        refine ⟨117147577171498214767528625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78098384780998809845019083 117147577171498214767528625)
        ·
          refine ⟨87860682878623661075646469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117147577171498214767528625 87860682878623661075646469)
          ·
            refine ⟨16473878039741936451683713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87860682878623661075646469 16473878039741936451683713)
            ·
              refine ⟨12355408529806452338762785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16473878039741936451683713 12355408529806452338762785)
              ·
                refine ⟨9266556397354839254072089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12355408529806452338762785 9266556397354839254072089)
                ·
                  refine ⟨6949917298016129440554067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9266556397354839254072089 6949917298016129440554067)
                  ·
                    refine ⟨10424875947024194160831101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949917298016129440554067 10424875947024194160831101)
                    ·
                      refine ⟨3909328480134072810311663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424875947024194160831101 3909328480134072810311663)
                      ·
                        rfl

theorem cell23_7613390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_7613390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613390 prefixEnd_7613390 := by exact prefixLift 7613390
  have htrace : WordTrace (prefixWord ++ tailWord_7613390) baseStart_7613390 baseEnd_7613390 := by
    simpa [prefixWord, tailWord_7613390, baseEnd_7613390] using wordTrace_append hprefix tailTrace_7613390
  have hstable : (prefixWord ++ tailWord_7613390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613390).length < 2 ^ (prefixWord ++ tailWord_7613390).sum := by decide
  have hdescent : baseEnd_7613390 < baseStart_7613390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613396 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7613396 : Nat := 118140960795 + 7613396 * 2 ^ 59
def prefixEnd_7613396 : Nat := 4983230072969 + 3 ^ 40 * 7613396 * 2
def baseEnd_7613396 : Nat := 3909331561017999786836635

theorem tailTrace_7613396 : CollatzResearch.WordTrace tailWord_7613396 prefixEnd_7613396 3909331561017999786836635 := by
  unfold tailWord_7613396
  simp only [CollatzResearch.WordTrace]
  refine ⟨138841682362987015681282021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185122243150649354241709361 138841682362987015681282021)
  ·
    refine ⟨26032815443060065440240379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138841682362987015681282021 26032815443060065440240379)
    ·
      refine ⟨39049223164590098160360569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26032815443060065440240379 39049223164590098160360569)
      ·
        refine ⟨29286917373442573620270427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39049223164590098160360569 29286917373442573620270427)
        ·
          refine ⟨43930376060163860430405641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29286917373442573620270427 43930376060163860430405641)
          ·
            refine ⟨32947782045122895322804231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43930376060163860430405641 32947782045122895322804231)
            ·
              refine ⟨49421673067684342984206347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32947782045122895322804231 49421673067684342984206347)
              ·
                refine ⟨74132509601526514476309521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49421673067684342984206347 74132509601526514476309521)
                ·
                  refine ⟨55599382201144885857232141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74132509601526514476309521 55599382201144885857232141)
                  ·
                    refine ⟨20849768325429332196462053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55599382201144885857232141 20849768325429332196462053)
                    ·
                      refine ⟨3909331561017999786836635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20849768325429332196462053 3909331561017999786836635)
                      ·
                        rfl

theorem cell23_7613396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7613396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613396 prefixEnd_7613396 := by exact prefixLift 7613396
  have htrace : WordTrace (prefixWord ++ tailWord_7613396) baseStart_7613396 baseEnd_7613396 := by
    simpa [prefixWord, tailWord_7613396, baseEnd_7613396] using wordTrace_append hprefix tailTrace_7613396
  have hstable : (prefixWord ++ tailWord_7613396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613396).length < 2 ^ (prefixWord ++ tailWord_7613396).sum := by decide
  have hdescent : baseEnd_7613396 < baseStart_7613396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613399 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_7613399 : Nat := 118140960795 + 7613399 * 2 ^ 59
def prefixEnd_7613399 : Nat := 4983230072969 + 3 ^ 40 * 7613399 * 2
def baseEnd_7613399 : Nat := 3909333101459963275099121

theorem tailTrace_7613399 : CollatzResearch.WordTrace tailWord_7613399 prefixEnd_7613399 3909333101459963275099121 := by
  unfold tailWord_7613399
  simp only [CollatzResearch.WordTrace]
  refine ⟨277683474144963162874923251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185122316096642108583282167 277683474144963162874923251)
  ·
    refine ⟨416525211217444744312384877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277683474144963162874923251 416525211217444744312384877)
    ·
      refine ⟨156196954206541779117144329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416525211217444744312384877 156196954206541779117144329)
      ·
        refine ⟨117147715654906334337858247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156196954206541779117144329 117147715654906334337858247)
        ·
          refine ⟨175721573482359501506787371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117147715654906334337858247 175721573482359501506787371)
          ·
            refine ⟨263582360223539252260181057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175721573482359501506787371 263582360223539252260181057)
            ·
              refine ⟨197686770167654439195135793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263582360223539252260181057 197686770167654439195135793)
              ·
                refine ⟨148265077625740829396351845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197686770167654439195135793 148265077625740829396351845)
                ·
                  refine ⟨27799702054826405511815971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148265077625740829396351845 27799702054826405511815971)
                  ·
                    refine ⟨41699553082239608267723957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27799702054826405511815971 41699553082239608267723957)
                    ·
                      refine ⟨3909333101459963275099121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41699553082239608267723957 3909333101459963275099121)
                      ·
                        rfl

theorem cell23_7613399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_7613399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613399 prefixEnd_7613399 := by exact prefixLift 7613399
  have htrace : WordTrace (prefixWord ++ tailWord_7613399) baseStart_7613399 baseEnd_7613399 := by
    simpa [prefixWord, tailWord_7613399, baseEnd_7613399] using wordTrace_append hprefix tailTrace_7613399
  have hstable : (prefixWord ++ tailWord_7613399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613399).length < 2 ^ (prefixWord ++ tailWord_7613399).sum := by decide
  have hdescent : baseEnd_7613399 < baseStart_7613399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613428 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7613428 : Nat := 118140960795 + 7613428 * 2 ^ 59
def prefixEnd_7613428 : Nat := 4983230072969 + 3 ^ 40 * 7613428 * 2
def baseEnd_7613428 : Nat := 3909347992398943661636489

theorem tailTrace_7613428 : CollatzResearch.WordTrace tailWord_7613428 prefixEnd_7613428 3909347992398943661636489 := by
  unfold tailWord_7613428
  simp only [CollatzResearch.WordTrace]
  refine ⟨138842265930929050413864469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185123021241238733885152625 138842265930929050413864469)
  ·
    refine ⟨6508231215512299238149897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138842265930929050413864469 6508231215512299238149897)
    ·
      refine ⟨4881173411634224428612423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6508231215512299238149897 4881173411634224428612423)
      ·
        refine ⟨7321760117451336642918635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881173411634224428612423 7321760117451336642918635)
        ·
          refine ⟨10982640176177004964377953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321760117451336642918635 10982640176177004964377953)
          ·
            refine ⟨8236980132132753723283465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982640176177004964377953 8236980132132753723283465)
            ·
              refine ⟨6177735099099565292462599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236980132132753723283465 6177735099099565292462599)
              ·
                refine ⟨9266602648649347938693899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177735099099565292462599 9266602648649347938693899)
                ·
                  refine ⟨13899903972974021908040849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266602648649347938693899 13899903972974021908040849)
                  ·
                    refine ⟨10424927979730516431030637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13899903972974021908040849 10424927979730516431030637)
                    ·
                      refine ⟨3909347992398943661636489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424927979730516431030637 3909347992398943661636489)
                      ·
                        rfl

theorem cell23_7613428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7613428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613428 prefixEnd_7613428 := by exact prefixLift 7613428
  have htrace : WordTrace (prefixWord ++ tailWord_7613428) baseStart_7613428 baseEnd_7613428 := by
    simpa [prefixWord, tailWord_7613428, baseEnd_7613428] using wordTrace_append hprefix tailTrace_7613428
  have hstable : (prefixWord ++ tailWord_7613428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613428).length < 2 ^ (prefixWord ++ tailWord_7613428).sum := by decide
  have hdescent : baseEnd_7613428 < baseStart_7613428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613430 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7613430 : Nat := 118140960795 + 7613430 * 2 ^ 59
def prefixEnd_7613430 : Nat := 4983230072969 + 3 ^ 40 * 7613430 * 2
def baseEnd_7613430 : Nat := 3909349019360252653811479

theorem tailTrace_7613430 : CollatzResearch.WordTrace tailWord_7613430 prefixEnd_7613430 3909349019360252653811479 := by
  unfold tailWord_7613430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355287800490678448081359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185123069871900570112867829 17355287800490678448081359)
  ·
    refine ⟨26032931700736017672122039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17355287800490678448081359 26032931700736017672122039)
    ·
      refine ⟨39049397551104026508183059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26032931700736017672122039 39049397551104026508183059)
      ·
        refine ⟨58574096326656039762274589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39049397551104026508183059 58574096326656039762274589)
        ·
          refine ⟨21965286122496014910852971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58574096326656039762274589 21965286122496014910852971)
          ·
            refine ⟨32947929183744022366279457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965286122496014910852971 32947929183744022366279457)
            ·
              refine ⟨24710946887808016774709593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32947929183744022366279457 24710946887808016774709593)
              ·
                refine ⟨18533210165856012581032195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24710946887808016774709593 18533210165856012581032195)
                ·
                  refine ⟨27799815248784018871548293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533210165856012581032195 27799815248784018871548293)
                  ·
                    refine ⟨5212465359147003538415305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27799815248784018871548293 5212465359147003538415305)
                    ·
                      refine ⟨3909349019360252653811479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212465359147003538415305 3909349019360252653811479)
                      ·
                        rfl

theorem cell23_7613430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7613430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613430 prefixEnd_7613430 := by exact prefixLift 7613430
  have htrace : WordTrace (prefixWord ++ tailWord_7613430) baseStart_7613430 baseEnd_7613430 := by
    simpa [prefixWord, tailWord_7613430, baseEnd_7613430] using wordTrace_append hprefix tailTrace_7613430
  have hstable : (prefixWord ++ tailWord_7613430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613430).length < 2 ^ (prefixWord ++ tailWord_7613430).sum := by decide
  have hdescent : baseEnd_7613430 < baseStart_7613430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613459 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_7613459 : Nat := 118140960795 + 7613459 * 2 ^ 59
def prefixEnd_7613459 : Nat := 4983230072969 + 3 ^ 40 * 7613459 * 2
def baseEnd_7613459 : Nat := 3909363910299233040348845

theorem tailTrace_7613459 : CollatzResearch.WordTrace tailWord_7613459 prefixEnd_7613459 3909363910299233040348845 := by
  unfold tailWord_7613459
  simp only [CollatzResearch.WordTrace]
  refine ⟨277685662524745793122107431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185123775016497195414738287 277685662524745793122107431)
  ·
    refine ⟨416528493787118689683161147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277685662524745793122107431 416528493787118689683161147)
    ·
      refine ⟨624792740680678034524741721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416528493787118689683161147 624792740680678034524741721)
      ·
        refine ⟨468594555510508525893556291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624792740680678034524741721 468594555510508525893556291)
        ·
          refine ⟨702891833265762788840334437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468594555510508525893556291 702891833265762788840334437)
          ·
            refine ⟨131792218737330522907562707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 702891833265762788840334437 131792218737330522907562707)
            ·
              refine ⟨197688328105995784361344061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131792218737330522907562707 197688328105995784361344061)
              ·
                refine ⟨74133123039748419135504023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197688328105995784361344061 74133123039748419135504023)
                ·
                  refine ⟨111199684559622628703256035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74133123039748419135504023 111199684559622628703256035)
                  ·
                    refine ⟨166799526839433943054884053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111199684559622628703256035 166799526839433943054884053)
                    ·
                      refine ⟨3909363910299233040348845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166799526839433943054884053 3909363910299233040348845)
                      ·
                        rfl

theorem cell23_7613459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_7613459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613459 prefixEnd_7613459 := by exact prefixLift 7613459
  have htrace : WordTrace (prefixWord ++ tailWord_7613459) baseStart_7613459 baseEnd_7613459 := by
    simpa [prefixWord, tailWord_7613459, baseEnd_7613459] using wordTrace_append hprefix tailTrace_7613459
  have hstable : (prefixWord ++ tailWord_7613459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613459).length < 2 ^ (prefixWord ++ tailWord_7613459).sum := by decide
  have hdescent : baseEnd_7613459 < baseStart_7613459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613463 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7613463 : Nat := 118140960795 + 7613463 * 2 ^ 59
def prefixEnd_7613463 : Nat := 4983230072969 + 3 ^ 40 * 7613463 * 2
def baseEnd_7613463 : Nat := 3909365964221851024698827

theorem tailTrace_7613463 : CollatzResearch.WordTrace tailWord_7613463 prefixEnd_7613463 3909365964221851024698827 := by
  unfold tailWord_7613463
  simp only [CollatzResearch.WordTrace]
  refine ⟨277685808416731301805253043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185123872277820867870168695 277685808416731301805253043)
  ·
    refine ⟨416528712625096952707879565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277685808416731301805253043 416528712625096952707879565)
    ·
      refine ⟨156198267234411357265454837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416528712625096952707879565 156198267234411357265454837)
      ·
        refine ⟨14643587553226064743636391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156198267234411357265454837 14643587553226064743636391)
        ·
          refine ⟨21965381329839097115454587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643587553226064743636391 21965381329839097115454587)
          ·
            refine ⟨32948071994758645673181881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965381329839097115454587 32948071994758645673181881)
            ·
              refine ⟨24711053996068984254886411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32948071994758645673181881 24711053996068984254886411)
              ·
                refine ⟨37066580994103476382329617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24711053996068984254886411 37066580994103476382329617)
                ·
                  refine ⟨27799935745577607286747213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37066580994103476382329617 27799935745577607286747213)
                  ·
                    refine ⟨10424975904591602732530205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27799935745577607286747213 10424975904591602732530205)
                    ·
                      refine ⟨3909365964221851024698827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10424975904591602732530205 3909365964221851024698827)
                      ·
                        rfl

theorem cell23_7613463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7613463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613463 prefixEnd_7613463 := by exact prefixLift 7613463
  have htrace : WordTrace (prefixWord ++ tailWord_7613463) baseStart_7613463 baseEnd_7613463 := by
    simpa [prefixWord, tailWord_7613463, baseEnd_7613463] using wordTrace_append hprefix tailTrace_7613463
  have hstable : (prefixWord ++ tailWord_7613463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613463).length < 2 ^ (prefixWord ++ tailWord_7613463).sum := by decide
  have hdescent : baseEnd_7613463 < baseStart_7613463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613510 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7613510 : Nat := 118140960795 + 7613510 * 2 ^ 59
def prefixEnd_7613510 : Nat := 4983230072969 + 3 ^ 40 * 7613510 * 2
def baseEnd_7613510 : Nat := 3909390097812612340811111

theorem tailTrace_7613510 : CollatzResearch.WordTrace tailWord_7613510 prefixEnd_7613510 3909390097812612340811111 := by
  unfold tailWord_7613510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677735082736282151006687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185125015098374019221475989 8677735082736282151006687)
  ·
    refine ⟨13016602624104423226510031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677735082736282151006687 13016602624104423226510031)
    ·
      refine ⟨19524903936156634839765047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016602624104423226510031 19524903936156634839765047)
      ·
        refine ⟨29287355904234952259647571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524903936156634839765047 29287355904234952259647571)
        ·
          refine ⟨43931033856352428389471357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29287355904234952259647571 43931033856352428389471357)
          ·
            refine ⟨16474137696132160646051759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43931033856352428389471357 16474137696132160646051759)
            ·
              refine ⟨24711206544198240969077639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474137696132160646051759 24711206544198240969077639)
              ·
                refine ⟨37066809816297361453616459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24711206544198240969077639 37066809816297361453616459)
                ·
                  refine ⟨55600214724446042180424689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37066809816297361453616459 55600214724446042180424689)
                  ·
                    refine ⟨41700161043334531635318517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55600214724446042180424689 41700161043334531635318517)
                    ·
                      refine ⟨3909390097812612340811111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41700161043334531635318517 3909390097812612340811111)
                      ·
                        rfl

theorem cell23_7613510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7613510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613510 prefixEnd_7613510 := by exact prefixLift 7613510
  have htrace : WordTrace (prefixWord ++ tailWord_7613510) baseStart_7613510 baseEnd_7613510 := by
    simpa [prefixWord, tailWord_7613510, baseEnd_7613510] using wordTrace_append hprefix tailTrace_7613510
  have hstable : (prefixWord ++ tailWord_7613510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613510).length < 2 ^ (prefixWord ++ tailWord_7613510).sum := by decide
  have hdescent : baseEnd_7613510 < baseStart_7613510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613553 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_7613553 : Nat := 118140960795 + 7613553 * 2 ^ 59
def prefixEnd_7613553 : Nat := 4983230072969 + 3 ^ 40 * 7613553 * 2
def baseEnd_7613553 : Nat := 3909412177480755672573413

theorem tailTrace_7613553 : CollatzResearch.WordTrace tailWord_7613553 prefixEnd_7613553 3909412177480755672573413 := by
  unfold tailWord_7613553
  simp only [CollatzResearch.WordTrace]
  refine ⟨277689090986405247176029313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185126060657603498117352875 277689090986405247176029313)
  ·
    refine ⟨208266818239803935382021985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277689090986405247176029313 208266818239803935382021985)
    ·
      refine ⟨156200113679852951536516489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208266818239803935382021985 156200113679852951536516489)
      ·
        refine ⟨117150085259889713652387367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156200113679852951536516489 117150085259889713652387367)
        ·
          refine ⟨175725127889834570478581051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117150085259889713652387367 175725127889834570478581051)
          ·
            refine ⟨263587691834751855717871577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175725127889834570478581051 263587691834751855717871577)
            ·
              refine ⟨197690768876063891788403683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263587691834751855717871577 197690768876063891788403683)
              ·
                refine ⟨296536153314095837682605525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197690768876063891788403683 296536153314095837682605525)
                ·
                  refine ⟨6950066093299121195686067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 296536153314095837682605525 6950066093299121195686067)
                  ·
                    refine ⟨10425099139948681793529101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950066093299121195686067 10425099139948681793529101)
                    ·
                      refine ⟨3909412177480755672573413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425099139948681793529101 3909412177480755672573413)
                      ·
                        rfl

theorem cell23_7613553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_7613553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613553 prefixEnd_7613553 := by exact prefixLift 7613553
  have htrace : WordTrace (prefixWord ++ tailWord_7613553) baseStart_7613553 baseEnd_7613553 := by
    simpa [prefixWord, tailWord_7613553, baseEnd_7613553] using wordTrace_append hprefix tailTrace_7613553
  have hstable : (prefixWord ++ tailWord_7613553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613553).length < 2 ^ (prefixWord ++ tailWord_7613553).sum := by decide
  have hdescent : baseEnd_7613553 < baseStart_7613553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613604 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_7613604 : Nat := 118140960795 + 7613604 * 2 ^ 59
def prefixEnd_7613604 : Nat := 4983230072969 + 3 ^ 40 * 7613604 * 2
def baseEnd_7613604 : Nat := 3909438364994134973035679

theorem tailTrace_7613604 : CollatzResearch.WordTrace tailWord_7613604 prefixEnd_7613604 3909438364994134973035679 := by
  unfold tailWord_7613604
  simp only [CollatzResearch.WordTrace]
  refine ⟨138845475554610241443067933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185127300739480321924090577 138845475554610241443067933)
  ·
    refine ⟨52067053332978840541150475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138845475554610241443067933 52067053332978840541150475)
    ·
      refine ⟨78100579999468260811725713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52067053332978840541150475 78100579999468260811725713)
      ·
        refine ⟨58575434999601195608794285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78100579999468260811725713 58575434999601195608794285)
        ·
          refine ⟨21965788124850448353297857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58575434999601195608794285 21965788124850448353297857)
          ·
            refine ⟨16474341093637836264973393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21965788124850448353297857 16474341093637836264973393)
            ·
              refine ⟨12355755820228377198730045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16474341093637836264973393 12355755820228377198730045)
              ·
                refine ⟨4633408432585641449523767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12355755820228377198730045 4633408432585641449523767)
                ·
                  refine ⟨6950112648878462174285651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633408432585641449523767 6950112648878462174285651)
                  ·
                    refine ⟨10425168973317693261428477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950112648878462174285651 10425168973317693261428477)
                    ·
                      refine ⟨3909438364994134973035679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425168973317693261428477 3909438364994134973035679)
                      ·
                        rfl

theorem cell23_7613604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_7613604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613604 prefixEnd_7613604 := by exact prefixLift 7613604
  have htrace : WordTrace (prefixWord ++ tailWord_7613604) baseStart_7613604 baseEnd_7613604 := by
    simpa [prefixWord, tailWord_7613604, baseEnd_7613604] using wordTrace_append hprefix tailTrace_7613604
  have hstable : (prefixWord ++ tailWord_7613604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613604).length < 2 ^ (prefixWord ++ tailWord_7613604).sum := by decide
  have hdescent : baseEnd_7613604 < baseStart_7613604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613607 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7613607 : Nat := 118140960795 + 7613607 * 2 ^ 59
def prefixEnd_7613607 : Nat := 4983230072969 + 3 ^ 40 * 7613607 * 2
def baseEnd_7613607 : Nat := 1303146635145366153766055

theorem tailTrace_7613607 : CollatzResearch.WordTrace tailWord_7613607 prefixEnd_7613607 1303146635145366153766055 := by
  unfold tailWord_7613607
  simp only [CollatzResearch.WordTrace]
  refine ⟨277691060528209614398495075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185127373685473076265663383 277691060528209614398495075)
  ·
    refine ⟨416536590792314421597742613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277691060528209614398495075 416536590792314421597742613)
    ·
      refine ⟨19525152693389738512394185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 416536590792314421597742613 19525152693389738512394185)
      ·
        refine ⟨14643864520042303884295639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19525152693389738512394185 14643864520042303884295639)
        ·
          refine ⟨21965796780063455826443459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643864520042303884295639 21965796780063455826443459)
          ·
            refine ⟨32948695170095183739665189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965796780063455826443459 32948695170095183739665189)
            ·
              refine ⟨6177880344392846951187223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32948695170095183739665189 6177880344392846951187223)
              ·
                refine ⟨9266820516589270426780835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177880344392846951187223 9266820516589270426780835)
                ·
                  refine ⟨13900230774883905640171253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266820516589270426780835 13900230774883905640171253)
                  ·
                    refine ⟨1303146635145366153766055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13900230774883905640171253 1303146635145366153766055)
                    ·
                      rfl

theorem cell23_7613607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7613607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613607 prefixEnd_7613607 := by exact prefixLift 7613607
  have htrace : WordTrace (prefixWord ++ tailWord_7613607) baseStart_7613607 baseEnd_7613607 := by
    simpa [prefixWord, tailWord_7613607, baseEnd_7613607] using wordTrace_append hprefix tailTrace_7613607
  have hstable : (prefixWord ++ tailWord_7613607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613607).length < 2 ^ (prefixWord ++ tailWord_7613607).sum := by decide
  have hdescent : baseEnd_7613607 < baseStart_7613607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613626 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_7613626 : Nat := 118140960795 + 7613626 * 2 ^ 59
def prefixEnd_7613626 : Nat := 4983230072969 + 3 ^ 40 * 7613626 * 2
def baseEnd_7613626 : Nat := 3909449661568533886960577

theorem tailTrace_7613626 : CollatzResearch.WordTrace tailWord_7613626 prefixEnd_7613626 3909449661568533886960577 := by
  unfold tailWord_7613626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69422938378785195160859183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185127835676760520428957821 69422938378785195160859183)
  ·
    refine ⟨104134407568177792741288775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69422938378785195160859183 104134407568177792741288775)
    ·
      refine ⟨156201611352266689111933163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104134407568177792741288775 156201611352266689111933163)
      ·
        refine ⟨234302417028400033667899745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156201611352266689111933163 234302417028400033667899745)
        ·
          refine ⟨175726812771300025250924809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234302417028400033667899745 175726812771300025250924809)
          ·
            refine ⟨131795109578475018938193607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175726812771300025250924809 131795109578475018938193607)
            ·
              refine ⟨197692664367712528407290411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131795109578475018938193607 197692664367712528407290411)
              ·
                refine ⟨296538996551568792610935617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197692664367712528407290411 296538996551568792610935617)
                ·
                  refine ⟨222404247413676594458201713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296538996551568792610935617 222404247413676594458201713)
                  ·
                    refine ⟨166803185560257445843651285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222404247413676594458201713 166803185560257445843651285)
                    ·
                      refine ⟨3909449661568533886960577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166803185560257445843651285 3909449661568533886960577)
                      ·
                        rfl

theorem cell23_7613626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_7613626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613626 prefixEnd_7613626 := by exact prefixLift 7613626
  have htrace : WordTrace (prefixWord ++ tailWord_7613626) baseStart_7613626 baseEnd_7613626 := by
    simpa [prefixWord, tailWord_7613626, baseEnd_7613626] using wordTrace_append hprefix tailTrace_7613626
  have hstable : (prefixWord ++ tailWord_7613626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613626).length < 2 ^ (prefixWord ++ tailWord_7613626).sum := by decide
  have hdescent : baseEnd_7613626 < baseStart_7613626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613630 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7613630 : Nat := 118140960795 + 7613630 * 2 ^ 59
def prefixEnd_7613630 : Nat := 4983230072969 + 3 ^ 40 * 7613630 * 2
def baseEnd_7613630 : Nat := 3909451715491151871310559

theorem tailTrace_7613630 : CollatzResearch.WordTrace tailWord_7613630 prefixEnd_7613630 3909451715491151871310559 := by
  unfold tailWord_7613630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711487425890786165822793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185127932938084192884388229 34711487425890786165822793)
  ·
    refine ⟨26033615569418089624367095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34711487425890786165822793 26033615569418089624367095)
    ·
      refine ⟨39050423354127134436550643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26033615569418089624367095 39050423354127134436550643)
      ·
        refine ⟨58575635031190701654825965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39050423354127134436550643 58575635031190701654825965)
        ·
          refine ⟨21965863136696513120559737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58575635031190701654825965 21965863136696513120559737)
          ·
            refine ⟨16474397352522384840419803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21965863136696513120559737 16474397352522384840419803)
            ·
              refine ⟨24711596028783577260629705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474397352522384840419803 24711596028783577260629705)
              ·
                refine ⟨18533697021587682945472279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24711596028783577260629705 18533697021587682945472279)
                ·
                  refine ⟨27800545532381524418208419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533697021587682945472279 27800545532381524418208419)
                  ·
                    refine ⟨41700818298572286627312629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27800545532381524418208419 41700818298572286627312629)
                    ·
                      refine ⟨3909451715491151871310559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41700818298572286627312629 3909451715491151871310559)
                      ·
                        rfl

theorem cell23_7613630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7613630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613630 prefixEnd_7613630 := by exact prefixLift 7613630
  have htrace : WordTrace (prefixWord ++ tailWord_7613630) baseStart_7613630 baseEnd_7613630 := by
    simpa [prefixWord, tailWord_7613630, baseEnd_7613630] using wordTrace_append hprefix tailTrace_7613630
  have hstable : (prefixWord ++ tailWord_7613630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613630).length < 2 ^ (prefixWord ++ tailWord_7613630).sum := by decide
  have hdescent : baseEnd_7613630 < baseStart_7613630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613643 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3]
def baseStart_7613643 : Nat := 118140960795 + 7613643 * 2 ^ 59
def prefixEnd_7613643 : Nat := 4983230072969 + 3 ^ 40 * 7613643 * 2
def baseEnd_7613643 : Nat := 3909458390739660320447999

theorem tailTrace_7613643 : CollatzResearch.WordTrace tailWord_7613643 prefixEnd_7613643 3909458390739660320447999 := by
  unfold tailWord_7613643
  simp only [CollatzResearch.WordTrace]
  refine ⟨277692373556079192546805583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185128249037386128364537055 277692373556079192546805583)
  ·
    refine ⟨416538560334118788820208375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277692373556079192546805583 416538560334118788820208375)
    ·
      refine ⟨624807840501178183230312563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416538560334118788820208375 624807840501178183230312563)
      ·
        refine ⟨937211760751767274845468845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624807840501178183230312563 937211760751767274845468845)
        ·
          refine ⟨351454410281912728067050817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937211760751767274845468845 351454410281912728067050817)
          ·
            refine ⟨263590807711434546050288113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351454410281912728067050817 263590807711434546050288113)
            ·
              refine ⟨197693105783575909537716085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263590807711434546050288113 197693105783575909537716085)
              ·
                refine ⟨18533728667210241519160883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197693105783575909537716085 18533728667210241519160883)
                ·
                  refine ⟨27800593000815362278741325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533728667210241519160883 27800593000815362278741325)
                  ·
                    refine ⟨10425222375305760854527997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27800593000815362278741325 10425222375305760854527997)
                    ·
                      refine ⟨3909458390739660320447999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425222375305760854527997 3909458390739660320447999)
                      ·
                        rfl

theorem cell23_7613643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].length) (baseStart_7613643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613643 prefixEnd_7613643 := by exact prefixLift 7613643
  have htrace : WordTrace (prefixWord ++ tailWord_7613643) baseStart_7613643 baseEnd_7613643 := by
    simpa [prefixWord, tailWord_7613643, baseEnd_7613643] using wordTrace_append hprefix tailTrace_7613643
  have hstable : (prefixWord ++ tailWord_7613643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613643).length < 2 ^ (prefixWord ++ tailWord_7613643).sum := by decide
  have hdescent : baseEnd_7613643 < baseStart_7613643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613677 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7613677 : Nat := 118140960795 + 7613677 * 2 ^ 59
def prefixEnd_7613677 : Nat := 4983230072969 + 3 ^ 40 * 7613677 * 2
def baseEnd_7613677 : Nat := 3909475849081913187422843

theorem tailTrace_7613677 : CollatzResearch.WordTrace tailWord_7613677 prefixEnd_7613677 3909475849081913187422843 := by
  unfold tailWord_7613677
  simp only [CollatzResearch.WordTrace]
  refine ⟨277693613637956016353543285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185129075758637344235695523 277693613637956016353543285)
  ·
    refine ⟨26033776278558376533144683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277693613637956016353543285 26033776278558376533144683)
    ·
      refine ⟨39050664417837564799717025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26033776278558376533144683 39050664417837564799717025)
      ·
        refine ⟨29287998313378173599787769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39050664417837564799717025 29287998313378173599787769)
        ·
          refine ⟨21965998735033630199840827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29287998313378173599787769 21965998735033630199840827)
          ·
            refine ⟨32948998102550445299761241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965998735033630199840827 32948998102550445299761241)
            ·
              refine ⟨24711748576912833974820931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32948998102550445299761241 24711748576912833974820931)
              ·
                refine ⟨37067622865369250962231397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24711748576912833974820931 37067622865369250962231397)
                ·
                  refine ⟨6950179287256734555418387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37067622865369250962231397 6950179287256734555418387)
                  ·
                    refine ⟨10425268930885101833127581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950179287256734555418387 10425268930885101833127581)
                    ·
                      refine ⟨3909475849081913187422843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425268930885101833127581 3909475849081913187422843)
                      ·
                        rfl

theorem cell23_7613677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7613677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613677 prefixEnd_7613677 := by exact prefixLift 7613677
  have htrace : WordTrace (prefixWord ++ tailWord_7613677) baseStart_7613677 baseEnd_7613677 := by
    simpa [prefixWord, tailWord_7613677, baseEnd_7613677] using wordTrace_append hprefix tailTrace_7613677
  have hstable : (prefixWord ++ tailWord_7613677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613677).length < 2 ^ (prefixWord ++ tailWord_7613677).sum := by decide
  have hdescent : baseEnd_7613677 < baseStart_7613677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613684 : List Nat := [2, 6, 1, 2, 1, 1, 2, 8]
def baseStart_7613684 : Nat := 118140960795 + 7613684 * 2 ^ 59
def prefixEnd_7613684 : Nat := 4983230072969 + 3 ^ 40 * 7613684 * 2
def baseEnd_7613684 : Nat := 144795534942462765186493

theorem tailTrace_7613684 : CollatzResearch.WordTrace tailWord_7613684 prefixEnd_7613684 144795534942462765186493 := by
  unfold tailWord_7613684
  simp only [CollatzResearch.WordTrace]
  refine ⟨138846934474465328274524053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185129245965953771032698737 138846934474465328274524053)
  ·
    refine ⟨6508450053490562262868315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138846934474465328274524053 6508450053490562262868315)
    ·
      refine ⟨9762675080235843394302473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508450053490562262868315 9762675080235843394302473)
      ·
        refine ⟨7322006310176882545726855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762675080235843394302473 7322006310176882545726855)
        ·
          refine ⟨10983009465265323818590283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322006310176882545726855 10983009465265323818590283)
          ·
            refine ⟨16474514197897985727885425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983009465265323818590283 16474514197897985727885425)
            ·
              refine ⟨12355885648423489295914069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16474514197897985727885425 12355885648423489295914069)
              ·
                refine ⟨144795534942462765186493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12355885648423489295914069 144795534942462765186493)
                ·
                  rfl

theorem cell23_7613684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 8].length) (baseStart_7613684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613684 prefixEnd_7613684 := by exact prefixLift 7613684
  have htrace : WordTrace (prefixWord ++ tailWord_7613684) baseStart_7613684 baseEnd_7613684 := by
    simpa [prefixWord, tailWord_7613684, baseEnd_7613684] using wordTrace_append hprefix tailTrace_7613684
  have hstable : (prefixWord ++ tailWord_7613684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613684).length < 2 ^ (prefixWord ++ tailWord_7613684).sum := by decide
  have hdescent : baseEnd_7613684 < baseStart_7613684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613694 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7613694 : Nat := 118140960795 + 7613694 * 2 ^ 59
def prefixEnd_7613694 : Nat := 4983230072969 + 3 ^ 40 * 7613694 * 2
def baseEnd_7613694 : Nat := 3909484578253039620910265

theorem tailTrace_7613694 : CollatzResearch.WordTrace tailWord_7613694 prefixEnd_7613694 3909484578253039620910265 := by
  unfold tailWord_7613694
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711779209861803532114017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185129489119262952171274757 34711779209861803532114017)
  ·
    refine ⟨26033834407396352649085513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34711779209861803532114017 26033834407396352649085513)
    ·
      refine ⟨19525375805547264486814135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26033834407396352649085513 19525375805547264486814135)
      ·
        refine ⟨29288063708320896730221203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525375805547264486814135 29288063708320896730221203)
        ·
          refine ⟨43932095562481345095331805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29288063708320896730221203 43932095562481345095331805)
          ·
            refine ⟨16474535835930504410749427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43932095562481345095331805 16474535835930504410749427)
            ·
              refine ⟨24711803753895756616124141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474535835930504410749427 24711803753895756616124141)
              ·
                refine ⟨9266926407710908731046553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24711803753895756616124141 9266926407710908731046553)
                ·
                  refine ⟨6950194805783181548284915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9266926407710908731046553 6950194805783181548284915)
                  ·
                    refine ⟨10425292208674772322427373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950194805783181548284915 10425292208674772322427373)
                    ·
                      refine ⟨3909484578253039620910265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425292208674772322427373 3909484578253039620910265)
                      ·
                        rfl

theorem cell23_7613694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7613694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613694 prefixEnd_7613694 := by exact prefixLift 7613694
  have htrace : WordTrace (prefixWord ++ tailWord_7613694) baseStart_7613694 baseEnd_7613694 := by
    simpa [prefixWord, tailWord_7613694, baseEnd_7613694] using wordTrace_append hprefix tailTrace_7613694
  have hstable : (prefixWord ++ tailWord_7613694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613694).length < 2 ^ (prefixWord ++ tailWord_7613694).sum := by decide
  have hdescent : baseEnd_7613694 < baseStart_7613694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613757 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 7]
def baseStart_7613757 : Nat := 118140960795 + 7613757 * 2 ^ 59
def prefixEnd_7613757 : Nat := 4983230072969 + 3 ^ 40 * 7613757 * 2
def baseEnd_7613757 : Nat := 434390769726030319380275

theorem tailTrace_7613757 : CollatzResearch.WordTrace tailWord_7613757 prefixEnd_7613757 434390769726030319380275 := by
  unfold tailWord_7613757
  simp only [CollatzResearch.WordTrace]
  refine ⟨277696531477666190016455525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185131020985110793344303683 277696531477666190016455525)
  ·
    refine ⟨52068099652062410628085411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277696531477666190016455525 52068099652062410628085411)
    ·
      refine ⟨78102149478093615942128117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52068099652062410628085411 78102149478093615942128117)
      ·
        refine ⟨7322076513571276494574511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78102149478093615942128117 7322076513571276494574511)
        ·
          refine ⟨10983114770356914741861767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322076513571276494574511 10983114770356914741861767)
          ·
            refine ⟨16474672155535372112792651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983114770356914741861767 16474672155535372112792651)
            ·
              refine ⟨24712008233303058169188977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474672155535372112792651 24712008233303058169188977)
              ·
                refine ⟨18534006174977293626891733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24712008233303058169188977 18534006174977293626891733)
                ·
                  refine ⟨434390769726030319380275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18534006174977293626891733 434390769726030319380275)
                  ·
                    rfl

theorem cell23_7613757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_7613757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613757 prefixEnd_7613757 := by exact prefixLift 7613757
  have htrace : WordTrace (prefixWord ++ tailWord_7613757) baseStart_7613757 baseEnd_7613757 := by
    simpa [prefixWord, tailWord_7613757, baseEnd_7613757] using wordTrace_append hprefix tailTrace_7613757
  have hstable : (prefixWord ++ tailWord_7613757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613757).length < 2 ^ (prefixWord ++ tailWord_7613757).sum := by decide
  have hdescent : baseEnd_7613757 < baseStart_7613757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613760 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2]
def baseStart_7613760 : Nat := 118140960795 + 7613760 * 2 ^ 59
def prefixEnd_7613760 : Nat := 4983230072969 + 3 ^ 40 * 7613760 * 2
def baseEnd_7613760 : Nat := 3909518467976236362684961

theorem tailTrace_7613760 : CollatzResearch.WordTrace tailWord_7613760 prefixEnd_7613760 3909518467976236362684961 := by
  unfold tailWord_7613760
  simp only [CollatzResearch.WordTrace]
  refine ⟨138848320448327660764407367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185131093931103547685876489 138848320448327660764407367)
  ·
    refine ⟨208272480672491491146611051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138848320448327660764407367 208272480672491491146611051)
    ·
      refine ⟨312408721008737236719916577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208272480672491491146611051 312408721008737236719916577)
      ·
        refine ⟨234306540756552927539937433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312408721008737236719916577 234306540756552927539937433)
        ·
          refine ⟨175729905567414695654953075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234306540756552927539937433 175729905567414695654953075)
          ·
            refine ⟨263594858351122043482429613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175729905567414695654953075 263594858351122043482429613)
            ·
              refine ⟨98848071881670766305911105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263594858351122043482429613 98848071881670766305911105)
              ·
                refine ⟨74136053911253074729433329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98848071881670766305911105 74136053911253074729433329)
                ·
                  refine ⟨55602040433439806047074997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74136053911253074729433329 55602040433439806047074997)
                  ·
                    refine ⟨5212691290634981816913281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55602040433439806047074997 5212691290634981816913281)
                    ·
                      refine ⟨3909518467976236362684961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212691290634981816913281 3909518467976236362684961)
                      ·
                        rfl

theorem cell23_7613760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_7613760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613760 prefixEnd_7613760 := by exact prefixLift 7613760
  have htrace : WordTrace (prefixWord ++ tailWord_7613760) baseStart_7613760 baseEnd_7613760 := by
    simpa [prefixWord, tailWord_7613760, baseEnd_7613760] using wordTrace_append hprefix tailTrace_7613760
  have hstable : (prefixWord ++ tailWord_7613760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613760).length < 2 ^ (prefixWord ++ tailWord_7613760).sum := by decide
  have hdescent : baseEnd_7613760 < baseStart_7613760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613793 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7613793 : Nat := 118140960795 + 7613793 * 2 ^ 59
def prefixEnd_7613793 : Nat := 4983230072969 + 3 ^ 40 * 7613793 * 2
def baseEnd_7613793 : Nat := 3909535412837834733572309

theorem tailTrace_7613793 : CollatzResearch.WordTrace tailWord_7613793 prefixEnd_7613793 3909535412837834733572309 := by
  unfold tailWord_7613793
  simp only [CollatzResearch.WordTrace]
  refine ⟨277697844505535768164766033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185131896337023845443177355 277697844505535768164766033)
  ·
    refine ⟨208273383379151826123574525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277697844505535768164766033 208273383379151826123574525)
    ·
      refine ⟨78102518767181934796340447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208273383379151826123574525 78102518767181934796340447)
      ·
        refine ⟨117153778150772902194510671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78102518767181934796340447 117153778150772902194510671)
        ·
          refine ⟨175730667226159353291766007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117153778150772902194510671 175730667226159353291766007)
          ·
            refine ⟨263596000839239029937649011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175730667226159353291766007 263596000839239029937649011)
            ·
              refine ⟨395394001258858544906473517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263596000839239029937649011 395394001258858544906473517)
              ·
                refine ⟨148272750472071954339927569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395394001258858544906473517 148272750472071954339927569)
                ·
                  refine ⟨111204562854053965754945677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148272750472071954339927569 111204562854053965754945677)
                  ·
                    refine ⟨41701711070270237158104629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111204562854053965754945677 41701711070270237158104629)
                    ·
                      refine ⟨3909535412837834733572309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41701711070270237158104629 3909535412837834733572309)
                      ·
                        rfl

theorem cell23_7613793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7613793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613793 prefixEnd_7613793 := by exact prefixLift 7613793
  have htrace : WordTrace (prefixWord ++ tailWord_7613793) baseStart_7613793 baseEnd_7613793 := by
    simpa [prefixWord, tailWord_7613793, baseEnd_7613793] using wordTrace_append hprefix tailTrace_7613793
  have hstable : (prefixWord ++ tailWord_7613793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613793).length < 2 ^ (prefixWord ++ tailWord_7613793).sum := by decide
  have hdescent : baseEnd_7613793 < baseStart_7613793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613803 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_7613803 : Nat := 118140960795 + 7613803 * 2 ^ 59
def prefixEnd_7613803 : Nat := 4983230072969 + 3 ^ 40 * 7613803 * 2
def baseEnd_7613803 : Nat := 3909540547644379694447263

theorem tailTrace_7613803 : CollatzResearch.WordTrace tailWord_7613803 prefixEnd_7613803 3909540547644379694447263 := by
  unfold tailWord_7613803
  simp only [CollatzResearch.WordTrace]
  refine ⟨277698209235499539872630063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185132139490333026581753375 277698209235499539872630063)
  ·
    refine ⟨416547313853249309808945095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277698209235499539872630063 416547313853249309808945095)
    ·
      refine ⟨624820970779873964713417643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416547313853249309808945095 624820970779873964713417643)
      ·
        refine ⟨937231456169810947070126465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624820970779873964713417643 937231456169810947070126465)
        ·
          refine ⟨702923592127358210302594849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937231456169810947070126465 702923592127358210302594849)
          ·
            refine ⟨527192694095518657726946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702923592127358210302594849 527192694095518657726946137)
            ·
              refine ⟨395394520571638993295209603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527192694095518657726946137 395394520571638993295209603)
              ·
                refine ⟨593091780857458489942814405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395394520571638993295209603 593091780857458489942814405)
                ·
                  refine ⟨111204708910773466864277701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593091780857458489942814405 111204708910773466864277701)
                  ·
                    refine ⟨20850882920770025037052069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111204708910773466864277701 20850882920770025037052069)
                    ·
                      refine ⟨3909540547644379694447263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20850882920770025037052069 3909540547644379694447263)
                      ·
                        rfl

theorem cell23_7613803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_7613803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613803 prefixEnd_7613803 := by exact prefixLift 7613803
  have htrace : WordTrace (prefixWord ++ tailWord_7613803) baseStart_7613803 baseEnd_7613803 := by
    simpa [prefixWord, tailWord_7613803, baseEnd_7613803] using wordTrace_append hprefix tailTrace_7613803
  have hstable : (prefixWord ++ tailWord_7613803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613803).length < 2 ^ (prefixWord ++ tailWord_7613803).sum := by decide
  have hdescent : baseEnd_7613803 < baseStart_7613803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613810 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7613810 : Nat := 118140960795 + 7613810 * 2 ^ 59
def prefixEnd_7613810 : Nat := 4983230072969 + 3 ^ 40 * 7613810 * 2
def baseEnd_7613810 : Nat := 3909544142008961167059731

theorem tailTrace_7613810 : CollatzResearch.WordTrace tailWord_7613810 prefixEnd_7613810 3909544142008961167059731 := by
  unfold tailWord_7613810
  simp only [CollatzResearch.WordTrace]
  refine ⟨69424616136618545017033721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185132309697649453378756589 69424616136618545017033721)
  ·
    refine ⟨52068462102463908762775291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69424616136618545017033721 52068462102463908762775291)
    ·
      refine ⟨78102693153695863144162937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52068462102463908762775291 78102693153695863144162937)
      ·
        refine ⟨58577019865271897358122203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78102693153695863144162937 58577019865271897358122203)
        ·
          refine ⟨87865529797907846037183305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58577019865271897358122203 87865529797907846037183305)
          ·
            refine ⟨65899147348430884527887479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87865529797907846037183305 65899147348430884527887479)
            ·
              refine ⟨98848721022646326791831219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65899147348430884527887479 98848721022646326791831219)
              ·
                refine ⟨148273081533969490187746829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98848721022646326791831219 148273081533969490187746829)
                ·
                  refine ⟨55602405575238558820405061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148273081533969490187746829 55602405575238558820405061)
                  ·
                    refine ⟨10425451045357229778825949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55602405575238558820405061 10425451045357229778825949)
                    ·
                      refine ⟨3909544142008961167059731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425451045357229778825949 3909544142008961167059731)
                      ·
                        rfl

theorem cell23_7613810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7613810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613810 prefixEnd_7613810 := by exact prefixLift 7613810
  have htrace : WordTrace (prefixWord ++ tailWord_7613810) baseStart_7613810 baseEnd_7613810 := by
    simpa [prefixWord, tailWord_7613810, baseEnd_7613810] using wordTrace_append hprefix tailTrace_7613810
  have hstable : (prefixWord ++ tailWord_7613810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613810).length < 2 ^ (prefixWord ++ tailWord_7613810).sum := by decide
  have hdescent : baseEnd_7613810 < baseStart_7613810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613844 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7613844 : Nat := 118140960795 + 7613844 * 2 ^ 59
def prefixEnd_7613844 : Nat := 4983230072969 + 3 ^ 40 * 7613844 * 2
def baseEnd_7613844 : Nat := 3909561600351214034034575

theorem tailTrace_7613844 : CollatzResearch.WordTrace tailWord_7613844 prefixEnd_7613844 3909561600351214034034575 := by
  unfold tailWord_7613844
  simp only [CollatzResearch.WordTrace]
  refine ⟨138849852314175501937436293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185133136418900669249915057 138849852314175501937436293)
  ·
    refine ⟨26034347308907906613269305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138849852314175501937436293 26034347308907906613269305)
    ·
      refine ⟨19525760481680929959951979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26034347308907906613269305 19525760481680929959951979)
      ·
        refine ⟨29288640722521394939927969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525760481680929959951979 29288640722521394939927969)
        ·
          refine ⟨21966480541891046204945977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29288640722521394939927969 21966480541891046204945977)
          ·
            refine ⟨16474860406418284653709483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21966480541891046204945977 16474860406418284653709483)
            ·
              refine ⟨24712290609627426980564225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474860406418284653709483 24712290609627426980564225)
              ·
                refine ⟨18534217957220570235423169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24712290609627426980564225 18534217957220570235423169)
                ·
                  refine ⟨13900663467915427676567377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18534217957220570235423169 13900663467915427676567377)
                  ·
                    refine ⟨10425497600936570757425533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13900663467915427676567377 10425497600936570757425533)
                    ·
                      refine ⟨3909561600351214034034575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425497600936570757425533 3909561600351214034034575)
                      ·
                        rfl

theorem cell23_7613844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7613844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613844 prefixEnd_7613844 := by exact prefixLift 7613844
  have htrace : WordTrace (prefixWord ++ tailWord_7613844) baseStart_7613844 baseEnd_7613844 := by
    simpa [prefixWord, tailWord_7613844, baseEnd_7613844] using wordTrace_append hprefix tailTrace_7613844
  have hstable : (prefixWord ++ tailWord_7613844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613844).length < 2 ^ (prefixWord ++ tailWord_7613844).sum := by decide
  have hdescent : baseEnd_7613844 < baseStart_7613844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613860 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_7613860 : Nat := 118140960795 + 7613860 * 2 ^ 59
def prefixEnd_7613860 : Nat := 4983230072969 + 3 ^ 40 * 7613860 * 2
def baseEnd_7613860 : Nat := 1303189938680561990478167

theorem tailTrace_7613860 : CollatzResearch.WordTrace tailWord_7613860 prefixEnd_7613860 1303189938680561990478167 := by
  unfold tailWord_7613860
  simp only [CollatzResearch.WordTrace]
  refine ⟨138850144098146519303727517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185133525464195359071636689 138850144098146519303727517)
  ·
    refine ⟨52068804036804944738897819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138850144098146519303727517 52068804036804944738897819)
    ·
      refine ⟨78103206055207417108346729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52068804036804944738897819 78103206055207417108346729)
      ·
        refine ⟨58577404541405562831260047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78103206055207417108346729 58577404541405562831260047)
        ·
          refine ⟨87866106812108344246890071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58577404541405562831260047 87866106812108344246890071)
          ·
            refine ⟨131799160218162516370335107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87866106812108344246890071 131799160218162516370335107)
            ·
              refine ⟨197698740327243774555502661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131799160218162516370335107 197698740327243774555502661)
              ·
                refine ⟨37068513811358207729156749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197698740327243774555502661 37068513811358207729156749)
                ·
                  refine ⟨13900692679259327898433781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37068513811358207729156749 13900692679259327898433781)
                  ·
                    refine ⟨1303189938680561990478167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13900692679259327898433781 1303189938680561990478167)
                    ·
                      rfl

theorem cell23_7613860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_7613860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613860 prefixEnd_7613860 := by exact prefixLift 7613860
  have htrace : WordTrace (prefixWord ++ tailWord_7613860) baseStart_7613860 baseEnd_7613860 := by
    simpa [prefixWord, tailWord_7613860, baseEnd_7613860] using wordTrace_append hprefix tailTrace_7613860
  have hstable : (prefixWord ++ tailWord_7613860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613860).length < 2 ^ (prefixWord ++ tailWord_7613860).sum := by decide
  have hdescent : baseEnd_7613860 < baseStart_7613860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613864 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 6]
def baseStart_7613864 : Nat := 118140960795 + 7613864 * 2 ^ 59
def prefixEnd_7613864 : Nat := 4983230072969 + 3 ^ 40 * 7613864 * 2
def baseEnd_7613864 : Nat := 434396874440478217309387

theorem tailTrace_7613864 : CollatzResearch.WordTrace tailWord_7613864 prefixEnd_7613864 434396874440478217309387 := by
  unfold tailWord_7613864
  simp only [CollatzResearch.WordTrace]
  refine ⟨138850217044139273645300323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185133622725519031527067097 138850217044139273645300323)
  ·
    refine ⟨208275325566208910467950485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138850217044139273645300323 208275325566208910467950485)
    ·
      refine ⟨9762905885916042678185179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208275325566208910467950485 9762905885916042678185179)
      ·
        refine ⟨14644358828874064017277769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762905885916042678185179 14644358828874064017277769)
        ·
          refine ⟨10983269121655548012958327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644358828874064017277769 10983269121655548012958327)
          ·
            refine ⟨16474903682483322019437491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983269121655548012958327 16474903682483322019437491)
            ·
              refine ⟨24712355523724983029156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474903682483322019437491 24712355523724983029156237)
              ·
                refine ⟨9267133321396868635933589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24712355523724983029156237 9267133321396868635933589)
                ·
                  refine ⟨434396874440478217309387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9267133321396868635933589 434396874440478217309387)
                  ·
                    rfl

theorem cell23_7613864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_7613864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613864 prefixEnd_7613864 := by exact prefixLift 7613864
  have htrace : WordTrace (prefixWord ++ tailWord_7613864) baseStart_7613864 baseEnd_7613864 := by
    simpa [prefixWord, tailWord_7613864, baseEnd_7613864] using wordTrace_append hprefix tailTrace_7613864
  have hstable : (prefixWord ++ tailWord_7613864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613864).length < 2 ^ (prefixWord ++ tailWord_7613864).sum := by decide
  have hdescent : baseEnd_7613864 < baseStart_7613864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613877 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7613877 : Nat := 118140960795 + 7613877 * 2 ^ 59
def prefixEnd_7613877 : Nat := 4983230072969 + 3 ^ 40 * 7613877 * 2
def baseEnd_7613877 : Nat := 1303192848404270801640641

theorem tailTrace_7613877 : CollatzResearch.WordTrace tailWord_7613877 prefixEnd_7613877 1303192848404270801640641 := by
  unfold tailWord_7613877
  simp only [CollatzResearch.WordTrace]
  refine ⟨277700908237231450510823885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185133938824820967007215923 277700908237231450510823885)
  ·
    refine ⟨104137840588961793941558957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277700908237231450510823885 104137840588961793941558957)
    ·
      refine ⟨39051690220860672728084609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104137840588961793941558957 39051690220860672728084609)
      ·
        refine ⟨29288767665645504546063457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39051690220860672728084609 29288767665645504546063457)
        ·
          refine ⟨21966575749234128409547593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29288767665645504546063457 21966575749234128409547593)
          ·
            refine ⟨16474931811925596307160695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21966575749234128409547593 16474931811925596307160695)
            ·
              refine ⟨24712397717888394460741043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474931811925596307160695 24712397717888394460741043)
              ·
                refine ⟨37068596576832591691111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24712397717888394460741043 37068596576832591691111565)
                ·
                  refine ⟨13900723716312221884166837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37068596576832591691111565 13900723716312221884166837)
                  ·
                    refine ⟨1303192848404270801640641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13900723716312221884166837 1303192848404270801640641)
                    ·
                      rfl

theorem cell23_7613877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7613877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613877 prefixEnd_7613877 := by exact prefixLift 7613877
  have htrace : WordTrace (prefixWord ++ tailWord_7613877) baseStart_7613877 baseEnd_7613877 := by
    simpa [prefixWord, tailWord_7613877, baseEnd_7613877] using wordTrace_append hprefix tailTrace_7613877
  have hstable : (prefixWord ++ tailWord_7613877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613877).length < 2 ^ (prefixWord ++ tailWord_7613877).sum := by decide
  have hdescent : baseEnd_7613877 < baseStart_7613877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613908 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7613908 : Nat := 118140960795 + 7613908 * 2 ^ 59
def prefixEnd_7613908 : Nat := 4983230072969 + 3 ^ 40 * 7613908 * 2
def baseEnd_7613908 : Nat := 3909594463113101783634281

theorem tailTrace_7613908 : CollatzResearch.WordTrace tailWord_7613908 prefixEnd_7613908 3909594463113101783634281 := by
  unfold tailWord_7613908
  simp only [CollatzResearch.WordTrace]
  refine ⟨138851019450059571402601189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185134692600079428536801585 138851019450059571402601189)
  ·
    refine ⟨26034566146886169637987723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138851019450059571402601189 26034566146886169637987723)
    ·
      refine ⟨39051849220329254456981585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26034566146886169637987723 39051849220329254456981585)
      ·
        refine ⟨29288886915246940842736189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39051849220329254456981585 29288886915246940842736189)
        ·
          refine ⟨10983332593217602816026071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29288886915246940842736189 10983332593217602816026071)
          ·
            refine ⟨16474998889826404224039107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983332593217602816026071 16474998889826404224039107)
            ·
              refine ⟨24712498334739606336058661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474998889826404224039107 24712498334739606336058661)
              ·
                refine ⟨4633593437763676188010999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24712498334739606336058661 4633593437763676188010999)
                ·
                  refine ⟨6950390156645514282016499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633593437763676188010999 6950390156645514282016499)
                  ·
                    refine ⟨10425585234968271423024749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950390156645514282016499 10425585234968271423024749)
                    ·
                      refine ⟨3909594463113101783634281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425585234968271423024749 3909594463113101783634281)
                      ·
                        rfl

theorem cell23_7613908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7613908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613908 prefixEnd_7613908 := by exact prefixLift 7613908
  have htrace : WordTrace (prefixWord ++ tailWord_7613908) baseStart_7613908 baseEnd_7613908 := by
    simpa [prefixWord, tailWord_7613908, baseEnd_7613908] using wordTrace_append hprefix tailTrace_7613908
  have hstable : (prefixWord ++ tailWord_7613908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613908).length < 2 ^ (prefixWord ++ tailWord_7613908).sum := by decide
  have hdescent : baseEnd_7613908 < baseStart_7613908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613927 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7613927 : Nat := 118140960795 + 7613927 * 2 ^ 59
def prefixEnd_7613927 : Nat := 4983230072969 + 3 ^ 40 * 7613927 * 2
def baseEnd_7613927 : Nat := 3909604219245537209296693

theorem tailTrace_7613927 : CollatzResearch.WordTrace tailWord_7613927 prefixEnd_7613927 3909604219245537209296693 := by
  unfold tailWord_7613927
  simp only [CollatzResearch.WordTrace]
  refine ⟨277702731887050309050144035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185135154591366872700096023 277702731887050309050144035)
  ·
    refine ⟨416554097830575463575216053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277702731887050309050144035 416554097830575463575216053)
    ·
      refine ⟨39051946671616449710176505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416554097830575463575216053 39051946671616449710176505)
      ·
        refine ⟨29288960003712337282632379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39051946671616449710176505 29288960003712337282632379)
        ·
          refine ⟨43933440005568505923948569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29288960003712337282632379 43933440005568505923948569)
          ·
            refine ⟨32950080004176379442961427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43933440005568505923948569 32950080004176379442961427)
            ·
              refine ⟨49425120006264569164442141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32950080004176379442961427 49425120006264569164442141)
              ·
                refine ⟨18534420002349213436665803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49425120006264569164442141 18534420002349213436665803)
                ·
                  refine ⟨27801630003523820154998705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18534420002349213436665803 27801630003523820154998705)
                  ·
                    refine ⟨20851222502642865116249029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27801630003523820154998705 20851222502642865116249029)
                    ·
                      refine ⟨3909604219245537209296693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20851222502642865116249029 3909604219245537209296693)
                      ·
                        rfl

theorem cell23_7613927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7613927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613927 prefixEnd_7613927 := by exact prefixLift 7613927
  have htrace : WordTrace (prefixWord ++ tailWord_7613927) baseStart_7613927 baseEnd_7613927 := by
    simpa [prefixWord, tailWord_7613927, baseEnd_7613927] using wordTrace_append hprefix tailTrace_7613927
  have hstable : (prefixWord ++ tailWord_7613927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613927).length < 2 ^ (prefixWord ++ tailWord_7613927).sum := by decide
  have hdescent : baseEnd_7613927 < baseStart_7613927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613934 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_7613934 : Nat := 118140960795 + 7613934 * 2 ^ 59
def prefixEnd_7613934 : Nat := 4983230072969 + 3 ^ 40 * 7613934 * 2
def baseEnd_7613934 : Nat := 3909607813610118681909161

theorem tailTrace_7613934 : CollatzResearch.WordTrace tailWord_7613934 prefixEnd_7613934 3909607813610118681909161 := by
  unfold tailWord_7613934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34712873399753118655706107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185135324798683299497099237 34712873399753118655706107)
  ·
    refine ⟨52069310099629677983559161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34712873399753118655706107 52069310099629677983559161)
    ·
      refine ⟨39051982574722258487669371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52069310099629677983559161 39051982574722258487669371)
      ·
        refine ⟨58577973862083387731504057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39051982574722258487669371 58577973862083387731504057)
        ·
          refine ⟨43933480396562540798628043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58577973862083387731504057 43933480396562540798628043)
          ·
            refine ⟨65900220594843811197942065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43933480396562540798628043 65900220594843811197942065)
            ·
              refine ⟨49425165446132858398456549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65900220594843811197942065 49425165446132858398456549)
              ·
                refine ⟨9267218521149910949710603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49425165446132858398456549 9267218521149910949710603)
                ·
                  refine ⟨13900827781724866424565905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267218521149910949710603 13900827781724866424565905)
                  ·
                    refine ⟨10425620836293649818424429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13900827781724866424565905 10425620836293649818424429)
                    ·
                      refine ⟨3909607813610118681909161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425620836293649818424429 3909607813610118681909161)
                      ·
                        rfl

theorem cell23_7613934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_7613934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613934 prefixEnd_7613934 := by exact prefixLift 7613934
  have htrace : WordTrace (prefixWord ++ tailWord_7613934) baseStart_7613934 baseEnd_7613934 := by
    simpa [prefixWord, tailWord_7613934, baseEnd_7613934] using wordTrace_append hprefix tailTrace_7613934
  have hstable : (prefixWord ++ tailWord_7613934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613934).length < 2 ^ (prefixWord ++ tailWord_7613934).sum := by decide
  have hdescent : baseEnd_7613934 < baseStart_7613934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613937 : List Nat := [1, 2, 2, 2, 3, 3, 3, 7]
def baseStart_7613937 : Nat := 118140960795 + 7613937 * 2 ^ 59
def prefixEnd_7613937 : Nat := 4983230072969 + 3 ^ 40 * 7613937 * 2
def baseEnd_7613937 : Nat := 144800346446373413710061

theorem tailTrace_7613937 : CollatzResearch.WordTrace tailWord_7613937 prefixEnd_7613937 144800346446373413710061 := by
  unfold tailWord_7613937
  simp only [CollatzResearch.WordTrace]
  refine ⟨277703096617014080758008065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185135397744676053838672043 277703096617014080758008065)
  ·
    refine ⟨208277322462760560568506049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277703096617014080758008065 208277322462760560568506049)
    ·
      refine ⟨156207991847070420426379537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208277322462760560568506049 156207991847070420426379537)
      ·
        refine ⟨117155993885302815319784653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156207991847070420426379537 117155993885302815319784653)
        ·
          refine ⟨43933497706988555744919245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117155993885302815319784653 43933497706988555744919245)
          ·
            refine ⟨16475061640120708404344717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43933497706988555744919245 16475061640120708404344717)
            ·
              refine ⟨6178148115045265651629269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16475061640120708404344717 6178148115045265651629269)
              ·
                refine ⟨144800346446373413710061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6178148115045265651629269 144800346446373413710061)
                ·
                  rfl

theorem cell23_7613937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 7].length) (baseStart_7613937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613937 prefixEnd_7613937 := by exact prefixLift 7613937
  have htrace : WordTrace (prefixWord ++ tailWord_7613937) baseStart_7613937 baseEnd_7613937 := by
    simpa [prefixWord, tailWord_7613937, baseEnd_7613937] using wordTrace_append hprefix tailTrace_7613937
  have hstable : (prefixWord ++ tailWord_7613937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613937).length < 2 ^ (prefixWord ++ tailWord_7613937).sum := by decide
  have hdescent : baseEnd_7613937 < baseStart_7613937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7613947 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 3]
def baseStart_7613947 : Nat := 118140960795 + 7613947 * 2 ^ 59
def prefixEnd_7613947 : Nat := 4983230072969 + 3 ^ 40 * 7613947 * 2
def baseEnd_7613947 : Nat := 3909614488858627131046601

theorem tailTrace_7613947 : CollatzResearch.WordTrace tailWord_7613947 prefixEnd_7613947 3909614488858627131046601 := by
  unfold tailWord_7613947
  simp only [CollatzResearch.WordTrace]
  refine ⟨277703461346977852465872095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185135640897985234977248063 277703461346977852465872095)
  ·
    refine ⟨416555192020466778698808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277703461346977852465872095 416555192020466778698808143)
    ·
      refine ⟨624832788030700168048212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416555192020466778698808143 624832788030700168048212215)
      ·
        refine ⟨937249182046050252072318323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624832788030700168048212215 937249182046050252072318323)
        ·
          refine ⟨1405873773069075378108477485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937249182046050252072318323 1405873773069075378108477485)
          ·
            refine ⟨527202664900903266790679057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405873773069075378108477485 527202664900903266790679057)
            ·
              refine ⟨395401998675677450093009293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527202664900903266790679057 395401998675677450093009293)
              ·
                refine ⟨148275749503379043784878485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395401998675677450093009293 148275749503379043784878485)
                ·
                  refine ⟨6950425757970892677416179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148275749503379043784878485 6950425757970892677416179)
                  ·
                    refine ⟨10425638636956339016124269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950425757970892677416179 10425638636956339016124269)
                    ·
                      refine ⟨3909614488858627131046601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425638636956339016124269 3909614488858627131046601)
                      ·
                        rfl

theorem cell23_7613947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 3].length) (baseStart_7613947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7613947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7613947 prefixEnd_7613947 := by exact prefixLift 7613947
  have htrace : WordTrace (prefixWord ++ tailWord_7613947) baseStart_7613947 baseEnd_7613947 := by
    simpa [prefixWord, tailWord_7613947, baseEnd_7613947] using wordTrace_append hprefix tailTrace_7613947
  have hstable : (prefixWord ++ tailWord_7613947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7613947).length < 2 ^ (prefixWord ++ tailWord_7613947).sum := by decide
  have hdescent : baseEnd_7613947 < baseStart_7613947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7613947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614007 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_7614007 : Nat := 118140960795 + 7614007 * 2 ^ 59
def prefixEnd_7614007 : Nat := 4983230072969 + 3 ^ 40 * 7614007 * 2
def baseEnd_7614007 : Nat := 3909645297697896896296325

theorem tailTrace_7614007 : CollatzResearch.WordTrace tailWord_7614007 prefixEnd_7614007 3909645297697896896296325 := by
  unfold tailWord_7614007
  simp only [CollatzResearch.WordTrace]
  refine ⟨277705649726760482713056275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185137099817840321808704183 277705649726760482713056275)
  ·
    refine ⟨416558474590140724069584413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277705649726760482713056275 416558474590140724069584413)
    ·
      refine ⟨156209427971302771526094155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416558474590140724069584413 156209427971302771526094155)
      ·
        refine ⟨234314141956954157289141233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156209427971302771526094155 234314141956954157289141233)
        ·
          refine ⟨175735606467715617966855925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234314141956954157289141233 175735606467715617966855925)
          ·
            refine ⟨16475213106348339184392743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175735606467715617966855925 16475213106348339184392743)
            ·
              refine ⟨24712819659522508776589115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475213106348339184392743 24712819659522508776589115)
              ·
                refine ⟨37069229489283763164883673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24712819659522508776589115 37069229489283763164883673)
                ·
                  refine ⟨27801922116962822373662755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37069229489283763164883673 27801922116962822373662755)
                  ·
                    refine ⟨41702883175444233560494133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27801922116962822373662755 41702883175444233560494133)
                    ·
                      refine ⟨3909645297697896896296325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41702883175444233560494133 3909645297697896896296325)
                      ·
                        rfl

theorem cell23_7614007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_7614007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614007 prefixEnd_7614007 := by exact prefixLift 7614007
  have htrace : WordTrace (prefixWord ++ tailWord_7614007) baseStart_7614007 baseEnd_7614007 := by
    simpa [prefixWord, tailWord_7614007, baseEnd_7614007] using wordTrace_append hprefix tailTrace_7614007
  have hstable : (prefixWord ++ tailWord_7614007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614007).length < 2 ^ (prefixWord ++ tailWord_7614007).sum := by decide
  have hdescent : baseEnd_7614007 < baseStart_7614007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614021 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_7614021 : Nat := 118140960795 + 7614021 * 2 ^ 59
def prefixEnd_7614021 : Nat := 4983230072969 + 3 ^ 40 * 7614021 * 2
def baseEnd_7614021 : Nat := 3909652486427059841521261

theorem tailTrace_7614021 : CollatzResearch.WordTrace tailWord_7614021 prefixEnd_7614021 3909652486427059841521261 := by
  unfold tailWord_7614021
  simp only [CollatzResearch.WordTrace]
  refine ⟨277706160348709763104065917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185137440232473175402710611 277706160348709763104065917)
  ·
    refine ⟨104139810130766161164024719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277706160348709763104065917 104139810130766161164024719)
    ·
      refine ⟨156209715196149241746037079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104139810130766161164024719 156209715196149241746037079)
      ·
        refine ⟨234314572794223862619055619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156209715196149241746037079 234314572794223862619055619)
        ·
          refine ⟨351471859191335793928583429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234314572794223862619055619 351471859191335793928583429)
          ·
            refine ⟨65900973598375461361609393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351471859191335793928583429 65900973598375461361609393)
            ·
              refine ⟨49425730198781596021207045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65900973598375461361609393 49425730198781596021207045)
              ·
                refine ⟨9267324412271549253976321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49425730198781596021207045 9267324412271549253976321)
                ·
                  refine ⟨6950493309203661940482241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267324412271549253976321 6950493309203661940482241)
                  ·
                    refine ⟨5212869981902746455361681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6950493309203661940482241 5212869981902746455361681)
                    ·
                      refine ⟨3909652486427059841521261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5212869981902746455361681 3909652486427059841521261)
                      ·
                        rfl

theorem cell23_7614021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_7614021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614021 prefixEnd_7614021 := by exact prefixLift 7614021
  have htrace : WordTrace (prefixWord ++ tailWord_7614021) baseStart_7614021 baseEnd_7614021 := by
    simpa [prefixWord, tailWord_7614021, baseEnd_7614021] using wordTrace_append hprefix tailTrace_7614021
  have hstable : (prefixWord ++ tailWord_7614021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614021).length < 2 ^ (prefixWord ++ tailWord_7614021).sum := by decide
  have hdescent : baseEnd_7614021 < baseStart_7614021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614037 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7614037 : Nat := 118140960795 + 7614037 * 2 ^ 59
def prefixEnd_7614037 : Nat := 4983230072969 + 3 ^ 40 * 7614037 * 2
def baseEnd_7614037 : Nat := 3909660702117531778921187

theorem tailTrace_7614037 : CollatzResearch.WordTrace tailWord_7614037 prefixEnd_7614037 3909660702117531778921187 := by
  unfold tailWord_7614037
  simp only [CollatzResearch.WordTrace]
  refine ⟨277706743916651797836648365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185137829277767865224432243 277706743916651797836648365)
  ·
    refine ⟨104140028968744424188743137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277706743916651797836648365 104140028968744424188743137)
    ·
      refine ⟨78105021726558318141557353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104140028968744424188743137 78105021726558318141557353)
      ·
        refine ⟨58578766294918738606168015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78105021726558318141557353 58578766294918738606168015)
        ·
          refine ⟨87868149442378107909252023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58578766294918738606168015 87868149442378107909252023)
          ·
            refine ⟨131802224163567161863878035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87868149442378107909252023 131802224163567161863878035)
            ·
              refine ⟨197703336245350742795817053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131802224163567161863878035 197703336245350742795817053)
              ·
                refine ⟨74138751092006528548431395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197703336245350742795817053 74138751092006528548431395)
                ·
                  refine ⟨111208126638009792822647093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74138751092006528548431395 111208126638009792822647093)
                  ·
                    refine ⟨10425761872313418077123165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111208126638009792822647093 10425761872313418077123165)
                    ·
                      refine ⟨3909660702117531778921187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425761872313418077123165 3909660702117531778921187)
                      ·
                        rfl

theorem cell23_7614037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7614037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614037 prefixEnd_7614037 := by exact prefixLift 7614037
  have htrace : WordTrace (prefixWord ++ tailWord_7614037) baseStart_7614037 baseEnd_7614037 := by
    simpa [prefixWord, tailWord_7614037, baseEnd_7614037] using wordTrace_append hprefix tailTrace_7614037
  have hstable : (prefixWord ++ tailWord_7614037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614037).length < 2 ^ (prefixWord ++ tailWord_7614037).sum := by decide
  have hdescent : baseEnd_7614037 < baseStart_7614037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614057 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_7614057 : Nat := 118140960795 + 7614057 * 2 ^ 59
def prefixEnd_7614057 : Nat := 4983230072969 + 3 ^ 40 * 7614057 * 2
def baseEnd_7614057 : Nat := 1303223657243540566890365

theorem tailTrace_7614057 : CollatzResearch.WordTrace tailWord_7614057 prefixEnd_7614057 1303223657243540566890365 := by
  unfold tailWord_7614057
  simp only [CollatzResearch.WordTrace]
  refine ⟨277707473376579341252376425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185138315584386227501584283 277707473376579341252376425)
  ·
    refine ⟨208280605032434505939282319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277707473376579341252376425 208280605032434505939282319)
    ·
      refine ⟨312420907548651758908923479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208280605032434505939282319 312420907548651758908923479)
      ·
        refine ⟨468631361322977638363385219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312420907548651758908923479 468631361322977638363385219)
        ·
          refine ⟨702947041984466457545077829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468631361322977638363385219 702947041984466457545077829)
          ·
            refine ⟨131802570372087460789702093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 702947041984466457545077829 131802570372087460789702093)
            ·
              refine ⟨49425963889532797796138285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131802570372087460789702093 49425963889532797796138285)
              ·
                refine ⟨18534736458574799173551857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49425963889532797796138285 18534736458574799173551857)
                ·
                  refine ⟨13901052343931099380163893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18534736458574799173551857 13901052343931099380163893)
                  ·
                    refine ⟨1303223657243540566890365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13901052343931099380163893 1303223657243540566890365)
                    ·
                      rfl

theorem cell23_7614057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_7614057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614057 prefixEnd_7614057 := by exact prefixLift 7614057
  have htrace : WordTrace (prefixWord ++ tailWord_7614057) baseStart_7614057 baseEnd_7614057 := by
    simpa [prefixWord, tailWord_7614057, baseEnd_7614057] using wordTrace_append hprefix tailTrace_7614057
  have hstable : (prefixWord ++ tailWord_7614057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614057).length < 2 ^ (prefixWord ++ tailWord_7614057).sum := by decide
  have hdescent : baseEnd_7614057 < baseStart_7614057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614104 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_7614104 : Nat := 118140960795 + 7614104 * 2 ^ 59
def prefixEnd_7614104 : Nat := 4983230072969 + 3 ^ 40 * 7614104 * 2
def baseEnd_7614104 : Nat := 1303231701773794338927793

theorem tailTrace_7614104 : CollatzResearch.WordTrace tailWord_7614104 prefixEnd_7614104 1303231701773794338927793 := by
  unfold tailWord_7614104
  simp only [CollatzResearch.WordTrace]
  refine ⟨138854593803704534139668683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185139458404939378852891577 138854593803704534139668683)
  ·
    refine ⟨208281890705556801209503025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138854593803704534139668683 208281890705556801209503025)
    ·
      refine ⟨156211418029167600907127269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208281890705556801209503025 156211418029167600907127269)
      ·
        refine ⟨29289640880468925170086363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156211418029167600907127269 29289640880468925170086363)
        ·
          refine ⟨43934461320703387755129545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29289640880468925170086363 43934461320703387755129545)
          ·
            refine ⟨32950845990527540816347159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43934461320703387755129545 32950845990527540816347159)
            ·
              refine ⟨49426268985791311224520739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32950845990527540816347159 49426268985791311224520739)
              ·
                refine ⟨74139403478686966836781109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49426268985791311224520739 74139403478686966836781109)
                ·
                  refine ⟨6950569076126903140948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74139403478686966836781109 6950569076126903140948229)
                  ·
                    refine ⟨1303231701773794338927793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950569076126903140948229 1303231701773794338927793)
                    ·
                      rfl

theorem cell23_7614104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_7614104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614104 prefixEnd_7614104 := by exact prefixLift 7614104
  have htrace : WordTrace (prefixWord ++ tailWord_7614104) baseStart_7614104 baseEnd_7614104 := by
    simpa [prefixWord, tailWord_7614104, baseEnd_7614104] using wordTrace_append hprefix tailTrace_7614104
  have hstable : (prefixWord ++ tailWord_7614104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614104).length < 2 ^ (prefixWord ++ tailWord_7614104).sum := by decide
  have hdescent : baseEnd_7614104 < baseStart_7614104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614108 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7614108 : Nat := 118140960795 + 7614108 * 2 ^ 59
def prefixEnd_7614108 : Nat := 4983230072969 + 3 ^ 40 * 7614108 * 2
def baseEnd_7614108 : Nat := 1303232386414667000377787

theorem tailTrace_7614108 : CollatzResearch.WordTrace tailWord_7614108 prefixEnd_7614108 1303232386414667000377787 := by
  unfold tailWord_7614108
  simp only [CollatzResearch.WordTrace]
  refine ⟨138854666749697288481241489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185139555666263051308321985 138854666749697288481241489)
  ·
    refine ⟨104141000062272966360931117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138854666749697288481241489 104141000062272966360931117)
    ·
      refine ⟨39052875023352362385349169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104141000062272966360931117 39052875023352362385349169)
      ·
        refine ⟨29289656267514271789011877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39052875023352362385349169 29289656267514271789011877)
        ·
          refine ⟨5491810550158925960439727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29289656267514271789011877 5491810550158925960439727)
          ·
            refine ⟨8237715825238388940659591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491810550158925960439727 8237715825238388940659591)
            ·
              refine ⟨12356573737857583410989387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237715825238388940659591 12356573737857583410989387)
              ·
                refine ⟨18534860606786375116484081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356573737857583410989387 18534860606786375116484081)
                ·
                  refine ⟨13901145455089781337363061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18534860606786375116484081 13901145455089781337363061)
                  ·
                    refine ⟨1303232386414667000377787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13901145455089781337363061 1303232386414667000377787)
                    ·
                      rfl

theorem cell23_7614108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7614108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614108 prefixEnd_7614108 := by exact prefixLift 7614108
  have htrace : WordTrace (prefixWord ++ tailWord_7614108) baseStart_7614108 baseEnd_7614108 := by
    simpa [prefixWord, tailWord_7614108, baseEnd_7614108] using wordTrace_append hprefix tailTrace_7614108
  have hstable : (prefixWord ++ tailWord_7614108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614108).length < 2 ^ (prefixWord ++ tailWord_7614108).sum := by decide
  have hdescent : baseEnd_7614108 < baseStart_7614108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614111 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7614111 : Nat := 118140960795 + 7614111 * 2 ^ 59
def prefixEnd_7614111 : Nat := 4983230072969 + 3 ^ 40 * 7614111 * 2
def baseEnd_7614111 : Nat := 3909698699685964489395847

theorem tailTrace_7614111 : CollatzResearch.WordTrace tailWord_7614111 prefixEnd_7614111 3909698699685964489395847 := by
  unfold tailWord_7614111
  simp only [CollatzResearch.WordTrace]
  refine ⟨277709442918383708474842187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185139628612255805649894791 277709442918383708474842187)
  ·
    refine ⟨416564164377575562712263281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277709442918383708474842187 416564164377575562712263281)
    ·
      refine ⟨312423123283181672034197461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416564164377575562712263281 312423123283181672034197461)
      ·
        refine ⟨7322416951949570438301503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 312423123283181672034197461 7322416951949570438301503)
        ·
          refine ⟨10983625427924355657452255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322416951949570438301503 10983625427924355657452255)
          ·
            refine ⟨16475438141886533486178383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983625427924355657452255 16475438141886533486178383)
            ·
              refine ⟨24713157212829800229267575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475438141886533486178383 24713157212829800229267575)
              ·
                refine ⟨37069735819244700343901363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24713157212829800229267575 37069735819244700343901363)
                ·
                  refine ⟨55604603728867050515852045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37069735819244700343901363 55604603728867050515852045)
                  ·
                    refine ⟨20851726398325143943444517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55604603728867050515852045 20851726398325143943444517)
                    ·
                      refine ⟨3909698699685964489395847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20851726398325143943444517 3909698699685964489395847)
                      ·
                        rfl

theorem cell23_7614111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7614111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614111 prefixEnd_7614111 := by exact prefixLift 7614111
  have htrace : WordTrace (prefixWord ++ tailWord_7614111) baseStart_7614111 baseEnd_7614111 := by
    simpa [prefixWord, tailWord_7614111, baseEnd_7614111] using wordTrace_append hprefix tailTrace_7614111
  have hstable : (prefixWord ++ tailWord_7614111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614111).length < 2 ^ (prefixWord ++ tailWord_7614111).sum := by decide
  have hdescent : baseEnd_7614111 < baseStart_7614111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614137 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7614137 : Nat := 118140960795 + 7614137 * 2 ^ 59
def prefixEnd_7614137 : Nat := 4983230072969 + 3 ^ 40 * 7614137 * 2
def baseEnd_7614137 : Nat := 3909712050182981387670727

theorem tailTrace_7614137 : CollatzResearch.WordTrace tailWord_7614137 prefixEnd_7614137 3909712050182981387670727 := by
  unfold tailWord_7614137
  simp only [CollatzResearch.WordTrace]
  refine ⟨277710391216289514915288665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185140260810859676610192443 277710391216289514915288665)
  ·
    refine ⟨208282793412217136186466499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277710391216289514915288665 208282793412217136186466499)
    ·
      refine ⟨312424190118325704279699749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208282793412217136186466499 312424190118325704279699749)
      ·
        refine ⟨58579535647186069552443703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312424190118325704279699749 58579535647186069552443703)
        ·
          refine ⟨87869303470779104328665555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58579535647186069552443703 87869303470779104328665555)
          ·
            refine ⟨131803955206168656492998333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87869303470779104328665555 131803955206168656492998333)
            ·
              refine ⟨49426483202313246184874375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131803955206168656492998333 49426483202313246184874375)
              ·
                refine ⟨74139724803469869277311563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49426483202313246184874375 74139724803469869277311563)
                ·
                  refine ⟨111209587205204803915967345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74139724803469869277311563 111209587205204803915967345)
                  ·
                    refine ⟨83407190403903602936975509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111209587205204803915967345 83407190403903602936975509)
                    ·
                      refine ⟨3909712050182981387670727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83407190403903602936975509 3909712050182981387670727)
                      ·
                        rfl

theorem cell23_7614137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7614137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614137 prefixEnd_7614137 := by exact prefixLift 7614137
  have htrace : WordTrace (prefixWord ++ tailWord_7614137) baseStart_7614137 baseEnd_7614137 := by
    simpa [prefixWord, tailWord_7614137, baseEnd_7614137] using wordTrace_append hprefix tailTrace_7614137
  have hstable : (prefixWord ++ tailWord_7614137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614137).length < 2 ^ (prefixWord ++ tailWord_7614137).sum := by decide
  have hdescent : baseEnd_7614137 < baseStart_7614137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614161 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_7614161 : Nat := 118140960795 + 7614161 * 2 ^ 59
def prefixEnd_7614161 : Nat := 4983230072969 + 3 ^ 40 * 7614161 * 2
def baseEnd_7614161 : Nat := 3909724373718689293770617

theorem tailTrace_7614161 : CollatzResearch.WordTrace tailWord_7614161 prefixEnd_7614161 3909724373718689293770617 := by
  unfold tailWord_7614161
  simp only [CollatzResearch.WordTrace]
  refine ⟨277711266568202567014162337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185140844378801711342774891 277711266568202567014162337)
  ·
    refine ⟨208283449926151925260621753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277711266568202567014162337 208283449926151925260621753)
    ·
      refine ⟨156212587444613943945466315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208283449926151925260621753 156212587444613943945466315)
      ·
        refine ⟨234318881166920915918199473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156212587444613943945466315 234318881166920915918199473)
        ·
          refine ⟨175739160875190686938649605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234318881166920915918199473 175739160875190686938649605)
          ·
            refine ⟨32951092664098253800996801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175739160875190686938649605 32951092664098253800996801)
            ·
              refine ⟨24713319498073690350747601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32951092664098253800996801 24713319498073690350747601)
              ·
                refine ⟨18534989623555267763060701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24713319498073690350747601 18534989623555267763060701)
                ·
                  refine ⟨6950621108833225411147763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18534989623555267763060701 6950621108833225411147763)
                  ·
                    refine ⟨10425931663249838116721645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950621108833225411147763 10425931663249838116721645)
                    ·
                      refine ⟨3909724373718689293770617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10425931663249838116721645 3909724373718689293770617)
                      ·
                        rfl

theorem cell23_7614161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_7614161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614161 prefixEnd_7614161 := by exact prefixLift 7614161
  have htrace : WordTrace (prefixWord ++ tailWord_7614161) baseStart_7614161 baseEnd_7614161 := by
    simpa [prefixWord, tailWord_7614161, baseEnd_7614161] using wordTrace_append hprefix tailTrace_7614161
  have hstable : (prefixWord ++ tailWord_7614161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614161).length < 2 ^ (prefixWord ++ tailWord_7614161).sum := by decide
  have hdescent : baseEnd_7614161 < baseStart_7614161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614172 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7614172 : Nat := 118140960795 + 7614172 * 2 ^ 59
def prefixEnd_7614172 : Nat := 4983230072969 + 3 ^ 40 * 7614172 * 2
def baseEnd_7614172 : Nat := 1303243340668629583577689

theorem tailTrace_7614172 : CollatzResearch.WordTrace tailWord_7614172 prefixEnd_7614172 1303243340668629583577689 := by
  unfold tailWord_7614172
  simp only [CollatzResearch.WordTrace]
  refine ⟨138855833885581357946406385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185141111847441810595208513 138855833885581357946406385)
  ·
    refine ⟨104141875414186018459804789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138855833885581357946406385 104141875414186018459804789)
    ·
      refine ⟨9763300820079939230606699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104141875414186018459804789 9763300820079939230606699)
      ·
        refine ⟨14644951230119908845910049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763300820079939230606699 14644951230119908845910049)
        ·
          refine ⟨10983713422589931634432537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644951230119908845910049 10983713422589931634432537)
          ·
            refine ⟨8237785066942448725824403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10983713422589931634432537 8237785066942448725824403)
            ·
              refine ⟨12356677600413673088736605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237785066942448725824403 12356677600413673088736605)
              ·
                refine ⟨4633754100155127408276227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12356677600413673088736605 4633754100155127408276227)
                ·
                  refine ⟨6950631150232691112414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633754100155127408276227 6950631150232691112414341)
                  ·
                    refine ⟨1303243340668629583577689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950631150232691112414341 1303243340668629583577689)
                    ·
                      rfl

theorem cell23_7614172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7614172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614172 prefixEnd_7614172 := by exact prefixLift 7614172
  have htrace : WordTrace (prefixWord ++ tailWord_7614172) baseStart_7614172 baseEnd_7614172 := by
    simpa [prefixWord, tailWord_7614172, baseEnd_7614172] using wordTrace_append hprefix tailTrace_7614172
  have hstable : (prefixWord ++ tailWord_7614172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614172).length < 2 ^ (prefixWord ++ tailWord_7614172).sum := by decide
  have hdescent : baseEnd_7614172 < baseStart_7614172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614204 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7614204 : Nat := 118140960795 + 7614204 * 2 ^ 59
def prefixEnd_7614204 : Nat := 4983230072969 + 3 ^ 40 * 7614204 * 2
def baseEnd_7614204 : Nat := 3909746453386832625532919

theorem tailTrace_7614204 : CollatzResearch.WordTrace tailWord_7614204 prefixEnd_7614204 3909746453386832625532919 := by
  unfold tailWord_7614204
  simp only [CollatzResearch.WordTrace]
  refine ⟨138856417453523392678988833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185141889938031190238651777 138856417453523392678988833)
  ·
    refine ⟨104142313090142544509241625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138856417453523392678988833 104142313090142544509241625)
    ·
      refine ⟨78106734817606908381931219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104142313090142544509241625 78106734817606908381931219)
      ·
        refine ⟨117160102226410362572896829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78106734817606908381931219 117160102226410362572896829)
        ·
          refine ⟨43935038334903885964836311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117160102226410362572896829 43935038334903885964836311)
          ·
            refine ⟨65902557502355828947254467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43935038334903885964836311 65902557502355828947254467)
            ·
              refine ⟨98853836253533743420881701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65902557502355828947254467 98853836253533743420881701)
              ·
                refine ⟨18535094297537576891415319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98853836253533743420881701 18535094297537576891415319)
                ·
                  refine ⟨27802641446306365337122979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18535094297537576891415319 27802641446306365337122979)
                  ·
                    refine ⟨41703962169459548005684469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27802641446306365337122979 41703962169459548005684469)
                    ·
                      refine ⟨3909746453386832625532919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41703962169459548005684469 3909746453386832625532919)
                      ·
                        rfl

theorem cell23_7614204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7614204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614204 prefixEnd_7614204 := by exact prefixLift 7614204
  have htrace : WordTrace (prefixWord ++ tailWord_7614204) baseStart_7614204 baseEnd_7614204 := by
    simpa [prefixWord, tailWord_7614204, baseEnd_7614204] using wordTrace_append hprefix tailTrace_7614204
  have hstable : (prefixWord ++ tailWord_7614204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614204).length < 2 ^ (prefixWord ++ tailWord_7614204).sum := by decide
  have hdescent : baseEnd_7614204 < baseStart_7614204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614207 : List Nat := [1, 1, 2, 2, 1, 3, 3, 10]
def baseStart_7614207 : Nat := 118140960795 + 7614207 * 2 ^ 59
def prefixEnd_7614207 : Nat := 4983230072969 + 3 ^ 40 * 7614207 * 2
def baseEnd_7614207 : Nat := 144805481252918374585015

theorem tailTrace_7614207 : CollatzResearch.WordTrace tailWord_7614207 prefixEnd_7614207 144805481252918374585015 := by
  unfold tailWord_7614207
  simp only [CollatzResearch.WordTrace]
  refine ⟨277712944326035916870336875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185141962884023944580224583 277712944326035916870336875)
  ·
    refine ⟨416569416489053875305505313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277712944326035916870336875 416569416489053875305505313)
    ·
      refine ⟨312427062366790406479128985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416569416489053875305505313 312427062366790406479128985)
      ·
        refine ⟨234320296775092804859346739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312427062366790406479128985 234320296775092804859346739)
        ·
          refine ⟨351480445162639207289020109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234320296775092804859346739 351480445162639207289020109)
          ·
            refine ⟨131805166935989702733382541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351480445162639207289020109 131805166935989702733382541)
            ·
              refine ⟨49426937600996138525018453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131805166935989702733382541 49426937600996138525018453)
              ·
                refine ⟨144805481252918374585015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49426937600996138525018453 144805481252918374585015)
                ·
                  rfl

theorem cell23_7614207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 10].length) (baseStart_7614207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614207 prefixEnd_7614207 := by exact prefixLift 7614207
  have htrace : WordTrace (prefixWord ++ tailWord_7614207) baseStart_7614207 baseEnd_7614207 := by
    simpa [prefixWord, tailWord_7614207, baseEnd_7614207] using wordTrace_append hprefix tailTrace_7614207
  have hstable : (prefixWord ++ tailWord_7614207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614207).length < 2 ^ (prefixWord ++ tailWord_7614207).sum := by decide
  have hdescent : baseEnd_7614207 < baseStart_7614207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614215 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 1, 5]
def baseStart_7614215 : Nat := 118140960795 + 7614215 * 2 ^ 59
def prefixEnd_7614215 : Nat := 4983230072969 + 3 ^ 40 * 7614215 * 2
def baseEnd_7614215 : Nat := 1303250700558010694165123

theorem tailTrace_7614215 : CollatzResearch.WordTrace tailWord_7614215 prefixEnd_7614215 1303250700558010694165123 := by
  unfold tailWord_7614215
  simp only [CollatzResearch.WordTrace]
  refine ⟨277713236110006934236628099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185142157406671289491085399 277713236110006934236628099)
  ·
    refine ⟨416569854165010401354942149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277713236110006934236628099 416569854165010401354942149)
    ·
      refine ⟨78106847655939450254051653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416569854165010401354942149 78106847655939450254051653)
      ·
        refine ⟨14645033935488646922634685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78106847655939450254051653 14645033935488646922634685)
        ·
          refine ⟨5491887725808242595988007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14645033935488646922634685 5491887725808242595988007)
          ·
            refine ⟨8237831588712363893982011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491887725808242595988007 8237831588712363893982011)
            ·
              refine ⟨12356747383068545840973017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237831588712363893982011 12356747383068545840973017)
              ·
                refine ⟨9267560537301409380729763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12356747383068545840973017 9267560537301409380729763)
                ·
                  refine ⟨13901340805952114071094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267560537301409380729763 13901340805952114071094645)
                  ·
                    refine ⟨1303250700558010694165123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13901340805952114071094645 1303250700558010694165123)
                    ·
                      rfl

theorem cell23_7614215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_7614215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614215 prefixEnd_7614215 := by exact prefixLift 7614215
  have htrace : WordTrace (prefixWord ++ tailWord_7614215) baseStart_7614215 baseEnd_7614215 := by
    simpa [prefixWord, tailWord_7614215, baseEnd_7614215] using wordTrace_append hprefix tailTrace_7614215
  have hstable : (prefixWord ++ tailWord_7614215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614215).length < 2 ^ (prefixWord ++ tailWord_7614215).sum := by decide
  have hdescent : baseEnd_7614215 < baseStart_7614215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614218 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_7614218 : Nat := 118140960795 + 7614218 * 2 ^ 59
def prefixEnd_7614218 : Nat := 4983230072969 + 3 ^ 40 * 7614218 * 2
def baseEnd_7614218 : Nat := 3909753642115995570757855

theorem tailTrace_7614218 : CollatzResearch.WordTrace tailWord_7614218 prefixEnd_7614218 3909753642115995570757855 := by
  unfold tailWord_7614218
  simp only [CollatzResearch.WordTrace]
  refine ⟨69428336382249016437246827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185142230352664043832658205 69428336382249016437246827)
  ·
    refine ⟨104142504573373524655870241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69428336382249016437246827 104142504573373524655870241)
    ·
      refine ⟨78106878430030143491902681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104142504573373524655870241 78106878430030143491902681)
      ·
        refine ⟨58580158822522607618927011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78106878430030143491902681 58580158822522607618927011)
        ·
          refine ⟨87870238233783911428390517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58580158822522607618927011 87870238233783911428390517)
          ·
            refine ⟨8237834834417241696411611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87870238233783911428390517 8237834834417241696411611)
            ·
              refine ⟨12356752251625862544617417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237834834417241696411611 12356752251625862544617417)
              ·
                refine ⟨9267564188719396908463063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12356752251625862544617417 9267564188719396908463063)
                ·
                  refine ⟨13901346283079095362694595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267564188719396908463063 13901346283079095362694595)
                  ·
                    refine ⟨20852019424618643044041893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13901346283079095362694595 20852019424618643044041893)
                    ·
                      refine ⟨3909753642115995570757855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20852019424618643044041893 3909753642115995570757855)
                      ·
                        rfl

theorem cell23_7614218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_7614218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614218 prefixEnd_7614218 := by exact prefixLift 7614218
  have htrace : WordTrace (prefixWord ++ tailWord_7614218) baseStart_7614218 baseEnd_7614218 := by
    simpa [prefixWord, tailWord_7614218, baseEnd_7614218] using wordTrace_append hprefix tailTrace_7614218
  have hstable : (prefixWord ++ tailWord_7614218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614218).length < 2 ^ (prefixWord ++ tailWord_7614218).sum := by decide
  have hdescent : baseEnd_7614218 < baseStart_7614218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614231 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7614231 : Nat := 118140960795 + 7614231 * 2 ^ 59
def prefixEnd_7614231 : Nat := 4983230072969 + 3 ^ 40 * 7614231 * 2
def baseEnd_7614231 : Nat := 3909760317364504019895295

theorem tailTrace_7614231 : CollatzResearch.WordTrace tailWord_7614231 prefixEnd_7614231 3909760317364504019895295 := by
  unfold tailWord_7614231
  simp only [CollatzResearch.WordTrace]
  refine ⟨277713819677948968969210547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185142546451965979312807031 277713819677948968969210547)
  ·
    refine ⟨416570729516923453453815821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277713819677948968969210547 416570729516923453453815821)
    ·
      refine ⟨156214023568846295045180933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416570729516923453453815821 156214023568846295045180933)
      ·
        refine ⟨29290129419158680320971425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156214023568846295045180933 29290129419158680320971425)
        ·
          refine ⟨21967597064369010240728569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29290129419158680320971425 21967597064369010240728569)
          ·
            refine ⟨16475697798276757680546427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21967597064369010240728569 16475697798276757680546427)
            ·
              refine ⟨24713546697415136520819641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475697798276757680546427 24713546697415136520819641)
              ·
                refine ⟨18535160023061352390614731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24713546697415136520819641 18535160023061352390614731)
                ·
                  refine ⟨27802740034592028585922097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18535160023061352390614731 27802740034592028585922097)
                  ·
                    refine ⟨20852055025944021439441573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27802740034592028585922097 20852055025944021439441573)
                    ·
                      refine ⟨3909760317364504019895295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20852055025944021439441573 3909760317364504019895295)
                      ·
                        rfl

theorem cell23_7614231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7614231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614231 prefixEnd_7614231 := by exact prefixLift 7614231
  have htrace : WordTrace (prefixWord ++ tailWord_7614231) baseStart_7614231 baseEnd_7614231 := by
    simpa [prefixWord, tailWord_7614231, baseEnd_7614231] using wordTrace_append hprefix tailTrace_7614231
  have hstable : (prefixWord ++ tailWord_7614231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614231).length < 2 ^ (prefixWord ++ tailWord_7614231).sum := by decide
  have hdescent : baseEnd_7614231 < baseStart_7614231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614252 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_7614252 : Nat := 118140960795 + 7614252 * 2 ^ 59
def prefixEnd_7614252 : Nat := 4983230072969 + 3 ^ 40 * 7614252 * 2
def baseEnd_7614252 : Nat := 3909771100458248437732699

theorem tailTrace_7614252 : CollatzResearch.WordTrace tailWord_7614252 prefixEnd_7614252 3909771100458248437732699 := by
  unfold tailWord_7614252
  simp only [CollatzResearch.WordTrace]
  refine ⟨138857292805436444777862505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185143057073915259703816673 138857292805436444777862505)
  ·
    refine ⟨104142969604077333583396879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138857292805436444777862505 104142969604077333583396879)
    ·
      refine ⟨156214454406116000375095319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104142969604077333583396879 156214454406116000375095319)
      ·
        refine ⟨234321681609174000562642979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156214454406116000375095319 234321681609174000562642979)
        ·
          refine ⟨351482522413761000843964469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234321681609174000562642979 351482522413761000843964469)
          ·
            refine ⟨32951486476290093829121669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351482522413761000843964469 32951486476290093829121669)
            ·
              refine ⟨6178403714304392592960313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32951486476290093829121669 6178403714304392592960313)
              ·
                refine ⟨4633802785728294444720235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6178403714304392592960313 4633802785728294444720235)
                ·
                  refine ⟨6950704178592441667080353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633802785728294444720235 6950704178592441667080353)
                  ·
                    refine ⟨5213028133944331250310265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6950704178592441667080353 5213028133944331250310265)
                    ·
                      refine ⟨3909771100458248437732699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213028133944331250310265 3909771100458248437732699)
                      ·
                        rfl

theorem cell23_7614252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_7614252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614252 prefixEnd_7614252 := by exact prefixLift 7614252
  have htrace : WordTrace (prefixWord ++ tailWord_7614252) baseStart_7614252 baseEnd_7614252 := by
    simpa [prefixWord, tailWord_7614252, baseEnd_7614252] using wordTrace_append hprefix tailTrace_7614252
  have hstable : (prefixWord ++ tailWord_7614252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614252).length < 2 ^ (prefixWord ++ tailWord_7614252).sum := by decide
  have hdescent : baseEnd_7614252 < baseStart_7614252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614268 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_7614268 : Nat := 118140960795 + 7614268 * 2 ^ 59
def prefixEnd_7614268 : Nat := 4983230072969 + 3 ^ 40 * 7614268 * 2
def baseEnd_7614268 : Nat := 3909779316148720375132625

theorem tailTrace_7614268 : CollatzResearch.WordTrace tailWord_7614268 prefixEnd_7614268 3909779316148720375132625 := by
  unfold tailWord_7614268
  simp only [CollatzResearch.WordTrace]
  refine ⟨138857584589407462144153729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185143446119209949525538305 138857584589407462144153729)
  ·
    refine ⟨104143188442055596608115297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138857584589407462144153729 104143188442055596608115297)
    ·
      refine ⟨78107391331541697456086473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104143188442055596608115297 78107391331541697456086473)
      ·
        refine ⟨58580543498656273092064855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78107391331541697456086473 58580543498656273092064855)
        ·
          refine ⟨87870815247984409638097283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58580543498656273092064855 87870815247984409638097283)
          ·
            refine ⟨131806222871976614457145925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87870815247984409638097283 131806222871976614457145925)
            ·
              refine ⟨24713666788495615210714861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131806222871976614457145925 24713666788495615210714861)
              ·
                refine ⟨9267625045685855704018073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24713666788495615210714861 9267625045685855704018073)
                ·
                  refine ⟨6950718784264391778013555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267625045685855704018073 6950718784264391778013555)
                  ·
                    refine ⟨10426078176396587667020333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950718784264391778013555 10426078176396587667020333)
                    ·
                      refine ⟨3909779316148720375132625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426078176396587667020333 3909779316148720375132625)
                      ·
                        rfl

theorem cell23_7614268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_7614268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614268 prefixEnd_7614268 := by exact prefixLift 7614268
  have htrace : WordTrace (prefixWord ++ tailWord_7614268) baseStart_7614268 baseEnd_7614268 := by
    simpa [prefixWord, tailWord_7614268, baseEnd_7614268] using wordTrace_append hprefix tailTrace_7614268
  have hstable : (prefixWord ++ tailWord_7614268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614268).length < 2 ^ (prefixWord ++ tailWord_7614268).sum := by decide
  have hdescent : baseEnd_7614268 < baseStart_7614268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614295 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_7614295 : Nat := 118140960795 + 7614295 * 2 ^ 59
def prefixEnd_7614295 : Nat := 4983230072969 + 3 ^ 40 * 7614295 * 2
def baseEnd_7614295 : Nat := 3909793180126391769495001

theorem tailTrace_7614295 : CollatzResearch.WordTrace tailWord_7614295 prefixEnd_7614295 3909793180126391769495001 := by
  unfold tailWord_7614295
  simp only [CollatzResearch.WordTrace]
  refine ⟨277716153949717107899540339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185144102633144738599693559 277716153949717107899540339)
  ·
    refine ⟨416574230924575661849310509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277716153949717107899540339 416574230924575661849310509)
    ·
      refine ⟨156215336596715873193491441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416574230924575661849310509 156215336596715873193491441)
      ·
        refine ⟨117161502447536904895118581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156215336596715873193491441 117161502447536904895118581)
        ·
          refine ⟨10983890854456584833917367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117161502447536904895118581 10983890854456584833917367)
          ·
            refine ⟨16475836281684877250876051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983890854456584833917367 16475836281684877250876051)
            ·
              refine ⟨24713754422527315876314077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475836281684877250876051 24713754422527315876314077)
              ·
                refine ⟨9267657908447743453617779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24713754422527315876314077 9267657908447743453617779)
                ·
                  refine ⟨13901486862671615180426669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267657908447743453617779 13901486862671615180426669)
                  ·
                    refine ⟨5213057573501855692660001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13901486862671615180426669 5213057573501855692660001)
                    ·
                      refine ⟨3909793180126391769495001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213057573501855692660001 3909793180126391769495001)
                      ·
                        rfl

theorem cell23_7614295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_7614295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614295 prefixEnd_7614295 := by exact prefixLift 7614295
  have htrace : WordTrace (prefixWord ++ tailWord_7614295) baseStart_7614295 baseEnd_7614295 := by
    simpa [prefixWord, tailWord_7614295, baseEnd_7614295] using wordTrace_append hprefix tailTrace_7614295
  have hstable : (prefixWord ++ tailWord_7614295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614295).length < 2 ^ (prefixWord ++ tailWord_7614295).sum := by decide
  have hdescent : baseEnd_7614295 < baseStart_7614295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614365 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 5]
def baseStart_7614365 : Nat := 118140960795 + 7614365 * 2 ^ 59
def prefixEnd_7614365 : Nat := 4983230072969 + 3 ^ 40 * 7614365 * 2
def baseEnd_7614365 : Nat := 434425458196911832846631

theorem tailTrace_7614365 : CollatzResearch.WordTrace tailWord_7614365 prefixEnd_7614365 434425458196911832846631 := by
  unfold tailWord_7614365
  simp only [CollatzResearch.WordTrace]
  refine ⟨277718707059463509854588549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185145804706309006569725699 277718707059463509854588549)
  ·
    refine ⟨52072257573649408097735353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277718707059463509854588549 52072257573649408097735353)
    ·
      refine ⟨39054193180237056073301515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52072257573649408097735353 39054193180237056073301515)
      ·
        refine ⟨58581289770355584109952273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39054193180237056073301515 58581289770355584109952273)
        ·
          refine ⟨43935967327766688082464205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58581289770355584109952273 43935967327766688082464205)
          ·
            refine ⟨16475987747912508030924077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43935967327766688082464205 16475987747912508030924077)
            ·
              refine ⟨6178495405467190511596529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16475987747912508030924077 6178495405467190511596529)
              ·
                refine ⟨4633871554100392883697397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6178495405467190511596529 4633871554100392883697397)
                ·
                  refine ⟨434425458196911832846631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4633871554100392883697397 434425458196911832846631)
                  ·
                    rfl

theorem cell23_7614365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_7614365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614365 prefixEnd_7614365 := by exact prefixLift 7614365
  have htrace : WordTrace (prefixWord ++ tailWord_7614365) baseStart_7614365 baseEnd_7614365 := by
    simpa [prefixWord, tailWord_7614365, baseEnd_7614365] using wordTrace_append hprefix tailTrace_7614365
  have hstable : (prefixWord ++ tailWord_7614365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614365).length < 2 ^ (prefixWord ++ tailWord_7614365).sum := by decide
  have hdescent : baseEnd_7614365 < baseStart_7614365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614384 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_7614384 : Nat := 118140960795 + 7614384 * 2 ^ 59
def prefixEnd_7614384 : Nat := 4983230072969 + 3 ^ 40 * 7614384 * 2
def baseEnd_7614384 : Nat := 3909838879904641921282091

theorem tailTrace_7614384 : CollatzResearch.WordTrace tailWord_7614384 prefixEnd_7614384 3909838879904641921282091 := by
  unfold tailWord_7614384
  simp only [CollatzResearch.WordTrace]
  refine ⟨138859700023197338049765103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185146266697596450733020137 138859700023197338049765103)
  ·
    refine ⟨208289550034796007074647655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138859700023197338049765103 208289550034796007074647655)
    ·
      refine ⟨312434325052194010611971483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208289550034796007074647655 312434325052194010611971483)
      ·
        refine ⟨468651487578291015917957225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312434325052194010611971483 468651487578291015917957225)
        ·
          refine ⟨351488615683718261938467919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468651487578291015917957225 351488615683718261938467919)
          ·
            refine ⟨527232923525577392907701879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351488615683718261938467919 527232923525577392907701879)
            ·
              refine ⟨790849385288366089361552819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527232923525577392907701879 790849385288366089361552819)
              ·
                refine ⟨1186274077932549134042329229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790849385288366089361552819 1186274077932549134042329229)
                ·
                  refine ⟨444852779224705925265873461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186274077932549134042329229 444852779224705925265873461)
                  ·
                    refine ⟨41704948052316180493675637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 444852779224705925265873461 41704948052316180493675637)
                    ·
                      refine ⟨3909838879904641921282091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41704948052316180493675637 3909838879904641921282091)
                      ·
                        rfl

theorem cell23_7614384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_7614384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614384 prefixEnd_7614384 := by exact prefixLift 7614384
  have htrace : WordTrace (prefixWord ++ tailWord_7614384) baseStart_7614384 baseEnd_7614384 := by
    simpa [prefixWord, tailWord_7614384, baseEnd_7614384] using wordTrace_append hprefix tailTrace_7614384
  have hstable : (prefixWord ++ tailWord_7614384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614384).length < 2 ^ (prefixWord ++ tailWord_7614384).sum := by decide
  have hdescent : baseEnd_7614384 < baseStart_7614384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614391 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 5, 4]
def baseStart_7614391 : Nat := 118140960795 + 7614391 * 2 ^ 59
def prefixEnd_7614391 : Nat := 4983230072969 + 3 ^ 40 * 7614391 * 2
def baseEnd_7614391 : Nat := 1303280824756407797964853

theorem tailTrace_7614391 : CollatzResearch.WordTrace tailWord_7614391 prefixEnd_7614391 1303280824756407797964853 := by
  unfold tailWord_7614391
  simp only [CollatzResearch.WordTrace]
  refine ⟨277719655357369316295035027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185146436904912877530023351 277719655357369316295035027)
  ·
    refine ⟨416579483036053974442552541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277719655357369316295035027 416579483036053974442552541)
    ·
      refine ⟨156217306138520240415957203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416579483036053974442552541 156217306138520240415957203)
      ·
        refine ⟨234325959207780360623935805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156217306138520240415957203 234325959207780360623935805)
        ·
          refine ⟨87872234702917635233975927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234325959207780360623935805 87872234702917635233975927)
          ·
            refine ⟨131808352054376452850963891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87872234702917635233975927 131808352054376452850963891)
            ·
              refine ⟨197712528081564679276445837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131808352054376452850963891 197712528081564679276445837)
              ·
                refine ⟨74142198030586754728667189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197712528081564679276445837 74142198030586754728667189)
                ·
                  refine ⟨6950831065367508255812549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74142198030586754728667189 6950831065367508255812549)
                  ·
                    refine ⟨1303280824756407797964853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950831065367508255812549 1303280824756407797964853)
                    ·
                      rfl

theorem cell23_7614391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_7614391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614391 prefixEnd_7614391 := by exact prefixLift 7614391
  have htrace : WordTrace (prefixWord ++ tailWord_7614391) baseStart_7614391 baseEnd_7614391 := by
    simpa [prefixWord, tailWord_7614391, baseEnd_7614391] using wordTrace_append hprefix tailTrace_7614391
  have hstable : (prefixWord ++ tailWord_7614391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614391).length < 2 ^ (prefixWord ++ tailWord_7614391).sum := by decide
  have hdescent : baseEnd_7614391 < baseStart_7614391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614398 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7614398 : Nat := 118140960795 + 7614398 * 2 ^ 59
def prefixEnd_7614398 : Nat := 4983230072969 + 3 ^ 40 * 7614398 * 2
def baseEnd_7614398 : Nat := 3909846068633804866507027

theorem tailTrace_7614398 : CollatzResearch.WordTrace tailWord_7614398 prefixEnd_7614398 3909846068633804866507027 := by
  unfold tailWord_7614398
  simp only [CollatzResearch.WordTrace]
  refine ⟨34714988833542994561317481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185146607112229304327026565 34714988833542994561317481)
  ·
    refine ⟨26036241625157245920988111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34714988833542994561317481 26036241625157245920988111)
    ·
      refine ⟨39054362437735868881482167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26036241625157245920988111 39054362437735868881482167)
      ·
        refine ⟨58581543656603803322223251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39054362437735868881482167 58581543656603803322223251)
        ·
          refine ⟨87872315484905704983334877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58581543656603803322223251 87872315484905704983334877)
          ·
            refine ⟨32952118306839639368750579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87872315484905704983334877 32952118306839639368750579)
            ·
              refine ⟨49428177460259459053125869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32952118306839639368750579 49428177460259459053125869)
              ·
                refine ⟨18535566547597297144922201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49428177460259459053125869 18535566547597297144922201)
                ·
                  refine ⟨13901674910697972858691651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18535566547597297144922201 13901674910697972858691651)
                  ·
                    refine ⟨20852512366046959288037477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13901674910697972858691651 20852512366046959288037477)
                    ·
                      refine ⟨3909846068633804866507027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20852512366046959288037477 3909846068633804866507027)
                      ·
                        rfl

theorem cell23_7614398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7614398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614398 prefixEnd_7614398 := by exact prefixLift 7614398
  have htrace : WordTrace (prefixWord ++ tailWord_7614398) baseStart_7614398 baseEnd_7614398 := by
    simpa [prefixWord, tailWord_7614398, baseEnd_7614398] using wordTrace_append hprefix tailTrace_7614398
  have hstable : (prefixWord ++ tailWord_7614398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614398).length < 2 ^ (prefixWord ++ tailWord_7614398).sum := by decide
  have hdescent : baseEnd_7614398 < baseStart_7614398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614448 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_7614448 : Nat := 118140960795 + 7614448 * 2 ^ 59
def prefixEnd_7614448 : Nat := 4983230072969 + 3 ^ 40 * 7614448 * 2
def baseEnd_7614448 : Nat := 3909871742666529670881797

theorem tailTrace_7614448 : CollatzResearch.WordTrace tailWord_7614448 prefixEnd_7614448 3909871742666529670881797 := by
  unfold tailWord_7614448
  simp only [CollatzResearch.WordTrace]
  refine ⟨138860867159081407514929999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185147822878775210019906665 138860867159081407514929999)
  ·
    refine ⟨208291300738622111272394999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138860867159081407514929999 208291300738622111272394999)
    ·
      refine ⟨312436951107933166908592499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208291300738622111272394999 312436951107933166908592499)
      ·
        refine ⟨468655426661899750362888749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312436951107933166908592499 468655426661899750362888749)
        ·
          refine ⟨175745784998212406386083281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468655426661899750362888749 175745784998212406386083281)
          ·
            refine ⟨131809338748659304789562461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175745784998212406386083281 131809338748659304789562461)
            ·
              refine ⟨49428502030747239296085923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131809338748659304789562461 49428502030747239296085923)
              ·
                refine ⟨74142753046120858944128885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49428502030747239296085923 74142753046120858944128885)
                ·
                  refine ⟨6950883098073830526012083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74142753046120858944128885 6950883098073830526012083)
                  ·
                    refine ⟨10426324647110745789018125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950883098073830526012083 10426324647110745789018125)
                    ·
                      refine ⟨3909871742666529670881797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426324647110745789018125 3909871742666529670881797)
                      ·
                        rfl

theorem cell23_7614448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_7614448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614448 prefixEnd_7614448 := by exact prefixLift 7614448
  have htrace : WordTrace (prefixWord ++ tailWord_7614448) baseStart_7614448 baseEnd_7614448 := by
    simpa [prefixWord, tailWord_7614448, baseEnd_7614448] using wordTrace_append hprefix tailTrace_7614448
  have hstable : (prefixWord ++ tailWord_7614448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614448).length < 2 ^ (prefixWord ++ tailWord_7614448).sum := by decide
  have hdescent : baseEnd_7614448 < baseStart_7614448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3]
def baseStart_7614491 : Nat := 118140960795 + 7614491 * 2 ^ 59
def prefixEnd_7614491 : Nat := 4983230072969 + 3 ^ 40 * 7614491 * 2
def baseEnd_7614491 : Nat := 3909893822334673002644099

theorem tailTrace_7614491 : CollatzResearch.WordTrace tailWord_7614491 prefixEnd_7614491 3909893822334673002644099 := by
  unfold tailWord_7614491
  simp only [CollatzResearch.WordTrace]
  refine ⟨277723302657007033373675327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185148868438004688915783551 277723302657007033373675327)
  ·
    refine ⟨416584953985510550060512991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277723302657007033373675327 416584953985510550060512991)
    ·
      refine ⟨624877430978265825090769487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416584953985510550060512991 624877430978265825090769487)
      ·
        refine ⟨937316146467398737636154231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624877430978265825090769487 937316146467398737636154231)
        ·
          refine ⟨1405974219701098106454231347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937316146467398737636154231 1405974219701098106454231347)
          ·
            refine ⟨2108961329551647159681347021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405974219701098106454231347 2108961329551647159681347021)
            ·
              refine ⟨790860498581867684880505133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108961329551647159681347021 790860498581867684880505133)
              ·
                refine ⟨296572686968200381830189425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790860498581867684880505133 296572686968200381830189425)
                ·
                  refine ⟨222429515226150286372642069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296572686968200381830189425 222429515226150286372642069)
                  ·
                    refine ⟨10426383526225794673717597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222429515226150286372642069 10426383526225794673717597)
                    ·
                      refine ⟨3909893822334673002644099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426383526225794673717597 3909893822334673002644099)
                      ·
                        rfl

theorem cell23_7614491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].length) (baseStart_7614491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614491 prefixEnd_7614491 := by exact prefixLift 7614491
  have htrace : WordTrace (prefixWord ++ tailWord_7614491) baseStart_7614491 baseEnd_7614491 := by
    simpa [prefixWord, tailWord_7614491, baseEnd_7614491] using wordTrace_append hprefix tailTrace_7614491
  have hstable : (prefixWord ++ tailWord_7614491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614491).length < 2 ^ (prefixWord ++ tailWord_7614491).sum := by decide
  have hdescent : baseEnd_7614491 < baseStart_7614491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614525 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7614525 : Nat := 118140960795 + 7614525 * 2 ^ 59
def prefixEnd_7614525 : Nat := 4983230072969 + 3 ^ 40 * 7614525 * 2
def baseEnd_7614525 : Nat := 3909911280676925869618943

theorem tailTrace_7614525 : CollatzResearch.WordTrace tailWord_7614525 prefixEnd_7614525 3909911280676925869618943 := by
  unfold tailWord_7614525
  simp only [CollatzResearch.WordTrace]
  refine ⟨277724542738883857180413029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185149695159255904786942019 277724542738883857180413029)
  ·
    refine ⟨52073351763540723221327443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277724542738883857180413029 52073351763540723221327443)
    ·
      refine ⟨78110027645311084831991165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52073351763540723221327443 78110027645311084831991165)
      ·
        refine ⟨29291260366991656811996687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78110027645311084831991165 29291260366991656811996687)
        ·
          refine ⟨43936890550487485217995031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29291260366991656811996687 43936890550487485217995031)
          ·
            refine ⟨65905335825731227826992547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43936890550487485217995031 65905335825731227826992547)
            ·
              refine ⟨98858003738596841740488821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65905335825731227826992547 98858003738596841740488821)
              ·
                refine ⟨9267937850493453913170827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98858003738596841740488821 9267937850493453913170827)
                ·
                  refine ⟨13901906775740180869756241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267937850493453913170827 13901906775740180869756241)
                  ·
                    refine ⟨10426430081805135652317181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13901906775740180869756241 10426430081805135652317181)
                    ·
                      refine ⟨3909911280676925869618943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426430081805135652317181 3909911280676925869618943)
                      ·
                        rfl

theorem cell23_7614525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7614525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614525 prefixEnd_7614525 := by exact prefixLift 7614525
  have htrace : WordTrace (prefixWord ++ tailWord_7614525) baseStart_7614525 baseEnd_7614525 := by
    simpa [prefixWord, tailWord_7614525, baseEnd_7614525] using wordTrace_append hprefix tailTrace_7614525
  have hstable : (prefixWord ++ tailWord_7614525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614525).length < 2 ^ (prefixWord ++ tailWord_7614525).sum := by decide
  have hdescent : baseEnd_7614525 < baseStart_7614525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614561 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7614561 : Nat := 118140960795 + 7614561 * 2 ^ 59
def prefixEnd_7614561 : Nat := 4983230072969 + 3 ^ 40 * 7614561 * 2
def baseEnd_7614561 : Nat := 3909929765980487728768777

theorem tailTrace_7614561 : CollatzResearch.WordTrace tailWord_7614561 prefixEnd_7614561 3909929765980487728768777 := by
  unfold tailWord_7614561
  simp only [CollatzResearch.WordTrace]
  refine ⟨277725855766753435328723537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185150570511168956885815691 277725855766753435328723537)
  ·
    refine ⟨208294391825065076496542653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277725855766753435328723537 208294391825065076496542653)
    ·
      refine ⟨78110396934399403686203495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208294391825065076496542653 78110396934399403686203495)
      ·
        refine ⟨117165595401599105529305243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78110396934399403686203495 117165595401599105529305243)
        ·
          refine ⟨175748393102398658293957865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117165595401599105529305243 175748393102398658293957865)
          ·
            refine ⟨131811294826798993720468399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175748393102398658293957865 131811294826798993720468399)
            ·
              refine ⟨197716942240198490580702599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131811294826798993720468399 197716942240198490580702599)
              ·
                refine ⟨296575413360297735871053899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197716942240198490580702599 296575413360297735871053899)
                ·
                  refine ⟨444863120040446603806580849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296575413360297735871053899 444863120040446603806580849)
                  ·
                    refine ⟨333647340030334952854935637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444863120040446603806580849 333647340030334952854935637)
                    ·
                      refine ⟨3909929765980487728768777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333647340030334952854935637 3909929765980487728768777)
                      ·
                        rfl

theorem cell23_7614561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7614561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614561 prefixEnd_7614561 := by exact prefixLift 7614561
  have htrace : WordTrace (prefixWord ++ tailWord_7614561) baseStart_7614561 baseEnd_7614561 := by
    simpa [prefixWord, tailWord_7614561, baseEnd_7614561] using wordTrace_append hprefix tailTrace_7614561
  have hstable : (prefixWord ++ tailWord_7614561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614561).length < 2 ^ (prefixWord ++ tailWord_7614561).sum := by decide
  have hdescent : baseEnd_7614561 < baseStart_7614561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614608 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_7614608 : Nat := 118140960795 + 7614608 * 2 ^ 59
def prefixEnd_7614608 : Nat := 4983230072969 + 3 ^ 40 * 7614608 * 2
def baseEnd_7614608 : Nat := 3909953899571249044881061

theorem tailTrace_7614608 : CollatzResearch.WordTrace tailWord_7614608 prefixEnd_7614608 3909953899571249044881061 := by
  unfold tailWord_7614608
  simp only [CollatzResearch.WordTrace]
  refine ⟨138863784998791581177842239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185151713331722108237122985 138863784998791581177842239)
  ·
    refine ⟨208295677498187371766763359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138863784998791581177842239 208295677498187371766763359)
    ·
      refine ⟨312443516247281057650145039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208295677498187371766763359 312443516247281057650145039)
      ·
        refine ⟨468665274370921586475217559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312443516247281057650145039 468665274370921586475217559)
        ·
          refine ⟨702997911556382379712826339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468665274370921586475217559 702997911556382379712826339)
          ·
            refine ⟨1054496867334573569569239509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702997911556382379712826339 1054496867334573569569239509)
            ·
              refine ⟨24714770328154068036779051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1054496867334573569569239509 24714770328154068036779051)
              ·
                refine ⟨37072155492231102055168577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24714770328154068036779051 37072155492231102055168577)
                ·
                  refine ⟨27804116619173326541376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37072155492231102055168577 27804116619173326541376433)
                  ·
                    refine ⟨20853087464379994906032325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27804116619173326541376433 20853087464379994906032325)
                    ·
                      refine ⟨3909953899571249044881061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20853087464379994906032325 3909953899571249044881061)
                      ·
                        rfl

theorem cell23_7614608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_7614608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614608 prefixEnd_7614608 := by exact prefixLift 7614608
  have htrace : WordTrace (prefixWord ++ tailWord_7614608) baseStart_7614608 baseEnd_7614608 := by
    simpa [prefixWord, tailWord_7614608, baseEnd_7614608] using wordTrace_append hprefix tailTrace_7614608
  have hstable : (prefixWord ++ tailWord_7614608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614608).length < 2 ^ (prefixWord ++ tailWord_7614608).sum := by decide
  have hdescent : baseEnd_7614608 < baseStart_7614608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614648 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_7614648 : Nat := 118140960795 + 7614648 * 2 ^ 59
def prefixEnd_7614648 : Nat := 4983230072969 + 3 ^ 40 * 7614648 * 2
def baseEnd_7614648 : Nat := 1303324812932476296126959

theorem tailTrace_7614648 : CollatzResearch.WordTrace tailWord_7614648 prefixEnd_7614648 1303324812932476296126959 := by
  unfold tailWord_7614648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138864514458719124593570299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185152685944958832791427065 138864514458719124593570299)
  ·
    refine ⟨208296771688078686890355449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138864514458719124593570299 208296771688078686890355449)
    ·
      refine ⟨156222578766059015167766587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208296771688078686890355449 156222578766059015167766587)
      ·
        refine ⟨234333868149088522751649881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156222578766059015167766587 234333868149088522751649881)
        ·
          refine ⟨175750401111816392063737411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234333868149088522751649881 175750401111816392063737411)
          ·
            refine ⟨263625601667724588095606117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175750401111816392063737411 263625601667724588095606117)
            ·
              refine ⟨49429800312698360267926147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263625601667724588095606117 49429800312698360267926147)
              ·
                refine ⟨74144700469047540401889221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49429800312698360267926147 74144700469047540401889221)
                ·
                  refine ⟨13902131337946413825354229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74144700469047540401889221 13902131337946413825354229)
                  ·
                    refine ⟨1303324812932476296126959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13902131337946413825354229 1303324812932476296126959)
                    ·
                      rfl

theorem cell23_7614648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_7614648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614648 prefixEnd_7614648 := by exact prefixLift 7614648
  have htrace : WordTrace (prefixWord ++ tailWord_7614648) baseStart_7614648 baseEnd_7614648 := by
    simpa [prefixWord, tailWord_7614648, baseEnd_7614648] using wordTrace_append hprefix tailTrace_7614648
  have hstable : (prefixWord ++ tailWord_7614648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614648).length < 2 ^ (prefixWord ++ tailWord_7614648).sum := by decide
  have hdescent : baseEnd_7614648 < baseStart_7614648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614705 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_7614705 : Nat := 118140960795 + 7614705 * 2 ^ 59
def prefixEnd_7614705 : Nat := 4983230072969 + 3 ^ 40 * 7614705 * 2
def baseEnd_7614705 : Nat := 3910003707194735165368115

theorem tailTrace_7614705 : CollatzResearch.WordTrace tailWord_7614705 prefixEnd_7614705 3910003707194735165368115 := by
  unfold tailWord_7614705
  simp only [CollatzResearch.WordTrace]
  refine ⟨277731107878231747921965569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185154071918821165281310379 277731107878231747921965569)
  ·
    refine ⟨208298330908673810941474177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277731107878231747921965569 208298330908673810941474177)
    ·
      refine ⟨156223748181505358206105633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208298330908673810941474177 156223748181505358206105633)
      ·
        refine ⟨117167811136129018654579225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156223748181505358206105633 117167811136129018654579225)
        ·
          refine ⟨87875858352096763990934419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117167811136129018654579225 87875858352096763990934419)
          ·
            refine ⟨131813787528145145986401629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87875858352096763990934419 131813787528145145986401629)
            ·
              refine ⟨49430170323054429744900611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131813787528145145986401629 49430170323054429744900611)
              ·
                refine ⟨74145255484581644617350917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49430170323054429744900611 74145255484581644617350917)
                ·
                  refine ⟨13902235403359058365753297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74145255484581644617350917 13902235403359058365753297)
                  ·
                    refine ⟨10426676552519293774314973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13902235403359058365753297 10426676552519293774314973)
                    ·
                      refine ⟨3910003707194735165368115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426676552519293774314973 3910003707194735165368115)
                      ·
                        rfl

theorem cell23_7614705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_7614705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614705 prefixEnd_7614705 := by exact prefixLift 7614705
  have htrace : WordTrace (prefixWord ++ tailWord_7614705) baseStart_7614705 baseEnd_7614705 := by
    simpa [prefixWord, tailWord_7614705, baseEnd_7614705] using wordTrace_append hprefix tailTrace_7614705
  have hstable : (prefixWord ++ tailWord_7614705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614705).length < 2 ^ (prefixWord ++ tailWord_7614705).sum := by decide
  have hdescent : baseEnd_7614705 < baseStart_7614705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614712 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 1, 4]
def baseStart_7614712 : Nat := 118140960795 + 7614712 * 2 ^ 59
def prefixEnd_7614712 : Nat := 4983230072969 + 3 ^ 40 * 7614712 * 2
def baseEnd_7614712 : Nat := 1303335767186438879326861

theorem tailTrace_7614712 : CollatzResearch.WordTrace tailWord_7614712 prefixEnd_7614712 1303335767186438879326861 := by
  unfold tailWord_7614712
  simp only [CollatzResearch.WordTrace]
  refine ⟨138865681594603194058735195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185154242126137592078313593 138865681594603194058735195)
  ·
    refine ⟨208298522391904791088102793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138865681594603194058735195 208298522391904791088102793)
    ·
      refine ⟨156223891793928593316077095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208298522391904791088102793 156223891793928593316077095)
      ·
        refine ⟨234335837690892889974115643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156223891793928593316077095 234335837690892889974115643)
        ·
          refine ⟨351503756536339334961173465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234335837690892889974115643 351503756536339334961173465)
          ·
            refine ⟨263627817402254501220880099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351503756536339334961173465 263627817402254501220880099)
            ·
              refine ⟨395441726103381751831320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263627817402254501220880099 395441726103381751831320149)
              ·
                refine ⟨4634082727774004904273283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 395441726103381751831320149 4634082727774004904273283)
                ·
                  refine ⟨6951124091661007356409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634082727774004904273283 6951124091661007356409925)
                  ·
                    refine ⟨1303335767186438879326861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951124091661007356409925 1303335767186438879326861)
                    ·
                      rfl

theorem cell23_7614712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_7614712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614712 prefixEnd_7614712 := by exact prefixLift 7614712
  have htrace : WordTrace (prefixWord ++ tailWord_7614712) baseStart_7614712 baseEnd_7614712 := by
    simpa [prefixWord, tailWord_7614712, baseEnd_7614712] using wordTrace_append hprefix tailTrace_7614712
  have hstable : (prefixWord ++ tailWord_7614712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614712).length < 2 ^ (prefixWord ++ tailWord_7614712).sum := by decide
  have hdescent : baseEnd_7614712 < baseStart_7614712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614772 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7614772 : Nat := 118140960795 + 7614772 * 2 ^ 59
def prefixEnd_7614772 : Nat := 4983230072969 + 3 ^ 40 * 7614772 * 2
def baseEnd_7614772 : Nat := 1303346036799528801076769

theorem tailTrace_7614772 : CollatzResearch.WordTrace tailWord_7614772 prefixEnd_7614772 1303346036799528801076769 := by
  unfold tailWord_7614772
  simp only [CollatzResearch.WordTrace]
  refine ⟨138866775784494509182327285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185155701045992678909769713 138866775784494509182327285)
  ·
    refine ⟨13018760229796360235843183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138866775784494509182327285 13018760229796360235843183)
    ·
      refine ⟨19528140344694540353764775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018760229796360235843183 19528140344694540353764775)
      ·
        refine ⟨29292210517041810530647163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528140344694540353764775 29292210517041810530647163)
        ·
          refine ⟨43938315775562715795970745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29292210517041810530647163 43938315775562715795970745)
          ·
            refine ⟨32953736831672036846978059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43938315775562715795970745 32953736831672036846978059)
            ·
              refine ⟨49430605247508055270467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32953736831672036846978059 49430605247508055270467089)
              ·
                refine ⟨37072953935631041452850317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49430605247508055270467089 37072953935631041452850317)
                ·
                  refine ⟨13902357725861640544818869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37072953935631041452850317 13902357725861640544818869)
                  ·
                    refine ⟨1303346036799528801076769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13902357725861640544818869 1303346036799528801076769)
                    ·
                      rfl

theorem cell23_7614772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7614772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614772 prefixEnd_7614772 := by exact prefixLift 7614772
  have htrace : WordTrace (prefixWord ++ tailWord_7614772) baseStart_7614772 baseEnd_7614772 := by
    simpa [prefixWord, tailWord_7614772, baseEnd_7614772] using wordTrace_append hprefix tailTrace_7614772
  have hstable : (prefixWord ++ tailWord_7614772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614772).length < 2 ^ (prefixWord ++ tailWord_7614772).sum := by decide
  have hdescent : baseEnd_7614772 < baseStart_7614772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614826 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7614826 : Nat := 118140960795 + 7614826 * 2 ^ 59
def prefixEnd_7614826 : Nat := 4983230072969 + 3 ^ 40 * 7614826 * 2
def baseEnd_7614826 : Nat := 3910065838353929191955059

theorem tailTrace_7614826 : CollatzResearch.WordTrace tailWord_7614826 prefixEnd_7614826 3910065838353929191955059 := by
  unfold tailWord_7614826
  simp only [CollatzResearch.WordTrace]
  refine ⟨69433880277698346396780083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185157014073862257058080221 69433880277698346396780083)
  ·
    refine ⟨104150820416547519595170125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69433880277698346396780083 104150820416547519595170125)
    ·
      refine ⟨39056557656205319848188797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104150820416547519595170125 39056557656205319848188797)
      ·
        refine ⟨14646209121076994943070799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39056557656205319848188797 14646209121076994943070799)
        ·
          refine ⟨21969313681615492414606199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646209121076994943070799 21969313681615492414606199)
          ·
            refine ⟨32953970522423238621909299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21969313681615492414606199 32953970522423238621909299)
            ·
              refine ⟨49430955783634857932863949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32953970522423238621909299 49430955783634857932863949)
              ·
                refine ⟨18536608418863071724823981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49430955783634857932863949 18536608418863071724823981)
                ·
                  refine ⟨6951228157073651896808993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18536608418863071724823981 6951228157073651896808993)
                  ·
                    refine ⟨5213421117805238922606745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6951228157073651896808993 5213421117805238922606745)
                    ·
                      refine ⟨3910065838353929191955059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213421117805238922606745 3910065838353929191955059)
                      ·
                        rfl

theorem cell23_7614826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7614826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614826 prefixEnd_7614826 := by exact prefixLift 7614826
  have htrace : WordTrace (prefixWord ++ tailWord_7614826) baseStart_7614826 baseEnd_7614826 := by
    simpa [prefixWord, tailWord_7614826, baseEnd_7614826] using wordTrace_append hprefix tailTrace_7614826
  have hstable : (prefixWord ++ tailWord_7614826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614826).length < 2 ^ (prefixWord ++ tailWord_7614826).sum := by decide
  have hdescent : baseEnd_7614826 < baseStart_7614826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614842 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_7614842 : Nat := 118140960795 + 7614842 * 2 ^ 59
def prefixEnd_7614842 : Nat := 4983230072969 + 3 ^ 40 * 7614842 * 2
def baseEnd_7614842 : Nat := 3910074054044401129354985

theorem tailTrace_7614842 : CollatzResearch.WordTrace tailWord_7614842 prefixEnd_7614842 3910074054044401129354985 := by
  unfold tailWord_7614842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69434026169683855079925695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185157403119156946879801853 69434026169683855079925695)
  ·
    refine ⟨104151039254525782619888543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69434026169683855079925695 104151039254525782619888543)
    ·
      refine ⟨156226558881788673929832815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104151039254525782619888543 156226558881788673929832815)
      ·
        refine ⟨234339838322683010894749223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156226558881788673929832815 234339838322683010894749223)
        ·
          refine ⟨351509757484024516342123835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234339838322683010894749223 351509757484024516342123835)
          ·
            refine ⟨527264636226036774513185753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351509757484024516342123835 527264636226036774513185753)
            ·
              refine ⟨395448477169527580884889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527264636226036774513185753 395448477169527580884889315)
              ·
                refine ⟨593172715754291371327333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395448477169527580884889315 593172715754291371327333973)
                ·
                  refine ⟨6951242762745602007742195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 593172715754291371327333973 6951242762745602007742195)
                  ·
                    refine ⟨10426864144118403011613293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951242762745602007742195 10426864144118403011613293)
                    ·
                      refine ⟨3910074054044401129354985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426864144118403011613293 3910074054044401129354985)
                      ·
                        rfl

theorem cell23_7614842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_7614842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614842 prefixEnd_7614842 := by exact prefixLift 7614842
  have htrace : WordTrace (prefixWord ++ tailWord_7614842) baseStart_7614842 baseEnd_7614842 := by
    simpa [prefixWord, tailWord_7614842, baseEnd_7614842] using wordTrace_append hprefix tailTrace_7614842
  have hstable : (prefixWord ++ tailWord_7614842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614842).length < 2 ^ (prefixWord ++ tailWord_7614842).sum := by decide
  have hdescent : baseEnd_7614842 < baseStart_7614842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614849 : List Nat := [1, 2, 4, 3, 1, 3, 2, 7]
def baseStart_7614849 : Nat := 118140960795 + 7614849 * 2 ^ 59
def prefixEnd_7614849 : Nat := 4983230072969 + 3 ^ 40 * 7614849 * 2
def baseEnd_7614849 : Nat := 144817690681814170443239

theorem tailTrace_7614849 : CollatzResearch.WordTrace tailWord_7614849 prefixEnd_7614849 144817690681814170443239 := by
  unfold tailWord_7614849
  simp only [CollatzResearch.WordTrace]
  refine ⟨277736359989710060515207601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185157573326473373676805067 277736359989710060515207601)
  ·
    refine ⟨208302269992282545386405701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277736359989710060515207601 208302269992282545386405701)
    ·
      refine ⟨39056675623552977259951069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208302269992282545386405701 39056675623552977259951069)
      ·
        refine ⟨14646253358832366472481651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39056675623552977259951069 14646253358832366472481651)
        ·
          refine ⟨21969380038248549708722477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646253358832366472481651 21969380038248549708722477)
          ·
            refine ⟨8238517514343206140770929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21969380038248549708722477 8238517514343206140770929)
            ·
              refine ⟨6178888135757404605578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8238517514343206140770929 6178888135757404605578197)
              ·
                refine ⟨144817690681814170443239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6178888135757404605578197 144817690681814170443239)
                ·
                  rfl

theorem cell23_7614849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 7].length) (baseStart_7614849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614849 prefixEnd_7614849 := by exact prefixLift 7614849
  have htrace : WordTrace (prefixWord ++ tailWord_7614849) baseStart_7614849 baseEnd_7614849 := by
    simpa [prefixWord, tailWord_7614849, baseEnd_7614849] using wordTrace_append hprefix tailTrace_7614849
  have hstable : (prefixWord ++ tailWord_7614849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614849).length < 2 ^ (prefixWord ++ tailWord_7614849).sum := by decide
  have hdescent : baseEnd_7614849 < baseStart_7614849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614855 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_7614855 : Nat := 118140960795 + 7614855 * 2 ^ 59
def prefixEnd_7614855 : Nat := 4983230072969 + 3 ^ 40 * 7614855 * 2
def baseEnd_7614855 : Nat := 3910080729292909578492425

theorem tailTrace_7614855 : CollatzResearch.WordTrace tailWord_7614855 prefixEnd_7614855 3910080729292909578492425 := by
  unfold tailWord_7614855
  simp only [CollatzResearch.WordTrace]
  refine ⟨277736578827688323539926019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185157719218458882359950679 277736578827688323539926019)
  ·
    refine ⟨416604868241532485309889029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277736578827688323539926019 416604868241532485309889029)
    ·
      refine ⟨78113412795287340995604193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416604868241532485309889029 78113412795287340995604193)
      ·
        refine ⟨58585059596465505746703145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78113412795287340995604193 58585059596465505746703145)
        ·
          refine ⟨43938794697349129310027359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58585059596465505746703145 43938794697349129310027359)
          ·
            refine ⟨65908192046023693965041039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43938794697349129310027359 65908192046023693965041039)
            ·
              refine ⟨98862288069035540947561559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65908192046023693965041039 98862288069035540947561559)
              ·
                refine ⟨148293432103553311421342339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98862288069035540947561559 148293432103553311421342339)
                ·
                  refine ⟨222440148155329967132013509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148293432103553311421342339 222440148155329967132013509)
                  ·
                    refine ⟨41707527779124368837252533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222440148155329967132013509 41707527779124368837252533)
                    ·
                      refine ⟨3910080729292909578492425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41707527779124368837252533 3910080729292909578492425)
                      ·
                        rfl

theorem cell23_7614855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_7614855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614855 prefixEnd_7614855 := by exact prefixLift 7614855
  have htrace : WordTrace (prefixWord ++ tailWord_7614855) baseStart_7614855 baseEnd_7614855 := by
    simpa [prefixWord, tailWord_7614855, baseEnd_7614855] using wordTrace_append hprefix tailTrace_7614855
  have hstable : (prefixWord ++ tailWord_7614855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614855).length < 2 ^ (prefixWord ++ tailWord_7614855).sum := by decide
  have hdescent : baseEnd_7614855 < baseStart_7614855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614882 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7614882 : Nat := 118140960795 + 7614882 * 2 ^ 59
def prefixEnd_7614882 : Nat := 4983230072969 + 3 ^ 40 * 7614882 * 2
def baseEnd_7614882 : Nat := 3910094593270580972854801

theorem tailTrace_7614882 : CollatzResearch.WordTrace tailWord_7614882 prefixEnd_7614882 3910094593270580972854801 := by
  unfold tailWord_7614882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69434390899647626787789725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185158375732393671434105933 69434390899647626787789725)
  ·
    refine ⟨26037896587367860045421147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69434390899647626787789725 26037896587367860045421147)
    ·
      refine ⟨39056844881051790068131721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26037896587367860045421147 39056844881051790068131721)
      ·
        refine ⟨29292633660788842551098791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39056844881051790068131721 29292633660788842551098791)
        ·
          refine ⟨43938950491183263826648187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29292633660788842551098791 43938950491183263826648187)
          ·
            refine ⟨65908425736774895739972281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43938950491183263826648187 65908425736774895739972281)
            ·
              refine ⟨49431319302581171804979211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65908425736774895739972281 49431319302581171804979211)
              ·
                refine ⟨74146978953871757707468817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49431319302581171804979211 74146978953871757707468817)
                ·
                  refine ⟨55610234215403818280601613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74146978953871757707468817 55610234215403818280601613)
                  ·
                    refine ⟨20853837830776431855225605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55610234215403818280601613 20853837830776431855225605)
                    ·
                      refine ⟨3910094593270580972854801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20853837830776431855225605 3910094593270580972854801)
                      ·
                        rfl

theorem cell23_7614882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7614882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614882 prefixEnd_7614882 := by exact prefixLift 7614882
  have htrace : WordTrace (prefixWord ++ tailWord_7614882) baseStart_7614882 baseEnd_7614882 := by
    simpa [prefixWord, tailWord_7614882, baseEnd_7614882] using wordTrace_append hprefix tailTrace_7614882
  have hstable : (prefixWord ++ tailWord_7614882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614882).length < 2 ^ (prefixWord ++ tailWord_7614882).sum := by decide
  have hdescent : baseEnd_7614882 < baseStart_7614882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614885 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7614885 : Nat := 118140960795 + 7614885 * 2 ^ 59
def prefixEnd_7614885 : Nat := 4983230072969 + 3 ^ 40 * 7614885 * 2
def baseEnd_7614885 : Nat := 3910096133712544461117287

theorem tailTrace_7614885 : CollatzResearch.WordTrace tailWord_7614885 prefixEnd_7614885 3910096133712544461117287 := by
  unfold tailWord_7614885
  simp only [CollatzResearch.WordTrace]
  refine ⟨277737673017579638663518109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185158448678386425775678739 277737673017579638663518109)
  ·
    refine ⟨104151627381592364498819291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277737673017579638663518109 104151627381592364498819291)
    ·
      refine ⟨156227441072388546748228937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104151627381592364498819291 156227441072388546748228937)
      ·
        refine ⟨117170580804291410061171703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156227441072388546748228937 117170580804291410061171703)
        ·
          refine ⟨175755871206437115091757555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117170580804291410061171703 175755871206437115091757555)
          ·
            refine ⟨263633806809655672637636333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175755871206437115091757555 263633806809655672637636333)
            ·
              refine ⟨98862677553620877239113625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263633806809655672637636333 98862677553620877239113625)
              ·
                refine ⟨74147008165215657929335219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98862677553620877239113625 74147008165215657929335219)
                ·
                  refine ⟨111220512247823486894002829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74147008165215657929335219 111220512247823486894002829)
                  ·
                    refine ⟨41707692092933807585251061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111220512247823486894002829 41707692092933807585251061)
                    ·
                      refine ⟨3910096133712544461117287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41707692092933807585251061 3910096133712544461117287)
                      ·
                        rfl

theorem cell23_7614885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7614885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614885 prefixEnd_7614885 := by exact prefixLift 7614885
  have htrace : WordTrace (prefixWord ++ tailWord_7614885) baseStart_7614885 baseEnd_7614885 := by
    simpa [prefixWord, tailWord_7614885, baseEnd_7614885] using wordTrace_append hprefix tailTrace_7614885
  have hstable : (prefixWord ++ tailWord_7614885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614885).length < 2 ^ (prefixWord ++ tailWord_7614885).sum := by decide
  have hdescent : baseEnd_7614885 < baseStart_7614885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614893 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7614893 : Nat := 118140960795 + 7614893 * 2 ^ 59
def prefixEnd_7614893 : Nat := 4983230072969 + 3 ^ 40 * 7614893 * 2
def baseEnd_7614893 : Nat := 3910100241557780429817251

theorem tailTrace_7614893 : CollatzResearch.WordTrace tailWord_7614893 prefixEnd_7614893 3910100241557780429817251 := by
  unfold tailWord_7614893
  simp only [CollatzResearch.WordTrace]
  refine ⟨277737964801550656029809333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185158643201033770686539555 277737964801550656029809333)
  ·
    refine ⟨26037934200145374002794625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277737964801550656029809333 26037934200145374002794625)
    ·
      refine ⟨19528450650109030502095969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26037934200145374002794625 19528450650109030502095969)
      ·
        refine ⟨14646337987581772876571977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19528450650109030502095969 14646337987581772876571977)
        ·
          refine ⟨10984753490686329657428983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14646337987581772876571977 10984753490686329657428983)
          ·
            refine ⟨16477130236029494486143475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10984753490686329657428983 16477130236029494486143475)
            ·
              refine ⟨24715695354044241729215213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477130236029494486143475 24715695354044241729215213)
              ·
                refine ⟨9268385757766590648455705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24715695354044241729215213 9268385757766590648455705)
                ·
                  refine ⟨6951289318324942986341779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9268385757766590648455705 6951289318324942986341779)
                  ·
                    refine ⟨10426933977487414479512669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951289318324942986341779 10426933977487414479512669)
                    ·
                      refine ⟨3910100241557780429817251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10426933977487414479512669 3910100241557780429817251)
                      ·
                        rfl

theorem cell23_7614893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7614893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614893 prefixEnd_7614893 := by exact prefixLift 7614893
  have htrace : WordTrace (prefixWord ++ tailWord_7614893) baseStart_7614893 baseEnd_7614893 := by
    simpa [prefixWord, tailWord_7614893, baseEnd_7614893] using wordTrace_append hprefix tailTrace_7614893
  have hstable : (prefixWord ++ tailWord_7614893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614893).length < 2 ^ (prefixWord ++ tailWord_7614893).sum := by decide
  have hdescent : baseEnd_7614893 < baseStart_7614893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614933 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7614933 : Nat := 118140960795 + 7614933 * 2 ^ 59
def prefixEnd_7614933 : Nat := 4983230072969 + 3 ^ 40 * 7614933 * 2
def baseEnd_7614933 : Nat := 3910120780783960273317067

theorem tailTrace_7614933 : CollatzResearch.WordTrace tailWord_7614933 prefixEnd_7614933 3910120780783960273317067 := by
  unfold tailWord_7614933
  simp only [CollatzResearch.WordTrace]
  refine ⟨277739423721405742861265453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185159615814270495240843635 277739423721405742861265453)
  ·
    refine ⟨104152283895527153572974545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277739423721405742861265453 104152283895527153572974545)
    ·
      refine ⟨78114212921645365179730909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104152283895527153572974545 78114212921645365179730909)
      ·
        refine ⟨29292829845617011942399091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78114212921645365179730909 29292829845617011942399091)
        ·
          refine ⟨43939244768425517913598637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29292829845617011942399091 43939244768425517913598637)
          ·
            refine ⟨16477216788159569217599489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43939244768425517913598637 16477216788159569217599489)
            ·
              refine ⟨12357912591119676913199617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16477216788159569217599489 12357912591119676913199617)
              ·
                refine ⟨9268434443339757684899713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12357912591119676913199617 9268434443339757684899713)
                ·
                  refine ⟨6951325832504818263674785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9268434443339757684899713 6951325832504818263674785)
                  ·
                    refine ⟨5213494374378613697756089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6951325832504818263674785 5213494374378613697756089)
                    ·
                      refine ⟨3910120780783960273317067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213494374378613697756089 3910120780783960273317067)
                      ·
                        rfl

theorem cell23_7614933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7614933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614933 prefixEnd_7614933 := by exact prefixLift 7614933
  have htrace : WordTrace (prefixWord ++ tailWord_7614933) baseStart_7614933 baseEnd_7614933 := by
    simpa [prefixWord, tailWord_7614933, baseEnd_7614933] using wordTrace_append hprefix tailTrace_7614933
  have hstable : (prefixWord ++ tailWord_7614933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614933).length < 2 ^ (prefixWord ++ tailWord_7614933).sum := by decide
  have hdescent : baseEnd_7614933 < baseStart_7614933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7614935 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 7]
def baseStart_7614935 : Nat := 118140960795 + 7614935 * 2 ^ 59
def prefixEnd_7614935 : Nat := 4983230072969 + 3 ^ 40 * 7614935 * 2
def baseEnd_7614935 : Nat := 1303373935915089755164019

theorem tailTrace_7614935 : CollatzResearch.WordTrace tailWord_7614935 prefixEnd_7614935 1303373935915089755164019 := by
  unfold tailWord_7614935
  simp only [CollatzResearch.WordTrace]
  refine ⟨277739496667398497202838259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185159664444932331468558839 277739496667398497202838259)
  ·
    refine ⟨416609245001097745804257389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277739496667398497202838259 416609245001097745804257389)
    ·
      refine ⟨156228466875411654676596521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416609245001097745804257389 156228466875411654676596521)
      ·
        refine ⟨117171350156558741007447391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156228466875411654676596521 117171350156558741007447391)
        ·
          refine ⟨175757025234838111511171087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117171350156558741007447391 175757025234838111511171087)
          ·
            refine ⟨263635537852257167266756631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175757025234838111511171087 263635537852257167266756631)
            ·
              refine ⟨395453306778385750900134947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263635537852257167266756631 395453306778385750900134947)
              ·
                refine ⟨593179960167578626350202421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395453306778385750900134947 593179960167578626350202421)
                ·
                  refine ⟨55610621265710496220331477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593179960167578626350202421 55610621265710496220331477)
                  ·
                    refine ⟨1303373935915089755164019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55610621265710496220331477 1303373935915089755164019)
                    ·
                      rfl

theorem cell23_7614935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_7614935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7614935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7614935 prefixEnd_7614935 := by exact prefixLift 7614935
  have htrace : WordTrace (prefixWord ++ tailWord_7614935) baseStart_7614935 baseEnd_7614935 := by
    simpa [prefixWord, tailWord_7614935, baseEnd_7614935] using wordTrace_append hprefix tailTrace_7614935
  have hstable : (prefixWord ++ tailWord_7614935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7614935).length < 2 ^ (prefixWord ++ tailWord_7614935).sum := by decide
  have hdescent : baseEnd_7614935 < baseStart_7614935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7614935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615016 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7615016 : Nat := 118140960795 + 7615016 * 2 ^ 59
def prefixEnd_7615016 : Nat := 4983230072969 + 3 ^ 40 * 7615016 * 2
def baseEnd_7615016 : Nat := 1303387799892761149526395

theorem tailTrace_7615016 : CollatzResearch.WordTrace tailWord_7615016 prefixEnd_7615016 1303387799892761149526395 := by
  unfold tailWord_7615016
  simp only [CollatzResearch.WordTrace]
  refine ⟨138871225490052524018268451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185161633986736698691024601 138871225490052524018268451)
  ·
    refine ⟨208306838235078786027402677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138871225490052524018268451 208306838235078786027402677)
    ·
      refine ⟨19528766084538636190069001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208306838235078786027402677 19528766084538636190069001)
      ·
        refine ⟨14646574563403977142551751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19528766084538636190069001 14646574563403977142551751)
        ·
          refine ⟨21969861845105965713827627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646574563403977142551751 21969861845105965713827627)
          ·
            refine ⟨32954792767658948570741441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21969861845105965713827627 32954792767658948570741441)
            ·
              refine ⟨24716094575744211428056081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32954792767658948570741441 24716094575744211428056081)
              ·
                refine ⟨18537070931808158571042061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24716094575744211428056081 18537070931808158571042061)
                ·
                  refine ⟨6951401599428059464140773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18537070931808158571042061 6951401599428059464140773)
                  ·
                    refine ⟨1303387799892761149526395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951401599428059464140773 1303387799892761149526395)
                    ·
                      rfl

theorem cell23_7615016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7615016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615016 prefixEnd_7615016 := by exact prefixLift 7615016
  have htrace : WordTrace (prefixWord ++ tailWord_7615016) baseStart_7615016 baseEnd_7615016 := by
    simpa [prefixWord, tailWord_7615016, baseEnd_7615016] using wordTrace_append hprefix tailTrace_7615016
  have hstable : (prefixWord ++ tailWord_7615016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615016).length < 2 ^ (prefixWord ++ tailWord_7615016).sum := by decide
  have hdescent : baseEnd_7615016 < baseStart_7615016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615046 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_7615046 : Nat := 118140960795 + 7615046 * 2 ^ 59
def prefixEnd_7615046 : Nat := 4983230072969 + 3 ^ 40 * 7615046 * 2
def baseEnd_7615046 : Nat := 434464311566435370133783

theorem tailTrace_7615046 : CollatzResearch.WordTrace tailWord_7615046 prefixEnd_7615046 434464311566435370133783 := by
  unfold tailWord_7615046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679485786562386348754031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185162363446664242106752661 8679485786562386348754031)
  ·
    refine ⟨13019228679843579523131047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8679485786562386348754031 13019228679843579523131047)
    ·
      refine ⟨19528843019765369284696571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13019228679843579523131047 19528843019765369284696571)
      ·
        refine ⟨29293264529648053927044857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528843019765369284696571 29293264529648053927044857)
        ·
          refine ⟨21969948397236040445283643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29293264529648053927044857 21969948397236040445283643)
          ·
            refine ⟨32954922595854060667925465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21969948397236040445283643 32954922595854060667925465)
            ·
              refine ⟨24716191946890545500944099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32954922595854060667925465 24716191946890545500944099)
              ·
                refine ⟨37074287920335818251416149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24716191946890545500944099 37074287920335818251416149)
                ·
                  refine ⟨434464311566435370133783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37074287920335818251416149 434464311566435370133783)
                  ·
                    rfl

theorem cell23_7615046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_7615046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615046 prefixEnd_7615046 := by exact prefixLift 7615046
  have htrace : WordTrace (prefixWord ++ tailWord_7615046) baseStart_7615046 baseEnd_7615046 := by
    simpa [prefixWord, tailWord_7615046, baseEnd_7615046] using wordTrace_append hprefix tailTrace_7615046
  have hstable : (prefixWord ++ tailWord_7615046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615046).length < 2 ^ (prefixWord ++ tailWord_7615046).sum := by decide
  have hdescent : baseEnd_7615046 < baseStart_7615046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615096 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_7615096 : Nat := 118140960795 + 7615096 * 2 ^ 59
def prefixEnd_7615096 : Nat := 4983230072969 + 3 ^ 40 * 7615096 * 2
def baseEnd_7615096 : Nat := 3910204478130643135578817

theorem tailTrace_7615096 : CollatzResearch.WordTrace tailWord_7615096 prefixEnd_7615096 3910204478130643135578817 := by
  unfold tailWord_7615096
  simp only [CollatzResearch.WordTrace]
  refine ⟨138872684409907610849724571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185163579213210147799632761 138872684409907610849724571)
  ·
    refine ⟨208309026614861416274586857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138872684409907610849724571 208309026614861416274586857)
    ·
      refine ⟨156231769961146062205940143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208309026614861416274586857 156231769961146062205940143)
      ·
        refine ⟨234347654941719093308910215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156231769961146062205940143 234347654941719093308910215)
        ·
          refine ⟨351521482412578639963365323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234347654941719093308910215 351521482412578639963365323)
          ·
            refine ⟨527282223618867959945047985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351521482412578639963365323 527282223618867959945047985)
            ·
              refine ⟨395461667714150969958785989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527282223618867959945047985 395461667714150969958785989)
              ·
                refine ⟨74149062696403306867272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395461667714150969958785989 74149062696403306867272373)
                ·
                  refine ⟨6951474627787810018806785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74149062696403306867272373 6951474627787810018806785)
                  ·
                    refine ⟨5213605970840857514105089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6951474627787810018806785 5213605970840857514105089)
                    ·
                      refine ⟨3910204478130643135578817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213605970840857514105089 3910204478130643135578817)
                      ·
                        rfl

theorem cell23_7615096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_7615096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615096 prefixEnd_7615096 := by exact prefixLift 7615096
  have htrace : WordTrace (prefixWord ++ tailWord_7615096) baseStart_7615096 baseEnd_7615096 := by
    simpa [prefixWord, tailWord_7615096, baseEnd_7615096] using wordTrace_append hprefix tailTrace_7615096
  have hstable : (prefixWord ++ tailWord_7615096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615096).length < 2 ^ (prefixWord ++ tailWord_7615096).sum := by decide
  have hdescent : baseEnd_7615096 < baseStart_7615096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615102 : List Nat := [4, 2, 17]
def baseStart_7615102 : Nat := 118140960795 + 7615102 * 2 ^ 59
def prefixEnd_7615102 : Nat := 4983230072969 + 3 ^ 40 * 7615102 * 2
def baseEnd_7615102 : Nat := 595977375249896374349

theorem tailTrace_7615102 : CollatzResearch.WordTrace tailWord_7615102 prefixEnd_7615102 595977375249896374349 := by
  unfold tailWord_7615102
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718198457224185590520945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185163725105195656482778373 34718198457224185590520945)
  ·
    refine ⟨26038648842918139192890709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34718198457224185590520945 26038648842918139192890709)
    ·
      refine ⟨595977375249896374349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 26038648842918139192890709 595977375249896374349)
      ·
        rfl

theorem cell23_7615102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 17].length) (baseStart_7615102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615102 prefixEnd_7615102 := by exact prefixLift 7615102
  have htrace : WordTrace (prefixWord ++ tailWord_7615102) baseStart_7615102 baseEnd_7615102 := by
    simpa [prefixWord, tailWord_7615102, baseEnd_7615102] using wordTrace_append hprefix tailTrace_7615102
  have hstable : (prefixWord ++ tailWord_7615102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615102).length < 2 ^ (prefixWord ++ tailWord_7615102).sum := by decide
  have hdescent : baseEnd_7615102 < baseStart_7615102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615136 : List Nat := [2, 1, 1, 4, 4, 1, 3, 7]
def baseStart_7615136 : Nat := 118140960795 + 7615136 * 2 ^ 59
def prefixEnd_7615136 : Nat := 4983230072969 + 3 ^ 40 * 7615136 * 2
def baseEnd_7615136 : Nat := 144823148790993443669579

theorem tailTrace_7615136 : CollatzResearch.WordTrace tailWord_7615136 prefixEnd_7615136 144823148790993443669579 := by
  unfold tailWord_7615136
  simp only [CollatzResearch.WordTrace]
  refine ⟨138873413869835154265452631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185164551826446872353936841 138873413869835154265452631)
  ·
    refine ⟨208310120804752731398178947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138873413869835154265452631 208310120804752731398178947)
    ·
      refine ⟨312465181207129097097268421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208310120804752731398178947 312465181207129097097268421)
      ·
        refine ⟨58587221476336705705737829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312465181207129097097268421 58587221476336705705737829)
        ·
          refine ⟨10985104026813132319825843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58587221476336705705737829 10985104026813132319825843)
          ·
            refine ⟨16477656040219698479738765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985104026813132319825843 16477656040219698479738765)
            ·
              refine ⟨6179121015082386929902037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16477656040219698479738765 6179121015082386929902037)
              ·
                refine ⟨144823148790993443669579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6179121015082386929902037 144823148790993443669579)
                ·
                  rfl

theorem cell23_7615136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 7].length) (baseStart_7615136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615136 prefixEnd_7615136 := by exact prefixLift 7615136
  have htrace : WordTrace (prefixWord ++ tailWord_7615136) baseStart_7615136 baseEnd_7615136 := by
    simpa [prefixWord, tailWord_7615136, baseEnd_7615136] using wordTrace_append hprefix tailTrace_7615136
  have hstable : (prefixWord ++ tailWord_7615136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615136).length < 2 ^ (prefixWord ++ tailWord_7615136).sum := by decide
  have hdescent : baseEnd_7615136 < baseStart_7615136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615150 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7615150 : Nat := 118140960795 + 7615150 * 2 ^ 59
def prefixEnd_7615150 : Nat := 4983230072969 + 3 ^ 40 * 7615150 * 2
def baseEnd_7615150 : Nat := 3910232206085985924303569

theorem tailTrace_7615150 : CollatzResearch.WordTrace tailWord_7615150 prefixEnd_7615150 3910232206085985924303569 := by
  unfold tailWord_7615150
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718417295202448615239363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185164892241079725947943269 34718417295202448615239363)
  ·
    refine ⟨52077625942803672922859045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34718417295202448615239363 52077625942803672922859045)
    ·
      refine ⟨9764554864275688673036071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52077625942803672922859045 9764554864275688673036071)
      ·
        refine ⟨14646832296413533009554107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9764554864275688673036071 14646832296413533009554107)
        ·
          refine ⟨21970248444620299514331161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646832296413533009554107 21970248444620299514331161)
          ·
            refine ⟨16477686333465224635748371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21970248444620299514331161 16477686333465224635748371)
            ·
              refine ⟨24716529500197836953622557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477686333465224635748371 24716529500197836953622557)
              ·
                refine ⟨9268698562574188857608459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24716529500197836953622557 9268698562574188857608459)
                ·
                  refine ⟨13903047843861283286412689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9268698562574188857608459 13903047843861283286412689)
                  ·
                    refine ⟨10427285882895962464809517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13903047843861283286412689 10427285882895962464809517)
                    ·
                      refine ⟨3910232206085985924303569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10427285882895962464809517 3910232206085985924303569)
                      ·
                        rfl

theorem cell23_7615150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7615150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615150 prefixEnd_7615150 := by exact prefixLift 7615150
  have htrace : WordTrace (prefixWord ++ tailWord_7615150) baseStart_7615150 baseEnd_7615150 := by
    simpa [prefixWord, tailWord_7615150, baseEnd_7615150] using wordTrace_append hprefix tailTrace_7615150
  have hstable : (prefixWord ++ tailWord_7615150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615150).length < 2 ^ (prefixWord ++ tailWord_7615150).sum := by decide
  have hdescent : baseEnd_7615150 < baseStart_7615150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615174 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7615174 : Nat := 118140960795 + 7615174 * 2 ^ 59
def prefixEnd_7615174 : Nat := 4983230072969 + 3 ^ 40 * 7615174 * 2
def baseEnd_7615174 : Nat := 1303414843207231276801153

theorem tailTrace_7615174 : CollatzResearch.WordTrace tailWord_7615174 prefixEnd_7615174 1303414843207231276801153 := by
  unfold tailWord_7615174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679631678547895031899643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185165475809021760680525717 8679631678547895031899643)
  ·
    refine ⟨13019447517821842547849465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8679631678547895031899643 13019447517821842547849465)
    ·
      refine ⟨9764585638366381910887099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13019447517821842547849465 9764585638366381910887099)
      ·
        refine ⟨14646878457549572866330649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9764585638366381910887099 14646878457549572866330649)
        ·
          refine ⟨10985158843162179649747987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14646878457549572866330649 10985158843162179649747987)
          ·
            refine ⟨16477738264743269474621981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985158843162179649747987 16477738264743269474621981)
            ·
              refine ⟨6179151849278726052983243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16477738264743269474621981 6179151849278726052983243)
              ·
                refine ⟨9268727773918089079474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179151849278726052983243 9268727773918089079474865)
                ·
                  refine ⟨6951545830438566809606149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9268727773918089079474865 6951545830438566809606149)
                  ·
                    refine ⟨1303414843207231276801153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951545830438566809606149 1303414843207231276801153)
                    ·
                      rfl

theorem cell23_7615174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7615174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615174 prefixEnd_7615174 := by exact prefixLift 7615174
  have htrace : WordTrace (prefixWord ++ tailWord_7615174) baseStart_7615174 baseEnd_7615174 := by
    simpa [prefixWord, tailWord_7615174, baseEnd_7615174] using wordTrace_append hprefix tailTrace_7615174
  have hstable : (prefixWord ++ tailWord_7615174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615174).length < 2 ^ (prefixWord ++ tailWord_7615174).sum := by decide
  have hdescent : baseEnd_7615174 < baseStart_7615174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615226 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_7615226 : Nat := 118140960795 + 7615226 * 2 ^ 59
def prefixEnd_7615226 : Nat := 4983230072969 + 3 ^ 40 * 7615226 * 2
def baseEnd_7615226 : Nat := 434474581179525291883691

theorem tailTrace_7615226 : CollatzResearch.WordTrace tailWord_7615226 prefixEnd_7615226 434474581179525291883691 := by
  unfold tailWord_7615226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69437527577336063475420383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185166740206229502601121021 69437527577336063475420383)
  ·
    refine ⟨104156291366004095213130575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69437527577336063475420383 104156291366004095213130575)
    ·
      refine ⟨156234437049006142819695863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104156291366004095213130575 156234437049006142819695863)
      ·
        refine ⟨234351655573509214229543795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156234437049006142819695863 234351655573509214229543795)
        ·
          refine ⟨351527483360263821344315693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234351655573509214229543795 351527483360263821344315693)
          ·
            refine ⟨131822806260098933004118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351527483360263821344315693 131822806260098933004118385)
            ·
              refine ⟨98867104695074199753088789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131822806260098933004118385 98867104695074199753088789)
              ·
                refine ⟨4634395532581603113426037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98867104695074199753088789 4634395532581603113426037)
                ·
                  refine ⟨434474581179525291883691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634395532581603113426037 434474581179525291883691)
                  ·
                    rfl

theorem cell23_7615226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_7615226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615226 prefixEnd_7615226 := by exact prefixLift 7615226
  have htrace : WordTrace (prefixWord ++ tailWord_7615226) baseStart_7615226 baseEnd_7615226 := by
    simpa [prefixWord, tailWord_7615226, baseEnd_7615226] using wordTrace_append hprefix tailTrace_7615226
  have hstable : (prefixWord ++ tailWord_7615226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615226).length < 2 ^ (prefixWord ++ tailWord_7615226).sum := by decide
  have hdescent : baseEnd_7615226 < baseStart_7615226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615236 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7615236 : Nat := 118140960795 + 7615236 * 2 ^ 59
def prefixEnd_7615236 : Nat := 4983230072969 + 3 ^ 40 * 7615236 * 2
def baseEnd_7615236 : Nat := 3910276365422272587828173

theorem tailTrace_7615236 : CollatzResearch.WordTrace tailWord_7615236 prefixEnd_7615236 3910276365422272587828173 := by
  unfold tailWord_7615236
  simp only [CollatzResearch.WordTrace]
  refine ⟨138875237519654012804772781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185166983359538683739697041 138875237519654012804772781)
  ·
    refine ⟨52078214069870254801789793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138875237519654012804772781 52078214069870254801789793)
    ·
      refine ⟨39058660552402691101342345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52078214069870254801789793 39058660552402691101342345)
      ·
        refine ⟨29293995414302018326006759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39058660552402691101342345 29293995414302018326006759)
        ·
          refine ⟨43940993121453027489010139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29293995414302018326006759 43940993121453027489010139)
          ·
            refine ⟨65911489682179541233515209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43940993121453027489010139 65911489682179541233515209)
            ·
              refine ⟨49433617261634655925136407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65911489682179541233515209 49433617261634655925136407)
              ·
                refine ⟨74150425892451983887704611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49433617261634655925136407 74150425892451983887704611)
                ·
                  refine ⟨111225638838677975831556917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74150425892451983887704611 111225638838677975831556917)
                  ·
                    refine ⟨10427403641126060234208461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111225638838677975831556917 10427403641126060234208461)
                    ·
                      refine ⟨3910276365422272587828173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10427403641126060234208461 3910276365422272587828173)
                      ·
                        rfl

theorem cell23_7615236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7615236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615236 prefixEnd_7615236 := by exact prefixLift 7615236
  have htrace : WordTrace (prefixWord ++ tailWord_7615236) baseStart_7615236 baseEnd_7615236 := by
    simpa [prefixWord, tailWord_7615236, baseEnd_7615236] using wordTrace_append hprefix tailTrace_7615236
  have hstable : (prefixWord ++ tailWord_7615236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615236).length < 2 ^ (prefixWord ++ tailWord_7615236).sum := by decide
  have hdescent : baseEnd_7615236 < baseStart_7615236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615266 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7615266 : Nat := 118140960795 + 7615266 * 2 ^ 59
def prefixEnd_7615266 : Nat := 4983230072969 + 3 ^ 40 * 7615266 * 2
def baseEnd_7615266 : Nat := 3910291769841907470453035

theorem tailTrace_7615266 : CollatzResearch.WordTrace tailWord_7615266 prefixEnd_7615266 3910291769841907470453035 := by
  unfold tailWord_7615266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69437892307299835183284413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185167712819466227155425101 69437892307299835183284413)
  ·
    refine ⟨26039209615237438193731655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69437892307299835183284413 26039209615237438193731655)
    ·
      refine ⟨39058814422856157290597483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039209615237438193731655 39058814422856157290597483)
      ·
        refine ⟨58588221634284235935896225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39058814422856157290597483 58588221634284235935896225)
        ·
          refine ⟨43941166225713176951922169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58588221634284235935896225 43941166225713176951922169)
          ·
            refine ⟨32955874669284882713941627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43941166225713176951922169 32955874669284882713941627)
            ·
              refine ⟨49433812003927324070912441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32955874669284882713941627 49433812003927324070912441)
              ·
                refine ⟨37075359002945493053184331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49433812003927324070912441 37075359002945493053184331)
                ·
                  refine ⟨55613038504418239579776497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37075359002945493053184331 55613038504418239579776497)
                  ·
                    refine ⟨41709778878313679684832373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55613038504418239579776497 41709778878313679684832373)
                    ·
                      refine ⟨3910291769841907470453035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41709778878313679684832373 3910291769841907470453035)
                      ·
                        rfl

theorem cell23_7615266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7615266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615266 prefixEnd_7615266 := by exact prefixLift 7615266
  have htrace : WordTrace (prefixWord ++ tailWord_7615266) baseStart_7615266 baseEnd_7615266 := by
    simpa [prefixWord, tailWord_7615266, baseEnd_7615266] using wordTrace_append hprefix tailTrace_7615266
  have hstable : (prefixWord ++ tailWord_7615266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615266).length < 2 ^ (prefixWord ++ tailWord_7615266).sum := by decide
  have hdescent : baseEnd_7615266 < baseStart_7615266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615276 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_7615276 : Nat := 118140960795 + 7615276 * 2 ^ 59
def prefixEnd_7615276 : Nat := 4983230072969 + 3 ^ 40 * 7615276 * 2
def baseEnd_7615276 : Nat := 3910296904648452431327989

theorem tailTrace_7615276 : CollatzResearch.WordTrace tailWord_7615276 prefixEnd_7615276 3910296904648452431327989 := by
  unfold tailWord_7615276
  simp only [CollatzResearch.WordTrace]
  refine ⟨138875966979581556220500841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185167955972775408294001121 138875966979581556220500841)
  ·
    refine ⟨104156975234686167165375631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138875966979581556220500841 104156975234686167165375631)
    ·
      refine ⟨156235462852029250748063447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104156975234686167165375631 156235462852029250748063447)
      ·
        refine ⟨234353194278043876122095171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156235462852029250748063447 234353194278043876122095171)
        ·
          refine ⟨351529791417065814183142757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234353194278043876122095171 351529791417065814183142757)
          ·
            refine ⟨65911835890699840159339267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351529791417065814183142757 65911835890699840159339267)
            ·
              refine ⟨98867753836049760239008901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65911835890699840159339267 98867753836049760239008901)
              ·
                refine ⟨18537703844259330044814169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98867753836049760239008901 18537703844259330044814169)
                ·
                  refine ⟨13903277883194497533610627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18537703844259330044814169 13903277883194497533610627)
                  ·
                    refine ⟨20854916824791746300415941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13903277883194497533610627 20854916824791746300415941)
                    ·
                      refine ⟨3910296904648452431327989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20854916824791746300415941 3910296904648452431327989)
                      ·
                        rfl

theorem cell23_7615276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_7615276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615276 prefixEnd_7615276 := by exact prefixLift 7615276
  have htrace : WordTrace (prefixWord ++ tailWord_7615276) baseStart_7615276 baseEnd_7615276 := by
    simpa [prefixWord, tailWord_7615276, baseEnd_7615276] using wordTrace_append hprefix tailTrace_7615276
  have hstable : (prefixWord ++ tailWord_7615276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615276).length < 2 ^ (prefixWord ++ tailWord_7615276).sum := by decide
  have hdescent : baseEnd_7615276 < baseStart_7615276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615277 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 5]
def baseStart_7615277 : Nat := 118140960795 + 7615277 * 2 ^ 59
def prefixEnd_7615277 : Nat := 4983230072969 + 3 ^ 40 * 7615277 * 2
def baseEnd_7615277 : Nat := 434477490903234103046165

theorem tailTrace_7615277 : CollatzResearch.WordTrace tailWord_7615277 prefixEnd_7615277 434477490903234103046165 := by
  unfold tailWord_7615277
  simp only [CollatzResearch.WordTrace]
  refine ⟨277751970432159489611788085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185167980288106326407858723 277751970432159489611788085)
  ·
    refine ⟨26039247228014952151105133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277751970432159489611788085 26039247228014952151105133)
    ·
      refine ⟨9764717710505607056664425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26039247228014952151105133 9764717710505607056664425)
      ·
        refine ⟨7323538282879205292498319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9764717710505607056664425 7323538282879205292498319)
        ·
          refine ⟨10985307424318807938747479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323538282879205292498319 10985307424318807938747479)
          ·
            refine ⟨16477961136478211908121219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985307424318807938747479 16477961136478211908121219)
            ·
              refine ⟨24716941704717317862181829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477961136478211908121219 24716941704717317862181829)
              ·
                refine ⟨4634426569634497099159093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24716941704717317862181829 4634426569634497099159093)
                ·
                  refine ⟨434477490903234103046165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634426569634497099159093 434477490903234103046165)
                  ·
                    rfl

theorem cell23_7615277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_7615277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615277 prefixEnd_7615277 := by exact prefixLift 7615277
  have htrace : WordTrace (prefixWord ++ tailWord_7615277) baseStart_7615277 baseEnd_7615277 := by
    simpa [prefixWord, tailWord_7615277, baseEnd_7615277] using wordTrace_append hprefix tailTrace_7615277
  have hstable : (prefixWord ++ tailWord_7615277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615277).length < 2 ^ (prefixWord ++ tailWord_7615277).sum := by decide
  have hdescent : baseEnd_7615277 < baseStart_7615277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615296 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_7615296 : Nat := 118140960795 + 7615296 * 2 ^ 59
def prefixEnd_7615296 : Nat := 4983230072969 + 3 ^ 40 * 7615296 * 2
def baseEnd_7615296 : Nat := 3910307174261542353077897

theorem tailTrace_7615296 : CollatzResearch.WordTrace tailWord_7615296 prefixEnd_7615296 3910307174261542353077897 := by
  unfold tailWord_7615296
  simp only [CollatzResearch.WordTrace]
  refine ⟨138876331709545327928364871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185168442279393770571153161 138876331709545327928364871)
  ·
    refine ⟨208314497564317991892547307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138876331709545327928364871 208314497564317991892547307)
    ·
      refine ⟨312471746346476987838820961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208314497564317991892547307 312471746346476987838820961)
      ·
        refine ⟨234353809759857740879115721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312471746346476987838820961 234353809759857740879115721)
        ·
          refine ⟨175765357319893305659336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234353809759857740879115721 175765357319893305659336791)
          ·
            refine ⟨263648035979839958489005187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175765357319893305659336791 263648035979839958489005187)
            ·
              refine ⟨395472053969759937733507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263648035979839958489005187 395472053969759937733507781)
              ·
                refine ⟨74151010119329988325032709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395472053969759937733507781 74151010119329988325032709)
                ·
                  refine ⟨13903314397374372810943633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74151010119329988325032709 13903314397374372810943633)
                  ·
                    refine ⟨10427485798030779608207725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13903314397374372810943633 10427485798030779608207725)
                    ·
                      refine ⟨3910307174261542353077897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10427485798030779608207725 3910307174261542353077897)
                      ·
                        rfl

theorem cell23_7615296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_7615296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615296 prefixEnd_7615296 := by exact prefixLift 7615296
  have htrace : WordTrace (prefixWord ++ tailWord_7615296) baseStart_7615296 baseEnd_7615296 := by
    simpa [prefixWord, tailWord_7615296, baseEnd_7615296] using wordTrace_append hprefix tailTrace_7615296
  have hstable : (prefixWord ++ tailWord_7615296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615296).length < 2 ^ (prefixWord ++ tailWord_7615296).sum := by decide
  have hdescent : baseEnd_7615296 < baseStart_7615296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615313 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_7615313 : Nat := 118140960795 + 7615313 * 2 ^ 59
def prefixEnd_7615313 : Nat := 4983230072969 + 3 ^ 40 * 7615313 * 2
def baseEnd_7615313 : Nat := 3910315903432668786565319

theorem tailTrace_7615313 : CollatzResearch.WordTrace tailWord_7615313 prefixEnd_7615313 3910315903432668786565319 := by
  unfold tailWord_7615313
  simp only [CollatzResearch.WordTrace]
  refine ⟨277753283460029067760098593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185168855640019378506732395 277753283460029067760098593)
  ·
    refine ⟨208314962595021800820073945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277753283460029067760098593 208314962595021800820073945)
    ·
      refine ⟨156236221946266350615055459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208314962595021800820073945 156236221946266350615055459)
      ·
        refine ⟨234354332919399525922583189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156236221946266350615055459 234354332919399525922583189)
        ·
          refine ⟨10985359355596852777621087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234354332919399525922583189 10985359355596852777621087)
          ·
            refine ⟨16478039033395279166431631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985359355596852777621087 16478039033395279166431631)
            ·
              refine ⟨24717058550092918749647447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16478039033395279166431631 24717058550092918749647447)
              ·
                refine ⟨37075587825139378124471171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24717058550092918749647447 37075587825139378124471171)
                ·
                  refine ⟨55613381737709067186706757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37075587825139378124471171 55613381737709067186706757)
                  ·
                    refine ⟨10427509075820450097507517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55613381737709067186706757 10427509075820450097507517)
                    ·
                      refine ⟨3910315903432668786565319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10427509075820450097507517 3910315903432668786565319)
                      ·
                        rfl

theorem cell23_7615313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_7615313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615313 prefixEnd_7615313 := by exact prefixLift 7615313
  have htrace : WordTrace (prefixWord ++ tailWord_7615313) baseStart_7615313 baseEnd_7615313 := by
    simpa [prefixWord, tailWord_7615313, baseEnd_7615313] using wordTrace_append hprefix tailTrace_7615313
  have hstable : (prefixWord ++ tailWord_7615313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615313).length < 2 ^ (prefixWord ++ tailWord_7615313).sum := by decide
  have hdescent : baseEnd_7615313 < baseStart_7615313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615336 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7615336 : Nat := 118140960795 + 7615336 * 2 ^ 59
def prefixEnd_7615336 : Nat := 4983230072969 + 3 ^ 40 * 7615336 * 2
def baseEnd_7615336 : Nat := 3910327713487722196577713

theorem tailTrace_7615336 : CollatzResearch.WordTrace tailWord_7615336 prefixEnd_7615336 3910327713487722196577713 := by
  unfold tailWord_7615336
  simp only [CollatzResearch.WordTrace]
  refine ⟨138877061169472871344092931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185169414892630495125457241 138877061169472871344092931)
  ·
    refine ⟨208315591754209307016139397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138877061169472871344092931 208315591754209307016139397)
    ·
      refine ⟨39059173453914245065526137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208315591754209307016139397 39059173453914245065526137)
      ·
        refine ⟨29294380090435683799144603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39059173453914245065526137 29294380090435683799144603)
        ·
          refine ⟨43941570135653525698716905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29294380090435683799144603 43941570135653525698716905)
          ·
            refine ⟨32956177601740144274037679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43941570135653525698716905 32956177601740144274037679)
            ·
              refine ⟨49434266402610216411056519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32956177601740144274037679 49434266402610216411056519)
              ·
                refine ⟨74151399603915324616584779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49434266402610216411056519 74151399603915324616584779)
                ·
                  refine ⟨111227099405872986924877169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74151399603915324616584779 111227099405872986924877169)
                  ·
                    refine ⟨83420324554404740193657877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111227099405872986924877169 83420324554404740193657877)
                    ·
                      refine ⟨3910327713487722196577713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83420324554404740193657877 3910327713487722196577713)
                      ·
                        rfl

theorem cell23_7615336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7615336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615336 prefixEnd_7615336 := by exact prefixLift 7615336
  have htrace : WordTrace (prefixWord ++ tailWord_7615336) baseStart_7615336 baseEnd_7615336 := by
    simpa [prefixWord, tailWord_7615336, baseEnd_7615336] using wordTrace_append hprefix tailTrace_7615336
  have hstable : (prefixWord ++ tailWord_7615336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615336).length < 2 ^ (prefixWord ++ tailWord_7615336).sum := by decide
  have hdescent : baseEnd_7615336 < baseStart_7615336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615346 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_7615346 : Nat := 118140960795 + 7615346 * 2 ^ 59
def prefixEnd_7615346 : Nat := 4983230072969 + 3 ^ 40 * 7615346 * 2
def baseEnd_7615346 : Nat := 1303444282764755719150889

theorem tailTrace_7615346 : CollatzResearch.WordTrace tailWord_7615346 prefixEnd_7615346 1303444282764755719150889 := by
  unfold tailWord_7615346
  simp only [CollatzResearch.WordTrace]
  refine ⟨69438621767227378599012473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185169658045939676264033261 69438621767227378599012473)
  ·
    refine ⟨52078966325420533949259355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69438621767227378599012473 52078966325420533949259355)
    ·
      refine ⟨78118449488130800923889033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52078966325420533949259355 78118449488130800923889033)
      ·
        refine ⟨58588837116098100692916775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78118449488130800923889033 58588837116098100692916775)
        ·
          refine ⟨87883255674147151039375163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58588837116098100692916775 87883255674147151039375163)
          ·
            refine ⟨131824883511220726559062745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87883255674147151039375163 131824883511220726559062745)
            ·
              refine ⟨98868662633415544919297059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131824883511220726559062745 98868662633415544919297059)
              ·
                refine ⟨148302993950123317378945589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98868662633415544919297059 148302993950123317378945589)
                ·
                  refine ⟨13903405682824061004276149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148302993950123317378945589 13903405682824061004276149)
                  ·
                    refine ⟨1303444282764755719150889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903405682824061004276149 1303444282764755719150889)
                    ·
                      rfl

theorem cell23_7615346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_7615346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615346 prefixEnd_7615346 := by exact prefixLift 7615346
  have htrace : WordTrace (prefixWord ++ tailWord_7615346) baseStart_7615346 baseEnd_7615346 := by
    simpa [prefixWord, tailWord_7615346, baseEnd_7615346] using wordTrace_append hprefix tailTrace_7615346
  have hstable : (prefixWord ++ tailWord_7615346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615346).length < 2 ^ (prefixWord ++ tailWord_7615346).sum := by decide
  have hdescent : baseEnd_7615346 < baseStart_7615346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615353 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 5, 2]
def baseStart_7615353 : Nat := 118140960795 + 7615353 * 2 ^ 59
def prefixEnd_7615353 : Nat := 4983230072969 + 3 ^ 40 * 7615353 * 2
def baseEnd_7615353 : Nat := 3910336442658848630065135

theorem tailTrace_7615353 : CollatzResearch.WordTrace tailWord_7615353 prefixEnd_7615353 3910336442658848630065135 := by
  unfold tailWord_7615353
  simp only [CollatzResearch.WordTrace]
  refine ⟨277754742379884154591554713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185169828253256103061036475 277754742379884154591554713)
  ·
    refine ⟨208316056784913115943666035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277754742379884154591554713 208316056784913115943666035)
    ·
      refine ⟨312474085177369673915499053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208316056784913115943666035 312474085177369673915499053)
      ·
        refine ⟨117177781941513627718312145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312474085177369673915499053 117177781941513627718312145)
        ·
          refine ⟨87883336456135220788734109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117177781941513627718312145 87883336456135220788734109)
          ·
            refine ⟨32956251171050707795775291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87883336456135220788734109 32956251171050707795775291)
            ·
              refine ⟨49434376756576061693662937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32956251171050707795775291 49434376756576061693662937)
              ·
                refine ⟨37075782567432046270247203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49434376756576061693662937 37075782567432046270247203)
                ·
                  refine ⟨55613673851148069405370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37075782567432046270247203 55613673851148069405370805)
                  ·
                    refine ⟨5213781923545131506753513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55613673851148069405370805 5213781923545131506753513)
                    ·
                      refine ⟨3910336442658848630065135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213781923545131506753513 3910336442658848630065135)
                      ·
                        rfl

theorem cell23_7615353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_7615353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615353 prefixEnd_7615353 := by exact prefixLift 7615353
  have htrace : WordTrace (prefixWord ++ tailWord_7615353) baseStart_7615353 baseEnd_7615353 := by
    simpa [prefixWord, tailWord_7615353, baseEnd_7615353] using wordTrace_append hprefix tailTrace_7615353
  have hstable : (prefixWord ++ tailWord_7615353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615353).length < 2 ^ (prefixWord ++ tailWord_7615353).sum := by decide
  have hdescent : baseEnd_7615353 < baseStart_7615353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615363 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 1, 5]
def baseStart_7615363 : Nat := 118140960795 + 7615363 * 2 ^ 59
def prefixEnd_7615363 : Nat := 4983230072969 + 3 ^ 40 * 7615363 * 2
def baseEnd_7615363 : Nat := 1303447192488464530313363

theorem tailTrace_7615363 : CollatzResearch.WordTrace tailWord_7615363 prefixEnd_7615363 1303447192488464530313363 := by
  unfold tailWord_7615363
  simp only [CollatzResearch.WordTrace]
  refine ⟨277755107109847926299418743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185170071406565284199612495 277755107109847926299418743)
  ·
    refine ⟨416632660664771889449128115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277755107109847926299418743 416632660664771889449128115)
    ·
      refine ⟨624948990997157834173692173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416632660664771889449128115 624948990997157834173692173)
      ·
        refine ⟨234355871623934187815134565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624948990997157834173692173 234355871623934187815134565)
        ·
          refine ⟨43941725929487660215337731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234355871623934187815134565 43941725929487660215337731)
          ·
            refine ⟨65912588894231490323006597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43941725929487660215337731 65912588894231490323006597)
            ·
              refine ⟨12358610417668404435563737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65912588894231490323006597 12358610417668404435563737)
              ·
                refine ⟨9268957813251303326672803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12358610417668404435563737 9268957813251303326672803)
                ·
                  refine ⟨13903436719876954990009205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9268957813251303326672803 13903436719876954990009205)
                  ·
                    refine ⟨1303447192488464530313363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903436719876954990009205 1303447192488464530313363)
                    ·
                      rfl

theorem cell23_7615363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 5].length) (baseStart_7615363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615363 prefixEnd_7615363 := by exact prefixLift 7615363
  have htrace : WordTrace (prefixWord ++ tailWord_7615363) baseStart_7615363 baseEnd_7615363 := by
    simpa [prefixWord, tailWord_7615363, baseEnd_7615363] using wordTrace_append hprefix tailTrace_7615363
  have hstable : (prefixWord ++ tailWord_7615363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615363).length < 2 ^ (prefixWord ++ tailWord_7615363).sum := by decide
  have hdescent : baseEnd_7615363 < baseStart_7615363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615370 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7615370 : Nat := 118140960795 + 7615370 * 2 ^ 59
def prefixEnd_7615370 : Nat := 4983230072969 + 3 ^ 40 * 7615370 * 2
def baseEnd_7615370 : Nat := 3910345171829975063552557

theorem tailTrace_7615370 : CollatzResearch.WordTrace tailWord_7615370 prefixEnd_7615370 3910345171829975063552557 := by
  unfold tailWord_7615370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69438840605205641623730891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185170241613881710996615709 69438840605205641623730891)
  ·
    refine ⟨104158260907808462435596337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69438840605205641623730891 104158260907808462435596337)
    ·
      refine ⟨78118695680856346826697253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104158260907808462435596337 78118695680856346826697253)
      ·
        refine ⟨14647255440160565030005735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78118695680856346826697253 14647255440160565030005735)
        ·
          refine ⟨21970883160240847545008603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647255440160565030005735 21970883160240847545008603)
          ·
            refine ⟨32956324740361271317512905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21970883160240847545008603 32956324740361271317512905)
            ·
              refine ⟨24717243555270953488134679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32956324740361271317512905 24717243555270953488134679)
              ·
                refine ⟨37075865332906430232202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24717243555270953488134679 37075865332906430232202019)
                ·
                  refine ⟨55613797999359645348303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37075865332906430232202019 55613797999359645348303029)
                  ·
                    refine ⟨5213793562439966751403409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55613797999359645348303029 5213793562439966751403409)
                    ·
                      refine ⟨3910345171829975063552557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213793562439966751403409 3910345171829975063552557)
                      ·
                        rfl

theorem cell23_7615370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7615370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615370 prefixEnd_7615370 := by exact prefixLift 7615370
  have htrace : WordTrace (prefixWord ++ tailWord_7615370) baseStart_7615370 baseEnd_7615370 := by
    simpa [prefixWord, tailWord_7615370, baseEnd_7615370] using wordTrace_append hprefix tailTrace_7615370
  have hstable : (prefixWord ++ tailWord_7615370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615370).length < 2 ^ (prefixWord ++ tailWord_7615370).sum := by decide
  have hdescent : baseEnd_7615370 < baseStart_7615370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615383 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_7615383 : Nat := 118140960795 + 7615383 * 2 ^ 59
def prefixEnd_7615383 : Nat := 4983230072969 + 3 ^ 40 * 7615383 * 2
def baseEnd_7615383 : Nat := 3910351847078483512689997

theorem tailTrace_7615383 : CollatzResearch.WordTrace tailWord_7615383 prefixEnd_7615383 3910351847078483512689997 := by
  unfold tailWord_7615383
  simp only [CollatzResearch.WordTrace]
  refine ⟨277755836569775469715146803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185170557713183646476764535 277755836569775469715146803)
  ·
    refine ⟨416633754854663204572720205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277755836569775469715146803 416633754854663204572720205)
    ·
      refine ⟨156237658070498701714770077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416633754854663204572720205 156237658070498701714770077)
      ·
        refine ⟨58589121776437013143038779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156237658070498701714770077 58589121776437013143038779)
        ·
          refine ⟨87883682664655519714558169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58589121776437013143038779 87883682664655519714558169)
          ·
            refine ⟨65912761998491639785918627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87883682664655519714558169 65912761998491639785918627)
            ·
              refine ⟨98869142997737459678877941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65912761998491639785918627 98869142997737459678877941)
              ·
                refine ⟨9268982156037886844894807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98869142997737459678877941 9268982156037886844894807)
                ·
                  refine ⟨13903473234056830267342211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9268982156037886844894807 13903473234056830267342211)
                  ·
                    refine ⟨20855209851085245401013317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13903473234056830267342211 20855209851085245401013317)
                    ·
                      refine ⟨3910351847078483512689997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20855209851085245401013317 3910351847078483512689997)
                      ·
                        rfl

theorem cell23_7615383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_7615383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615383 prefixEnd_7615383 := by exact prefixLift 7615383
  have htrace : WordTrace (prefixWord ++ tailWord_7615383) baseStart_7615383 baseEnd_7615383 := by
    simpa [prefixWord, tailWord_7615383, baseEnd_7615383] using wordTrace_append hprefix tailTrace_7615383
  have hstable : (prefixWord ++ tailWord_7615383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615383).length < 2 ^ (prefixWord ++ tailWord_7615383).sum := by decide
  have hdescent : baseEnd_7615383 < baseStart_7615383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615396 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_7615396 : Nat := 118140960795 + 7615396 * 2 ^ 59
def prefixEnd_7615396 : Nat := 4983230072969 + 3 ^ 40 * 7615396 * 2
def baseEnd_7615396 : Nat := 3910358522326991961827437

theorem tailTrace_7615396 : CollatzResearch.WordTrace tailWord_7615396 prefixEnd_7615396 3910358522326991961827437 := by
  unfold tailWord_7615396
  simp only [CollatzResearch.WordTrace]
  refine ⟨138878155359364186467685021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185170873812485581956913361 138878155359364186467685021)
  ·
    refine ⟨52079308259761569925381883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138878155359364186467685021 52079308259761569925381883)
    ·
      refine ⟨78118962389642354888072825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52079308259761569925381883 78118962389642354888072825)
      ·
        refine ⟨58589221792231766166054619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78118962389642354888072825 58589221792231766166054619)
        ·
          refine ⟨87883832688347649249081929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58589221792231766166054619 87883832688347649249081929)
          ·
            refine ⟨65912874516260736936811447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87883832688347649249081929 65912874516260736936811447)
            ·
              refine ⟨98869311774391105405217171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65912874516260736936811447 98869311774391105405217171)
              ·
                refine ⟨148303967661586658107825757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98869311774391105405217171 148303967661586658107825757)
                ·
                  refine ⟨55613987873094996790434659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148303967661586658107825757 55613987873094996790434659)
                  ·
                    refine ⟨83420981809642495185651989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55613987873094996790434659 83420981809642495185651989)
                    ·
                      refine ⟨3910358522326991961827437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83420981809642495185651989 3910358522326991961827437)
                      ·
                        rfl

theorem cell23_7615396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_7615396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615396 prefixEnd_7615396 := by exact prefixLift 7615396
  have htrace : WordTrace (prefixWord ++ tailWord_7615396) baseStart_7615396 baseEnd_7615396 := by
    simpa [prefixWord, tailWord_7615396, baseEnd_7615396] using wordTrace_append hprefix tailTrace_7615396
  have hstable : (prefixWord ++ tailWord_7615396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615396).length < 2 ^ (prefixWord ++ tailWord_7615396).sum := by decide
  have hdescent : baseEnd_7615396 < baseStart_7615396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615413 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7615413 : Nat := 118140960795 + 7615413 * 2 ^ 59
def prefixEnd_7615413 : Nat := 4983230072969 + 3 ^ 40 * 7615413 * 2
def baseEnd_7615413 : Nat := 3910367251498118395314859

theorem tailTrace_7615413 : CollatzResearch.WordTrace tailWord_7615413 prefixEnd_7615413 3910367251498118395314859 := by
  unfold tailWord_7615413
  simp only [CollatzResearch.WordTrace]
  refine ⟨277756930759666784838738893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185171287173111189892492595 277756930759666784838738893)
  ·
    refine ⟨104158849034875044314527085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277756930759666784838738893 104158849034875044314527085)
    ·
      refine ⟨39059568388078141617947657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104158849034875044314527085 39059568388078141617947657)
      ·
        refine ⟨29294676291058606213460743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39059568388078141617947657 29294676291058606213460743)
        ·
          refine ⟨43942014436587909320191115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29294676291058606213460743 43942014436587909320191115)
          ·
            refine ⟨65913021654881863980286673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43942014436587909320191115 65913021654881863980286673)
            ·
              refine ⟨49434766241161397985215005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65913021654881863980286673 49434766241161397985215005)
              ·
                refine ⟨18538037340435524244455627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49434766241161397985215005 18538037340435524244455627)
                ·
                  refine ⟨27807056010653286366683441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18538037340435524244455627 27807056010653286366683441)
                  ·
                    refine ⟨20855292007989964775012581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27807056010653286366683441 20855292007989964775012581)
                    ·
                      refine ⟨3910367251498118395314859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20855292007989964775012581 3910367251498118395314859)
                      ·
                        rfl

theorem cell23_7615413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7615413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615413 prefixEnd_7615413 := by exact prefixLift 7615413
  have htrace : WordTrace (prefixWord ++ tailWord_7615413) baseStart_7615413 baseEnd_7615413 := by
    simpa [prefixWord, tailWord_7615413, baseEnd_7615413] using wordTrace_append hprefix tailTrace_7615413
  have hstable : (prefixWord ++ tailWord_7615413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615413).length < 2 ^ (prefixWord ++ tailWord_7615413).sum := by decide
  have hdescent : baseEnd_7615413 < baseStart_7615413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615414 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7615414 : Nat := 118140960795 + 7615414 * 2 ^ 59
def prefixEnd_7615414 : Nat := 4983230072969 + 3 ^ 40 * 7615414 * 2
def baseEnd_7615414 : Nat := 1303455921659590963800785

theorem tailTrace_7615414 : CollatzResearch.WordTrace tailWord_7615414 prefixEnd_7615414 1303455921659590963800785 := by
  unfold tailWord_7615414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359810452041447625595331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185171311488442108006350197 17359810452041447625595331)
  ·
    refine ⟨26039715678062171438392997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17359810452041447625595331 26039715678062171438392997)
    ·
      refine ⟨4882446689636657144698687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26039715678062171438392997 4882446689636657144698687)
      ·
        refine ⟨7323670034454985717048031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882446689636657144698687 7323670034454985717048031)
        ·
          refine ⟨10985505051682478575572047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323670034454985717048031 10985505051682478575572047)
          ·
            refine ⟨16478257577523717863358071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985505051682478575572047 16478257577523717863358071)
            ·
              refine ⟨24717386366285576795037107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16478257577523717863358071 24717386366285576795037107)
              ·
                refine ⟨37076079549428365192555661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24717386366285576795037107 37076079549428365192555661)
                ·
                  refine ⟨13903529831035636947208373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37076079549428365192555661 13903529831035636947208373)
                  ·
                    refine ⟨1303455921659590963800785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903529831035636947208373 1303455921659590963800785)
                    ·
                      rfl

theorem cell23_7615414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7615414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615414 prefixEnd_7615414 := by exact prefixLift 7615414
  have htrace : WordTrace (prefixWord ++ tailWord_7615414) baseStart_7615414 baseEnd_7615414 := by
    simpa [prefixWord, tailWord_7615414, baseEnd_7615414] using wordTrace_append hprefix tailTrace_7615414
  have hstable : (prefixWord ++ tailWord_7615414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615414).length < 2 ^ (prefixWord ++ tailWord_7615414).sum := by decide
  have hdescent : baseEnd_7615414 < baseStart_7615414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615453 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7615453 : Nat := 118140960795 + 7615453 * 2 ^ 59
def prefixEnd_7615453 : Nat := 4983230072969 + 3 ^ 40 * 7615453 * 2
def baseEnd_7615453 : Nat := 1303462596908099412938225

theorem tailTrace_7615453 : CollatzResearch.WordTrace tailWord_7615453 prefixEnd_7615453 1303462596908099412938225 := by
  unfold tailWord_7615453
  simp only [CollatzResearch.WordTrace]
  refine ⟨277758389679521871670195013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185172259786347914446796675 277758389679521871670195013)
  ·
    refine ⟨52079698064910350938161565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277758389679521871670195013 52079698064910350938161565)
    ·
      refine ⟨19529886774341381601810587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52079698064910350938161565 19529886774341381601810587)
      ·
        refine ⟨29294830161512072402715881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19529886774341381601810587 29294830161512072402715881)
        ·
          refine ⟨21971122621134054302036911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29294830161512072402715881 21971122621134054302036911)
          ·
            refine ⟨32956683931701081453055367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21971122621134054302036911 32956683931701081453055367)
            ·
              refine ⟨49435025897551622179583051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32956683931701081453055367 49435025897551622179583051)
              ·
                refine ⟨74152538846327433269374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49435025897551622179583051 74152538846327433269374577)
                ·
                  refine ⟨55614404134745574952030933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74152538846327433269374577 55614404134745574952030933)
                  ·
                    refine ⟨1303462596908099412938225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55614404134745574952030933 1303462596908099412938225)
                    ·
                      rfl

theorem cell23_7615453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7615453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615453 prefixEnd_7615453 := by exact prefixLift 7615453
  have htrace : WordTrace (prefixWord ++ tailWord_7615453) baseStart_7615453 baseEnd_7615453 := by
    simpa [prefixWord, tailWord_7615453, baseEnd_7615453] using wordTrace_append hprefix tailTrace_7615453
  have hstable : (prefixWord ++ tailWord_7615453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615453).length < 2 ^ (prefixWord ++ tailWord_7615453).sum := by decide
  have hdescent : baseEnd_7615453 < baseStart_7615453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615524 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7615524 : Nat := 118140960795 + 7615524 * 2 ^ 59
def prefixEnd_7615524 : Nat := 4983230072969 + 3 ^ 40 * 7615524 * 2
def baseEnd_7615524 : Nat := 3910424247850767461026849

theorem tailTrace_7615524 : CollatzResearch.WordTrace tailWord_7615524 prefixEnd_7615524 3910424247850767461026849 := by
  unfold tailWord_7615524
  simp only [CollatzResearch.WordTrace]
  refine ⟨138880489631132325398014813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185173986174843100530686417 138880489631132325398014813)
  ·
    refine ⟨52080183611674622024255555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138880489631132325398014813 52080183611674622024255555)
    ·
      refine ⟨78120275417511933036383333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52080183611674622024255555 78120275417511933036383333)
      ·
        refine ⟨14647551640783487444321875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78120275417511933036383333 14647551640783487444321875)
        ·
          refine ⟨21971327461175231166482813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647551640783487444321875 21971327461175231166482813)
          ·
            refine ⟨8239247797940711687431055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21971327461175231166482813 8239247797940711687431055)
            ·
              refine ⟨12358871696911067531146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239247797940711687431055 12358871696911067531146583)
              ·
                refine ⟨18538307545366601296719875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358871696911067531146583 18538307545366601296719875)
                ·
                  refine ⟨27807461318049901945079813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18538307545366601296719875 27807461318049901945079813)
                  ·
                    refine ⟨5213898997134356614702465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27807461318049901945079813 5213898997134356614702465)
                    ·
                      refine ⟨3910424247850767461026849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5213898997134356614702465 3910424247850767461026849)
                      ·
                        rfl

theorem cell23_7615524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7615524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615524 prefixEnd_7615524 := by exact prefixLift 7615524
  have htrace : WordTrace (prefixWord ++ tailWord_7615524) baseStart_7615524 baseEnd_7615524 := by
    simpa [prefixWord, tailWord_7615524, baseEnd_7615524] using wordTrace_append hprefix tailTrace_7615524
  have hstable : (prefixWord ++ tailWord_7615524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615524).length < 2 ^ (prefixWord ++ tailWord_7615524).sum := by decide
  have hdescent : baseEnd_7615524 < baseStart_7615524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615543 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 2, 5]
def baseStart_7615543 : Nat := 118140960795 + 7615543 * 2 ^ 59
def prefixEnd_7615543 : Nat := 4983230072969 + 3 ^ 40 * 7615543 * 2
def baseEnd_7615543 : Nat := 1303478001327734295563087

theorem tailTrace_7615543 : CollatzResearch.WordTrace tailWord_7615543 prefixEnd_7615543 1303478001327734295563087 := by
  unfold tailWord_7615543
  simp only [CollatzResearch.WordTrace]
  refine ⟨277761672249195817040971283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185174448166130544693980855 277761672249195817040971283)
  ·
    refine ⟨416642508373793725561456925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277761672249195817040971283 416642508373793725561456925)
    ·
      refine ⟨156240940640172647085546347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416642508373793725561456925 156240940640172647085546347)
      ·
        refine ⟨234361410960258970628319521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156240940640172647085546347 234361410960258970628319521)
        ·
          refine ⟨175771058220194227971239641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234361410960258970628319521 175771058220194227971239641)
          ·
            refine ⟨131828293665145670978429731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175771058220194227971239641 131828293665145670978429731)
            ·
              refine ⟨197742440497718506467644597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131828293665145670978429731 197742440497718506467644597)
              ·
                refine ⟨18538353796661109981341681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197742440497718506467644597 18538353796661109981341681)
                ·
                  refine ⟨13903765347495832486006261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18538353796661109981341681 13903765347495832486006261)
                  ·
                    refine ⟨1303478001327734295563087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903765347495832486006261 1303478001327734295563087)
                    ·
                      rfl

theorem cell23_7615543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_7615543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615543 prefixEnd_7615543 := by exact prefixLift 7615543
  have htrace : WordTrace (prefixWord ++ tailWord_7615543) baseStart_7615543 baseEnd_7615543 := by
    simpa [prefixWord, tailWord_7615543, baseEnd_7615543] using wordTrace_append hprefix tailTrace_7615543
  have hstable : (prefixWord ++ tailWord_7615543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615543).length < 2 ^ (prefixWord ++ tailWord_7615543).sum := by decide
  have hdescent : baseEnd_7615543 < baseStart_7615543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615570 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7615570 : Nat := 118140960795 + 7615570 * 2 ^ 59
def prefixEnd_7615570 : Nat := 4983230072969 + 3 ^ 40 * 7615570 * 2
def baseEnd_7615570 : Nat := 3910447867960874281051637

theorem tailTrace_7615570 : CollatzResearch.WordTrace tailWord_7615570 prefixEnd_7615570 3910447867960874281051637 := by
  unfold tailWord_7615570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69440664255024500163051041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185175104680065333768136109 69440664255024500163051041)
  ·
    refine ⟨52080498191268375122288281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69440664255024500163051041 52080498191268375122288281)
    ·
      refine ⟨39060373643451281341716211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52080498191268375122288281 39060373643451281341716211)
      ·
        refine ⟨58590560465176922012574317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060373643451281341716211 58590560465176922012574317)
        ·
          refine ⟨21971460174441345754715369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58590560465176922012574317 21971460174441345754715369)
          ·
            refine ⟨16478595130831009316036527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21971460174441345754715369 16478595130831009316036527)
            ·
              refine ⟨24717892696246513974054791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16478595130831009316036527 24717892696246513974054791)
              ·
                refine ⟨37076839044369770961082187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24717892696246513974054791 37076839044369770961082187)
                ·
                  refine ⟨55615258566554656441623281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37076839044369770961082187 55615258566554656441623281)
                  ·
                    refine ⟨41711443924915992331217461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55615258566554656441623281 41711443924915992331217461)
                    ·
                      refine ⟨3910447867960874281051637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41711443924915992331217461 3910447867960874281051637)
                      ·
                        rfl

theorem cell23_7615570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7615570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615570 prefixEnd_7615570 := by exact prefixLift 7615570
  have htrace : WordTrace (prefixWord ++ tailWord_7615570) baseStart_7615570 baseEnd_7615570 := by
    simpa [prefixWord, tailWord_7615570, baseEnd_7615570] using wordTrace_append hprefix tailTrace_7615570
  have hstable : (prefixWord ++ tailWord_7615570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615570).length < 2 ^ (prefixWord ++ tailWord_7615570).sum := by decide
  have hdescent : baseEnd_7615570 < baseStart_7615570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615580 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7615580 : Nat := 118140960795 + 7615580 * 2 ^ 59
def prefixEnd_7615580 : Nat := 4983230072969 + 3 ^ 40 * 7615580 * 2
def baseEnd_7615580 : Nat := 3910453002767419241926591

theorem tailTrace_7615580 : CollatzResearch.WordTrace tailWord_7615580 prefixEnd_7615580 3910453002767419241926591 := by
  unfold tailWord_7615580
  simp only [CollatzResearch.WordTrace]
  refine ⟨138881510875030886180034097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185175347833374514906712129 138881510875030886180034097)
  ·
    refine ⟨104161133156273164635025573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138881510875030886180034097 104161133156273164635025573)
    ·
      refine ⟨19530212466801218369067295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104161133156273164635025573 19530212466801218369067295)
      ·
        refine ⟨29295318700201827553600943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19530212466801218369067295 29295318700201827553600943)
        ·
          refine ⟨43942978050302741330401415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29295318700201827553600943 43942978050302741330401415)
          ·
            refine ⟨65914467075454111995602123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43942978050302741330401415 65914467075454111995602123)
            ·
              refine ⟨98871700613181167993403185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65914467075454111995602123 98871700613181167993403185)
              ·
                refine ⟨74153775459885875995052389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98871700613181167993403185 74153775459885875995052389)
                ·
                  refine ⟨13903832898728601749072323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74153775459885875995052389 13903832898728601749072323)
                  ·
                    refine ⟨20855749348092902623608485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13903832898728601749072323 20855749348092902623608485)
                    ·
                      refine ⟨3910453002767419241926591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20855749348092902623608485 3910453002767419241926591)
                      ·
                        rfl

theorem cell23_7615580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7615580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615580 prefixEnd_7615580 := by exact prefixLift 7615580
  have htrace : WordTrace (prefixWord ++ tailWord_7615580) baseStart_7615580 baseEnd_7615580 := by
    simpa [prefixWord, tailWord_7615580, baseEnd_7615580] using wordTrace_append hprefix tailTrace_7615580
  have hstable : (prefixWord ++ tailWord_7615580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615580).length < 2 ^ (prefixWord ++ tailWord_7615580).sum := by decide
  have hdescent : baseEnd_7615580 < baseStart_7615580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615597 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7615597 : Nat := 118140960795 + 7615597 * 2 ^ 59
def prefixEnd_7615597 : Nat := 4983230072969 + 3 ^ 40 * 7615597 * 2
def baseEnd_7615597 : Nat := 3910461731938545675414013

theorem tailTrace_7615597 : CollatzResearch.WordTrace tailWord_7615597 prefixEnd_7615597 3910461731938545675414013 := by
  unfold tailWord_7615597
  simp only [CollatzResearch.WordTrace]
  refine ⟨277763641791000184263437045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185175761194000122842291363 277763641791000184263437045)
  ·
    refine ⟨26040341417906267274697223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277763641791000184263437045 26040341417906267274697223)
    ·
      refine ⟨39060512126859400912045835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26040341417906267274697223 39060512126859400912045835)
      ·
        refine ⟨58590768190289101368068753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060512126859400912045835 58590768190289101368068753)
        ·
          refine ⟨43943076142716826026051565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58590768190289101368068753 43943076142716826026051565)
          ·
            refine ⟨16478653553518809759769337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43943076142716826026051565 16478653553518809759769337)
            ·
              refine ⟨12358990165139107319827003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16478653553518809759769337 12358990165139107319827003)
              ·
                refine ⟨18538485247708660979740505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358990165139107319827003 18538485247708660979740505)
                ·
                  refine ⟨13903863935781495734805379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18538485247708660979740505 13903863935781495734805379)
                  ·
                    refine ⟨20855795903672243602208069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13903863935781495734805379 20855795903672243602208069)
                    ·
                      refine ⟨3910461731938545675414013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20855795903672243602208069 3910461731938545675414013)
                      ·
                        rfl

theorem cell23_7615597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7615597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615597 prefixEnd_7615597 := by exact prefixLift 7615597
  have htrace : WordTrace (prefixWord ++ tailWord_7615597) baseStart_7615597 baseEnd_7615597 := by
    simpa [prefixWord, tailWord_7615597, baseEnd_7615597] using wordTrace_append hprefix tailTrace_7615597
  have hstable : (prefixWord ++ tailWord_7615597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615597).length < 2 ^ (prefixWord ++ tailWord_7615597).sum := by decide
  have hdescent : baseEnd_7615597 < baseStart_7615597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615607 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 1, 4]
def baseStart_7615607 : Nat := 118140960795 + 7615607 * 2 ^ 59
def prefixEnd_7615607 : Nat := 4983230072969 + 3 ^ 40 * 7615607 * 2
def baseEnd_7615607 : Nat := 1303488955581696878762989

theorem tailTrace_7615607 : CollatzResearch.WordTrace tailWord_7615607 prefixEnd_7615607 1303488955581696878762989 := by
  unfold tailWord_7615607
  simp only [CollatzResearch.WordTrace]
  refine ⟨277764006520963955971301075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185176004347309303980867383 277764006520963955971301075)
  ·
    refine ⟨416646009781445933956951613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277764006520963955971301075 416646009781445933956951613)
    ·
      refine ⟨156242253668042225233856855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416646009781445933956951613 156242253668042225233856855)
      ·
        refine ⟨234363380502063337850785283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156242253668042225233856855 234363380502063337850785283)
        ·
          refine ⟨351545070753095006776177925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234363380502063337850785283 351545070753095006776177925)
          ·
            refine ⟨65914700766205313770533361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351545070753095006776177925 65914700766205313770533361)
            ·
              refine ⟨49436025574653985327900021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65914700766205313770533361 49436025574653985327900021)
              ·
                refine ⟨4634627397623811124490627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49436025574653985327900021 4634627397623811124490627)
                ·
                  refine ⟨6951941096435716686735941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634627397623811124490627 6951941096435716686735941)
                  ·
                    refine ⟨1303488955581696878762989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951941096435716686735941 1303488955581696878762989)
                    ·
                      rfl

theorem cell23_7615607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_7615607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615607 prefixEnd_7615607 := by exact prefixLift 7615607
  have htrace : WordTrace (prefixWord ++ tailWord_7615607) baseStart_7615607 baseEnd_7615607 := by
    simpa [prefixWord, tailWord_7615607, baseEnd_7615607] using wordTrace_append hprefix tailTrace_7615607
  have hstable : (prefixWord ++ tailWord_7615607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615607).length < 2 ^ (prefixWord ++ tailWord_7615607).sum := by decide
  have hdescent : baseEnd_7615607 < baseStart_7615607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615617 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_7615617 : Nat := 118140960795 + 7615617 * 2 ^ 59
def prefixEnd_7615617 : Nat := 4983230072969 + 3 ^ 40 * 7615617 * 2
def baseEnd_7615617 : Nat := 3910472001551635597163921

theorem tailTrace_7615617 : CollatzResearch.WordTrace tailWord_7615617 prefixEnd_7615617 3910472001551635597163921 := by
  unfold tailWord_7615617
  simp only [CollatzResearch.WordTrace]
  refine ⟨277764371250927727679165105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185176247500618485119443403 277764371250927727679165105)
  ·
    refine ⟨208323278438195795759373829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277764371250927727679165105 208323278438195795759373829)
    ·
      refine ⟨39060614707161711704882593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208323278438195795759373829 39060614707161711704882593)
      ·
        refine ⟨29295461030371283778661945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39060614707161711704882593 29295461030371283778661945)
        ·
          refine ⟨21971595772778462833996459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29295461030371283778661945 21971595772778462833996459)
          ·
            refine ⟨32957393659167694250994689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21971595772778462833996459 32957393659167694250994689)
            ·
              refine ⟨24718045244375770688246017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32957393659167694250994689 24718045244375770688246017)
              ·
                refine ⟨18538533933281828016184513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24718045244375770688246017 18538533933281828016184513)
                ·
                  refine ⟨13903900449961371012138385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18538533933281828016184513 13903900449961371012138385)
                  ·
                    refine ⟨10427925337471028259103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13903900449961371012138385 10427925337471028259103789)
                    ·
                      refine ⟨3910472001551635597163921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10427925337471028259103789 3910472001551635597163921)
                      ·
                        rfl

theorem cell23_7615617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_7615617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615617 prefixEnd_7615617 := by exact prefixLift 7615617
  have htrace : WordTrace (prefixWord ++ tailWord_7615617) baseStart_7615617 baseEnd_7615617 := by
    simpa [prefixWord, tailWord_7615617, baseEnd_7615617] using wordTrace_append hprefix tailTrace_7615617
  have hstable : (prefixWord ++ tailWord_7615617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615617).length < 2 ^ (prefixWord ++ tailWord_7615617).sum := by decide
  have hdescent : baseEnd_7615617 < baseStart_7615617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615620 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 6]
def baseStart_7615620 : Nat := 118140960795 + 7615620 * 2 ^ 59
def prefixEnd_7615620 : Nat := 4983230072969 + 3 ^ 40 * 7615620 * 2
def baseEnd_7615620 : Nat := 434497060221511009491823

theorem tailTrace_7615620 : CollatzResearch.WordTrace tailWord_7615620 prefixEnd_7615620 434497060221511009491823 := by
  unfold tailWord_7615620
  simp only [CollatzResearch.WordTrace]
  refine ⟨138882240334958429595762157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185176320446611239461016209 138882240334958429595762157)
  ·
    refine ⟨52080840125609411098410809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138882240334958429595762157 52080840125609411098410809)
    ·
      refine ⟨39060630094207058323808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52080840125609411098410809 39060630094207058323808107)
      ·
        refine ⟨58590945141310587485712161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060630094207058323808107 58590945141310587485712161)
        ·
          refine ⟨43943208855982940614284121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58590945141310587485712161 43943208855982940614284121)
          ·
            refine ⟨32957406641987205460713091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43943208855982940614284121 32957406641987205460713091)
            ·
              refine ⟨49436109962980808191069637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32957406641987205460713091 49436109962980808191069637)
              ·
                refine ⟨9269270618058901535825557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49436109962980808191069637 9269270618058901535825557)
                ·
                  refine ⟨434497060221511009491823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9269270618058901535825557 434497060221511009491823)
                  ·
                    rfl

theorem cell23_7615620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_7615620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615620 prefixEnd_7615620 := by exact prefixLift 7615620
  have htrace : WordTrace (prefixWord ++ tailWord_7615620) baseStart_7615620 baseEnd_7615620 := by
    simpa [prefixWord, tailWord_7615620, baseEnd_7615620] using wordTrace_append hprefix tailTrace_7615620
  have hstable : (prefixWord ++ tailWord_7615620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615620).length < 2 ^ (prefixWord ++ tailWord_7615620).sum := by decide
  have hdescent : baseEnd_7615620 < baseStart_7615620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615623 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_7615623 : Nat := 118140960795 + 7615623 * 2 ^ 59
def prefixEnd_7615623 : Nat := 4983230072969 + 3 ^ 40 * 7615623 * 2
def baseEnd_7615623 : Nat := 3910475082435562573688893

theorem tailTrace_7615623 : CollatzResearch.WordTrace tailWord_7615623 prefixEnd_7615623 3910475082435562573688893 := by
  unfold tailWord_7615623
  simp only [CollatzResearch.WordTrace]
  refine ⟨277764590088905990703883523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185176393392603993802589015 277764590088905990703883523)
  ·
    refine ⟨416646885133358986055825285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277764590088905990703883523 416646885133358986055825285)
    ·
      refine ⟨78121290962504809885467241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416646885133358986055825285 78121290962504809885467241)
      ·
        refine ⟨58590968221878607414100431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78121290962504809885467241 58590968221878607414100431)
        ·
          refine ⟨87886452332817911121150647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58590968221878607414100431 87886452332817911121150647)
          ·
            refine ⟨131829678499226866681725971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87886452332817911121150647 131829678499226866681725971)
            ·
              refine ⟨197744517748840300022588957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131829678499226866681725971 197744517748840300022588957)
              ·
                refine ⟨74154194155815112508470859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197744517748840300022588957 74154194155815112508470859)
                ·
                  refine ⟨111231291233722668762706289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74154194155815112508470859 111231291233722668762706289)
                  ·
                    refine ⟨83423468425292001572029717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111231291233722668762706289 83423468425292001572029717)
                    ·
                      refine ⟨3910475082435562573688893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83423468425292001572029717 3910475082435562573688893)
                      ·
                        rfl

theorem cell23_7615623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_7615623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615623 prefixEnd_7615623 := by exact prefixLift 7615623
  have htrace : WordTrace (prefixWord ++ tailWord_7615623) baseStart_7615623 baseEnd_7615623 := by
    simpa [prefixWord, tailWord_7615623, baseEnd_7615623] using wordTrace_append hprefix tailTrace_7615623
  have hstable : (prefixWord ++ tailWord_7615623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615623).length < 2 ^ (prefixWord ++ tailWord_7615623).sum := by decide
  have hdescent : baseEnd_7615623 < baseStart_7615623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615667 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 1, 5]
def baseStart_7615667 : Nat := 118140960795 + 7615667 * 2 ^ 59
def prefixEnd_7615667 : Nat := 4983230072969 + 3 ^ 40 * 7615667 * 2
def baseEnd_7615667 : Nat := 1303499225194786800512897

theorem tailTrace_7615667 : CollatzResearch.WordTrace tailWord_7615667 prefixEnd_7615667 1303499225194786800512897 := by
  unfold tailWord_7615667
  simp only [CollatzResearch.WordTrace]
  refine ⟨277766194900746586218485255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185177463267164390812323503 277766194900746586218485255)
  ·
    refine ⟨416649292351119879327727883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277766194900746586218485255 416649292351119879327727883)
    ·
      refine ⟨624973938526679818991591825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416649292351119879327727883 624973938526679818991591825)
      ·
        refine ⟨468730453895009864243693869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624973938526679818991591825 468730453895009864243693869)
        ·
          refine ⟨175773920210628699091385201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468730453895009864243693869 175773920210628699091385201)
          ·
            refine ⟨131830440157971524318538901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175773920210628699091385201 131830440157971524318538901)
            ·
              refine ⟨6179551882404915202431511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131830440157971524318538901 6179551882404915202431511)
              ·
                refine ⟨9269327823607372803647267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179551882404915202431511 9269327823607372803647267)
                ·
                  refine ⟨13903991735411059205470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9269327823607372803647267 13903991735411059205470901)
                  ·
                    refine ⟨1303499225194786800512897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903991735411059205470901 1303499225194786800512897)
                    ·
                      rfl

theorem cell23_7615667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 5].length) (baseStart_7615667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615667 prefixEnd_7615667 := by exact prefixLift 7615667
  have htrace : WordTrace (prefixWord ++ tailWord_7615667) baseStart_7615667 baseEnd_7615667 := by
    simpa [prefixWord, tailWord_7615667, baseEnd_7615667] using wordTrace_append hprefix tailTrace_7615667
  have hstable : (prefixWord ++ tailWord_7615667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615667).length < 2 ^ (prefixWord ++ tailWord_7615667).sum := by decide
  have hdescent : baseEnd_7615667 < baseStart_7615667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615681 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7615681 : Nat := 118140960795 + 7615681 * 2 ^ 59
def prefixEnd_7615681 : Nat := 4983230072969 + 3 ^ 40 * 7615681 * 2
def baseEnd_7615681 : Nat := 3910504864313523346763627

theorem tailTrace_7615681 : CollatzResearch.WordTrace tailWord_7615681 prefixEnd_7615681 3910504864313523346763627 := by
  unfold tailWord_7615681
  simp only [CollatzResearch.WordTrace]
  refine ⟨277766705522695866609494897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185177803681797244406329931 277766705522695866609494897)
  ·
    refine ⟨208325029142021899957121173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277766705522695866609494897 208325029142021899957121173)
    ·
      refine ⟨9765235741032276560490055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208325029142021899957121173 9765235741032276560490055)
      ·
        refine ⟨14647853611548414840735083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9765235741032276560490055 14647853611548414840735083)
        ·
          refine ⟨21971780417322622261102625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647853611548414840735083 21971780417322622261102625)
          ·
            refine ⟨16478835312991966695826969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21971780417322622261102625 16478835312991966695826969)
            ·
              refine ⟨12359126484743975021870227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16478835312991966695826969 12359126484743975021870227)
              ·
                refine ⟨18538689727115962532805341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359126484743975021870227 18538689727115962532805341)
                ·
                  refine ⟨6952008647668485949802003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18538689727115962532805341 6952008647668485949802003)
                  ·
                    refine ⟨10428012971502728924703005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952008647668485949802003 10428012971502728924703005)
                    ·
                      refine ⟨3910504864313523346763627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428012971502728924703005 3910504864313523346763627)
                      ·
                        rfl

theorem cell23_7615681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7615681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615681 prefixEnd_7615681 := by exact prefixLift 7615681
  have htrace : WordTrace (prefixWord ++ tailWord_7615681) baseStart_7615681 baseEnd_7615681 := by
    simpa [prefixWord, tailWord_7615681, baseEnd_7615681] using wordTrace_append hprefix tailTrace_7615681
  have hstable : (prefixWord ++ tailWord_7615681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615681).length < 2 ^ (prefixWord ++ tailWord_7615681).sum := by decide
  have hdescent : baseEnd_7615681 < baseStart_7615681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615690 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_7615690 : Nat := 118140960795 + 7615690 * 2 ^ 59
def prefixEnd_7615690 : Nat := 4983230072969 + 3 ^ 40 * 7615690 * 2
def baseEnd_7615690 : Nat := 3910509485639413811551085

theorem tailTrace_7615690 : CollatzResearch.WordTrace tailWord_7615690 prefixEnd_7615690 3910509485639413811551085 := by
  unfold tailWord_7615690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69441758444915815286643131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185178022519775507431048349 69441758444915815286643131)
  ·
    refine ⟨104162637667373722929964697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69441758444915815286643131 104162637667373722929964697)
    ·
      refine ⟨78121978250530292197473523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104162637667373722929964697 78121978250530292197473523)
      ·
        refine ⟨117182967375795438296210285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78121978250530292197473523 117182967375795438296210285)
        ·
          refine ⟨43943612765923289361078857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117182967375795438296210285 43943612765923289361078857)
          ·
            refine ⟨32957709574442467020809143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43943612765923289361078857 32957709574442467020809143)
            ·
              refine ⟨49436564361663700531213715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32957709574442467020809143 49436564361663700531213715)
              ·
                refine ⟨74154846542495550796820573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49436564361663700531213715 74154846542495550796820573)
                ·
                  refine ⟨27808067453435831548807715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74154846542495550796820573 27808067453435831548807715)
                  ·
                    refine ⟨41712101180153747323211573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27808067453435831548807715 41712101180153747323211573)
                    ·
                      refine ⟨3910509485639413811551085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41712101180153747323211573 3910509485639413811551085)
                      ·
                        rfl

theorem cell23_7615690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_7615690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615690 prefixEnd_7615690 := by exact prefixLift 7615690
  have htrace : WordTrace (prefixWord ++ tailWord_7615690) baseStart_7615690 baseEnd_7615690 := by
    simpa [prefixWord, tailWord_7615690, baseEnd_7615690] using wordTrace_append hprefix tailTrace_7615690
  have hstable : (prefixWord ++ tailWord_7615690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615690).length < 2 ^ (prefixWord ++ tailWord_7615690).sum := by decide
  have hdescent : baseEnd_7615690 < baseStart_7615690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615704 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_7615704 : Nat := 118140960795 + 7615704 * 2 ^ 59
def prefixEnd_7615704 : Nat := 4983230072969 + 3 ^ 40 * 7615704 * 2
def baseEnd_7615704 : Nat := 3910516674368576756776021

theorem tailTrace_7615704 : CollatzResearch.WordTrace tailWord_7615704 prefixEnd_7615704 3910516674368576756776021 := by
  unfold tailWord_7615704
  simp only [CollatzResearch.WordTrace]
  refine ⟨138883772200806270768791083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185178362934408361025054777 138883772200806270768791083)
  ·
    refine ⟨208325658301209406153186625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138883772200806270768791083 208325658301209406153186625)
    ·
      refine ⟨156244243725907054614889969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208325658301209406153186625 156244243725907054614889969)
      ·
        refine ⟨117183182794430290961167477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156244243725907054614889969 117183182794430290961167477)
        ·
          refine ⟨10985923386977839777609451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117183182794430290961167477 10985923386977839777609451)
          ·
            refine ⟨16478885080466759666414177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985923386977839777609451 16478885080466759666414177)
            ·
              refine ⟨12359163810350069749810633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16478885080466759666414177 12359163810350069749810633)
              ·
                refine ⟨9269372857762552312357975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12359163810350069749810633 9269372857762552312357975)
                ·
                  refine ⟨13904059286643828468536963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9269372857762552312357975 13904059286643828468536963)
                  ·
                    refine ⟨20856088929965742702805445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13904059286643828468536963 20856088929965742702805445)
                    ·
                      refine ⟨3910516674368576756776021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20856088929965742702805445 3910516674368576756776021)
                      ·
                        rfl

theorem cell23_7615704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_7615704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615704 prefixEnd_7615704 := by exact prefixLift 7615704
  have htrace : WordTrace (prefixWord ++ tailWord_7615704) baseStart_7615704 baseEnd_7615704 := by
    simpa [prefixWord, tailWord_7615704, baseEnd_7615704] using wordTrace_append hprefix tailTrace_7615704
  have hstable : (prefixWord ++ tailWord_7615704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615704).length < 2 ^ (prefixWord ++ tailWord_7615704).sum := by decide
  have hdescent : baseEnd_7615704 < baseStart_7615704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615727 : List Nat := [1, 1, 2, 1, 8, 1, 9]
def baseStart_7615727 : Nat := 118140960795 + 7615727 * 2 ^ 59
def prefixEnd_7615727 : Nat := 4983230072969 + 3 ^ 40 * 7615727 * 2
def baseEnd_7615727 : Nat := 48278129437328767491215

theorem tailTrace_7615727 : CollatzResearch.WordTrace tailWord_7615727 prefixEnd_7615727 48278129437328767491215 := by
  unfold tailWord_7615727
  simp only [CollatzResearch.WordTrace]
  refine ⟨277768383280529216465669435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185178922187019477643779623 277768383280529216465669435)
  ·
    refine ⟨416652574920793824698504153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277768383280529216465669435 416652574920793824698504153)
    ·
      refine ⟨312489431190595368523878115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416652574920793824698504153 312489431190595368523878115)
      ·
        refine ⟨468734146785893052785817173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312489431190595368523878115 468734146785893052785817173)
        ·
          refine ⟨5492978282647184212333795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 468734146785893052785817173 5492978282647184212333795)
          ·
            refine ⟨8239467423970776318500693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492978282647184212333795 8239467423970776318500693)
            ·
              refine ⟨48278129437328767491215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8239467423970776318500693 48278129437328767491215)
              ·
                rfl

theorem cell23_7615727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 9].length) (baseStart_7615727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615727 prefixEnd_7615727 := by exact prefixLift 7615727
  have htrace : WordTrace (prefixWord ++ tailWord_7615727) baseStart_7615727 baseEnd_7615727 := by
    simpa [prefixWord, tailWord_7615727, baseEnd_7615727] using wordTrace_append hprefix tailTrace_7615727
  have hstable : (prefixWord ++ tailWord_7615727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615727).length < 2 ^ (prefixWord ++ tailWord_7615727).sum := by decide
  have hdescent : baseEnd_7615727 < baseStart_7615727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615732 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7615732 : Nat := 118140960795 + 7615732 * 2 ^ 59
def prefixEnd_7615732 : Nat := 4983230072969 + 3 ^ 40 * 7615732 * 2
def baseEnd_7615732 : Nat := 3910531051826902647225893

theorem tailTrace_7615732 : CollatzResearch.WordTrace tailWord_7615732 prefixEnd_7615732 3910531051826902647225893 := by
  unfold tailWord_7615732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138884282822755551159800725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185179043763674068213067633 138884282822755551159800725)
  ·
    refine ⟨6510200757316666460615659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138884282822755551159800725 6510200757316666460615659)
    ·
      refine ⟨9765301135974999690923489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510200757316666460615659 9765301135974999690923489)
      ·
        refine ⟨7323975851981249768192617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9765301135974999690923489 7323975851981249768192617)
        ·
          refine ⟨5492981888985937326144463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7323975851981249768192617 5492981888985937326144463)
          ·
            refine ⟨8239472833478905989216695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492981888985937326144463 8239472833478905989216695)
            ·
              refine ⟨12359209250218358983825043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239472833478905989216695 12359209250218358983825043)
              ·
                refine ⟨18538813875327538475737565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359209250218358983825043 18538813875327538475737565)
                ·
                  refine ⟨6952055203247826928401587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18538813875327538475737565 6952055203247826928401587)
                  ·
                    refine ⟨10428082804871740392602381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952055203247826928401587 10428082804871740392602381)
                    ·
                      refine ⟨3910531051826902647225893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428082804871740392602381 3910531051826902647225893)
                      ·
                        rfl

theorem cell23_7615732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7615732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615732 prefixEnd_7615732 := by exact prefixLift 7615732
  have htrace : WordTrace (prefixWord ++ tailWord_7615732) baseStart_7615732 baseEnd_7615732 := by
    simpa [prefixWord, tailWord_7615732, baseEnd_7615732] using wordTrace_append hprefix tailTrace_7615732
  have hstable : (prefixWord ++ tailWord_7615732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615732).length < 2 ^ (prefixWord ++ tailWord_7615732).sum := by decide
  have hdescent : baseEnd_7615732 < baseStart_7615732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615737 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_7615737 : Nat := 118140960795 + 7615737 * 2 ^ 59
def prefixEnd_7615737 : Nat := 4983230072969 + 3 ^ 40 * 7615737 * 2
def baseEnd_7615737 : Nat := 3910533619230175127663369

theorem tailTrace_7615737 : CollatzResearch.WordTrace tailWord_7615737 prefixEnd_7615737 3910533619230175127663369 := by
  unfold tailWord_7615737
  simp only [CollatzResearch.WordTrace]
  refine ⟨277768748010492988173533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185179165340328658782355643 277768748010492988173533465)
  ·
    refine ⟨208326561007869741130150099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277768748010492988173533465 208326561007869741130150099)
    ·
      refine ⟨312489841511804611695225149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208326561007869741130150099 312489841511804611695225149)
      ·
        refine ⟨117183690566926729385709431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312489841511804611695225149 117183690566926729385709431)
        ·
          refine ⟨175775535850390094078564147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117183690566926729385709431 175775535850390094078564147)
          ·
            refine ⟨263663303775585141117846221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175775535850390094078564147 263663303775585141117846221)
            ·
              refine ⟨98873738915844427919192333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263663303775585141117846221 98873738915844427919192333)
              ·
                refine ⟨37077652093441660469697125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98873738915844427919192333 37077652093441660469697125)
                ·
                  refine ⟨6952059767520311338068211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37077652093441660469697125 6952059767520311338068211)
                  ·
                    refine ⟨10428089651280467007102317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952059767520311338068211 10428089651280467007102317)
                    ·
                      refine ⟨3910533619230175127663369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428089651280467007102317 3910533619230175127663369)
                      ·
                        rfl

theorem cell23_7615737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_7615737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615737 prefixEnd_7615737 := by exact prefixLift 7615737
  have htrace : WordTrace (prefixWord ++ tailWord_7615737) baseStart_7615737 baseEnd_7615737 := by
    simpa [prefixWord, tailWord_7615737, baseEnd_7615737] using wordTrace_append hprefix tailTrace_7615737
  have hstable : (prefixWord ++ tailWord_7615737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615737).length < 2 ^ (prefixWord ++ tailWord_7615737).sum := by decide
  have hdescent : baseEnd_7615737 < baseStart_7615737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615738 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_7615738 : Nat := 118140960795 + 7615738 * 2 ^ 59
def prefixEnd_7615738 : Nat := 4983230072969 + 3 ^ 40 * 7615738 * 2
def baseEnd_7615738 : Nat := 3910534132710829623750865

theorem tailTrace_7615738 : CollatzResearch.WordTrace tailWord_7615738 prefixEnd_7615738 3910534132710829623750865 := by
  unfold tailWord_7615738
  simp only [CollatzResearch.WordTrace]
  refine ⟨69442196120872341336079967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185179189655659576896213245 69442196120872341336079967)
  ·
    refine ⟨104163294181308512004119951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69442196120872341336079967 104163294181308512004119951)
    ·
      refine ⟨156244941271962768006179927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104163294181308512004119951 156244941271962768006179927)
      ·
        refine ⟨234367411907944152009269891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156244941271962768006179927 234367411907944152009269891)
        ·
          refine ⟨351551117861916228013904837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234367411907944152009269891 351551117861916228013904837)
          ·
            refine ⟨65915834599109292752607157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351551117861916228013904837 65915834599109292752607157)
            ·
              refine ⟨6179609493666496195556921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65915834599109292752607157 6179609493666496195556921)
              ·
                refine ⟨4634707120249872146667691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6179609493666496195556921 4634707120249872146667691)
                ·
                  refine ⟨6952060680374808220001537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634707120249872146667691 6952060680374808220001537)
                  ·
                    refine ⟨5214045510281106165001153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6952060680374808220001537 5214045510281106165001153)
                    ·
                      refine ⟨3910534132710829623750865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214045510281106165001153 3910534132710829623750865)
                      ·
                        rfl

theorem cell23_7615738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_7615738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615738 prefixEnd_7615738 := by exact prefixLift 7615738
  have htrace : WordTrace (prefixWord ++ tailWord_7615738) baseStart_7615738 baseEnd_7615738 := by
    simpa [prefixWord, tailWord_7615738, baseEnd_7615738] using wordTrace_append hprefix tailTrace_7615738
  have hstable : (prefixWord ++ tailWord_7615738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615738).length < 2 ^ (prefixWord ++ tailWord_7615738).sum := by decide
  have hdescent : baseEnd_7615738 < baseStart_7615738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615797 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_7615797 : Nat := 118140960795 + 7615797 * 2 ^ 59
def prefixEnd_7615797 : Nat := 4983230072969 + 3 ^ 40 * 7615797 * 2
def baseEnd_7615797 : Nat := 3910564428069444892913093

theorem tailTrace_7615797 : CollatzResearch.WordTrace tailWord_7615797 prefixEnd_7615797 3910564428069444892913093 := by
  unfold tailWord_7615797
  simp only [CollatzResearch.WordTrace]
  refine ⟨277770936390275618420717645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185180624260183745613811763 277770936390275618420717645)
  ·
    refine ⟨104164101146353356907769117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277770936390275618420717645 104164101146353356907769117)
    ·
      refine ⟨39061537929882508840413419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104164101146353356907769117 39061537929882508840413419)
      ·
        refine ⟨58592306894823763260620129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39061537929882508840413419 58592306894823763260620129)
        ·
          refine ⟨43944230171117822445465097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58592306894823763260620129 43944230171117822445465097)
          ·
            refine ⟨32958172628338366834098823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43944230171117822445465097 32958172628338366834098823)
            ·
              refine ⟨49437258942507550251148235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32958172628338366834098823 49437258942507550251148235)
              ·
                refine ⟨74155888413761325376722353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49437258942507550251148235 74155888413761325376722353)
                ·
                  refine ⟨55616916310320994032541765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74155888413761325376722353 55616916310320994032541765)
                  ·
                    refine ⟨10428171808185186381101581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55616916310320994032541765 10428171808185186381101581)
                    ·
                      refine ⟨3910564428069444892913093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428171808185186381101581 3910564428069444892913093)
                      ·
                        rfl

theorem cell23_7615797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_7615797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615797 prefixEnd_7615797 := by exact prefixLift 7615797
  have htrace : WordTrace (prefixWord ++ tailWord_7615797) baseStart_7615797 baseEnd_7615797 := by
    simpa [prefixWord, tailWord_7615797, baseEnd_7615797] using wordTrace_append hprefix tailTrace_7615797
  have hstable : (prefixWord ++ tailWord_7615797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615797).length < 2 ^ (prefixWord ++ tailWord_7615797).sum := by decide
  have hdescent : baseEnd_7615797 < baseStart_7615797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615800 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 7]
def baseStart_7615800 : Nat := 118140960795 + 7615800 * 2 ^ 59
def prefixEnd_7615800 : Nat := 4983230072969 + 3 ^ 40 * 7615800 * 2
def baseEnd_7615800 : Nat := 434507329834600931241731

theorem tailTrace_7615800 : CollatzResearch.WordTrace tailWord_7615800 prefixEnd_7615800 434507329834600931241731 := by
  unfold tailWord_7615800
  simp only [CollatzResearch.WordTrace]
  refine ⟨138885522904632374966538427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185180697206176499955384569 138885522904632374966538427)
  ·
    refine ⟨208328284356948562449807641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138885522904632374966538427 208328284356948562449807641)
    ·
      refine ⟨156246213267711421837355731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208328284356948562449807641 156246213267711421837355731)
      ·
        refine ⟨234369319901567132756033597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156246213267711421837355731 234369319901567132756033597)
        ·
          refine ⟨87888494963087674783512599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234369319901567132756033597 87888494963087674783512599)
          ·
            refine ⟨131832742444631512175268899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87888494963087674783512599 131832742444631512175268899)
            ·
              refine ⟨197749113666947268262903349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131832742444631512175268899 197749113666947268262903349)
              ·
                refine ⟨18538979406276306399647189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197749113666947268262903349 18538979406276306399647189)
                ·
                  refine ⟨434507329834600931241731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18538979406276306399647189 434507329834600931241731)
                  ·
                    rfl

theorem cell23_7615800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_7615800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615800 prefixEnd_7615800 := by exact prefixLift 7615800
  have htrace : WordTrace (prefixWord ++ tailWord_7615800) baseStart_7615800 baseEnd_7615800 := by
    simpa [prefixWord, tailWord_7615800, baseEnd_7615800] using wordTrace_append hprefix tailTrace_7615800
  have hstable : (prefixWord ++ tailWord_7615800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615800).length < 2 ^ (prefixWord ++ tailWord_7615800).sum := by decide
  have hdescent : baseEnd_7615800 < baseStart_7615800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615807 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_7615807 : Nat := 118140960795 + 7615807 * 2 ^ 59
def prefixEnd_7615807 : Nat := 4983230072969 + 3 ^ 40 * 7615807 * 2
def baseEnd_7615807 : Nat := 3910569562875989853788047

theorem tailTrace_7615807 : CollatzResearch.WordTrace tailWord_7615807 prefixEnd_7615807 3910569562875989853788047 := by
  unfold tailWord_7615807
  simp only [CollatzResearch.WordTrace]
  refine ⟨277771301120239390128581675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185180867413492926752387783 277771301120239390128581675)
  ·
    refine ⟨416656951680359085192872513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277771301120239390128581675 416656951680359085192872513)
    ·
      refine ⟨312492713760269313894654385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416656951680359085192872513 312492713760269313894654385)
      ·
        refine ⟨234369535320201985420990789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312492713760269313894654385 234369535320201985420990789)
        ·
          refine ⟨43944287872537872266435773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234369535320201985420990789 43944287872537872266435773)
          ·
            refine ⟨16479107952201702099913415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43944287872537872266435773 16479107952201702099913415)
            ·
              refine ⟨24718661928302553149870123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16479107952201702099913415 24718661928302553149870123)
              ·
                refine ⟨37077992892453829724805185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24718661928302553149870123 37077992892453829724805185)
                ·
                  refine ⟨27808494669340372293603889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37077992892453829724805185 27808494669340372293603889)
                  ·
                    refine ⟨20856371002005279220202917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27808494669340372293603889 20856371002005279220202917)
                    ·
                      refine ⟨3910569562875989853788047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20856371002005279220202917 3910569562875989853788047)
                      ·
                        rfl

theorem cell23_7615807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_7615807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615807 prefixEnd_7615807 := by exact prefixLift 7615807
  have htrace : WordTrace (prefixWord ++ tailWord_7615807) baseStart_7615807 baseEnd_7615807 := by
    simpa [prefixWord, tailWord_7615807, baseEnd_7615807] using wordTrace_append hprefix tailTrace_7615807
  have hstable : (prefixWord ++ tailWord_7615807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615807).length < 2 ^ (prefixWord ++ tailWord_7615807).sum := by decide
  have hdescent : baseEnd_7615807 < baseStart_7615807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615904 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_7615904 : Nat := 118140960795 + 7615904 * 2 ^ 59
def prefixEnd_7615904 : Nat := 4983230072969 + 3 ^ 40 * 7615904 * 2
def baseEnd_7615904 : Nat := 3910619370499475974275101

theorem tailTrace_7615904 : CollatzResearch.WordTrace tailWord_7615904 prefixEnd_7615904 3910619370499475974275101 := by
  unfold tailWord_7615904
  simp only [CollatzResearch.WordTrace]
  refine ⟨138887419500443987847431383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185183226000591983796575177 138887419500443987847431383)
  ·
    refine ⟨208331129250665981771147075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138887419500443987847431383 208331129250665981771147075)
    ·
      refine ⟨312496693875998972656720613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208331129250665981771147075 312496693875998972656720613)
      ·
        refine ⟨58593130101749807373135115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312496693875998972656720613 58593130101749807373135115)
        ·
          refine ⟨87889695152624711059702673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58593130101749807373135115 87889695152624711059702673)
          ·
            refine ⟨65917271364468533294777005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87889695152624711059702673 65917271364468533294777005)
            ·
              refine ⟨24718976761675699985541377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65917271364468533294777005 24718976761675699985541377)
              ·
                refine ⟨18539232571256774989156033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24718976761675699985541377 18539232571256774989156033)
                ·
                  refine ⟨13904424428442581241867025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18539232571256774989156033 13904424428442581241867025)
                  ·
                    refine ⟨10428318321331935931400269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13904424428442581241867025 10428318321331935931400269)
                    ·
                      refine ⟨3910619370499475974275101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428318321331935931400269 3910619370499475974275101)
                      ·
                        rfl

theorem cell23_7615904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_7615904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615904 prefixEnd_7615904 := by exact prefixLift 7615904
  have htrace : WordTrace (prefixWord ++ tailWord_7615904) baseStart_7615904 baseEnd_7615904 := by
    simpa [prefixWord, tailWord_7615904, baseEnd_7615904] using wordTrace_append hprefix tailTrace_7615904
  have hstable : (prefixWord ++ tailWord_7615904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615904).length < 2 ^ (prefixWord ++ tailWord_7615904).sum := by decide
  have hdescent : baseEnd_7615904 < baseStart_7615904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615907 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 6]
def baseStart_7615907 : Nat := 118140960795 + 7615907 * 2 ^ 59
def prefixEnd_7615907 : Nat := 4983230072969 + 3 ^ 40 * 7615907 * 2
def baseEnd_7615907 : Nat := 434513434549048829170843

theorem tailTrace_7615907 : CollatzResearch.WordTrace tailWord_7615907 prefixEnd_7615907 434513434549048829170843 := by
  unfold tailWord_7615907
  simp only [CollatzResearch.WordTrace]
  refine ⟨277774948419877107207221975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185183298946584738138147983 277774948419877107207221975)
  ·
    refine ⟨416662422629815660810832963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277774948419877107207221975 416662422629815660810832963)
    ·
      refine ⟨624993633944723491216249445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416662422629815660810832963 624993633944723491216249445)
      ·
        refine ⟨117186306364635654603046771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624993633944723491216249445 117186306364635654603046771)
        ·
          refine ⟨175779459546953481904570157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117186306364635654603046771 175779459546953481904570157)
          ·
            refine ⟨65917297330107555714213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175779459546953481904570157 65917297330107555714213809)
            ·
              refine ⟨49437972997580666785660357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65917297330107555714213809 49437972997580666785660357)
              ·
                refine ⟨9269619937046375022311317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49437972997580666785660357 9269619937046375022311317)
                ·
                  refine ⟨434513434549048829170843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9269619937046375022311317 434513434549048829170843)
                  ·
                    rfl

theorem cell23_7615907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 6].length) (baseStart_7615907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615907 prefixEnd_7615907 := by exact prefixLift 7615907
  have htrace : WordTrace (prefixWord ++ tailWord_7615907) baseStart_7615907 baseEnd_7615907 := by
    simpa [prefixWord, tailWord_7615907, baseEnd_7615907] using wordTrace_append hprefix tailTrace_7615907
  have hstable : (prefixWord ++ tailWord_7615907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615907).length < 2 ^ (prefixWord ++ tailWord_7615907).sum := by decide
  have hdescent : baseEnd_7615907 < baseStart_7615907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615961 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 2, 3, 2]
def baseStart_7615961 : Nat := 118140960795 + 7615961 * 2 ^ 59
def prefixEnd_7615961 : Nat := 4983230072969 + 3 ^ 40 * 7615961 * 2
def baseEnd_7615961 : Nat := 3910648638896782251262339

theorem tailTrace_7615961 : CollatzResearch.WordTrace tailWord_7615961 prefixEnd_7615961 3910648638896782251262339 := by
  unfold tailWord_7615961
  simp only [CollatzResearch.WordTrace]
  refine ⟨277776917961681474429687737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185184611974454316286458491 277776917961681474429687737)
  ·
    refine ⟨208332688471261105822265803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277776917961681474429687737 208332688471261105822265803)
    ·
      refine ⟨312499032706891658733398705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208332688471261105822265803 312499032706891658733398705)
      ·
        refine ⟨234374274530168744050049029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312499032706891658733398705 234374274530168744050049029)
        ·
          refine ⟨43945176474406639509384193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234374274530168744050049029 43945176474406639509384193)
          ·
            refine ⟨32958882355804979632038145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43945176474406639509384193 32958882355804979632038145)
            ·
              refine ⟨24719161766853734724028609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32958882355804979632038145 24719161766853734724028609)
              ·
                refine ⟨18539371325140301043021457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24719161766853734724028609 18539371325140301043021457)
                ·
                  refine ⟨13904528493855225782266093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18539371325140301043021457 13904528493855225782266093)
                  ·
                    refine ⟨5214198185195709668349785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13904528493855225782266093 5214198185195709668349785)
                    ·
                      refine ⟨3910648638896782251262339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214198185195709668349785 3910648638896782251262339)
                      ·
                        rfl

theorem cell23_7615961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_7615961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615961 prefixEnd_7615961 := by exact prefixLift 7615961
  have htrace : WordTrace (prefixWord ++ tailWord_7615961) baseStart_7615961 baseEnd_7615961 := by
    simpa [prefixWord, tailWord_7615961, baseEnd_7615961] using wordTrace_append hprefix tailTrace_7615961
  have hstable : (prefixWord ++ tailWord_7615961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615961).length < 2 ^ (prefixWord ++ tailWord_7615961).sum := by decide
  have hdescent : baseEnd_7615961 < baseStart_7615961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615967 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 6]
def baseStart_7615967 : Nat := 118140960795 + 7615967 * 2 ^ 59
def prefixEnd_7615967 : Nat := 4983230072969 + 3 ^ 40 * 7615967 * 2
def baseEnd_7615967 : Nat := 1303550573260236409262437

theorem tailTrace_7615967 : CollatzResearch.WordTrace tailWord_7615967 prefixEnd_7615967 1303550573260236409262437 := by
  unfold tailWord_7615967
  simp only [CollatzResearch.WordTrace]
  refine ⟨277777136799659737454406155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185184757866439824969604103 277777136799659737454406155)
  ·
    refine ⟨416665705199489606181609233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277777136799659737454406155 416665705199489606181609233)
    ·
      refine ⟨312499278899617204636206925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416665705199489606181609233 312499278899617204636206925)
      ·
        refine ⟨117187229587356451738577597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312499278899617204636206925 117187229587356451738577597)
        ·
          refine ⟨43945211095258669401966599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117187229587356451738577597 43945211095258669401966599)
          ·
            refine ⟨65917816642888004102949899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43945211095258669401966599 65917816642888004102949899)
            ·
              refine ⟨98876724964332006154424849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65917816642888004102949899 98876724964332006154424849)
              ·
                refine ⟨74157543723249004615818637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98876724964332006154424849 74157543723249004615818637)
                ·
                  refine ⟨27809078896218376730931989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74157543723249004615818637 27809078896218376730931989)
                  ·
                    refine ⟨1303550573260236409262437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27809078896218376730931989 1303550573260236409262437)
                    ·
                      rfl

theorem cell23_7615967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_7615967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615967 prefixEnd_7615967 := by exact prefixLift 7615967
  have htrace : WordTrace (prefixWord ++ tailWord_7615967) baseStart_7615967 baseEnd_7615967 := by
    simpa [prefixWord, tailWord_7615967, baseEnd_7615967] using wordTrace_append hprefix tailTrace_7615967
  have hstable : (prefixWord ++ tailWord_7615967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615967).length < 2 ^ (prefixWord ++ tailWord_7615967).sum := by decide
  have hdescent : baseEnd_7615967 < baseStart_7615967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615984 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_7615984 : Nat := 118140960795 + 7615984 * 2 ^ 59
def prefixEnd_7615984 : Nat := 4983230072969 + 3 ^ 40 * 7615984 * 2
def baseEnd_7615984 : Nat := 1303553482983945220424911

theorem tailTrace_7615984 : CollatzResearch.WordTrace tailWord_7615984 prefixEnd_7615984 1303553482983945220424911 := by
  unfold tailWord_7615984
  simp only [CollatzResearch.WordTrace]
  refine ⟨138888878420299074678887503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185185171227065432905183337 138888878420299074678887503)
  ·
    refine ⟨208333317630448612018331255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138888878420299074678887503 208333317630448612018331255)
    ·
      refine ⟨312499976445672918027496883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208333317630448612018331255 312499976445672918027496883)
      ·
        refine ⟨468749964668509377041245325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312499976445672918027496883 468749964668509377041245325)
        ·
          refine ⟨175781236750691016390466997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468749964668509377041245325 175781236750691016390466997)
          ·
            refine ⟨16479490945377282786606281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175781236750691016390466997 16479490945377282786606281)
            ·
              refine ⟨12359618209032962089954711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16479490945377282786606281 12359618209032962089954711)
              ·
                refine ⟨18539427313549443134932067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359618209032962089954711 18539427313549443134932067)
                ·
                  refine ⟨27809140970324164702398101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18539427313549443134932067 27809140970324164702398101)
                  ·
                    refine ⟨1303553482983945220424911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27809140970324164702398101 1303553482983945220424911)
                    ·
                      rfl

theorem cell23_7615984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_7615984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615984 prefixEnd_7615984 := by exact prefixLift 7615984
  have htrace : WordTrace (prefixWord ++ tailWord_7615984) baseStart_7615984 baseEnd_7615984 := by
    simpa [prefixWord, tailWord_7615984, baseEnd_7615984] using wordTrace_append hprefix tailTrace_7615984
  have hstable : (prefixWord ++ tailWord_7615984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615984).length < 2 ^ (prefixWord ++ tailWord_7615984).sum := by decide
  have hdescent : baseEnd_7615984 < baseStart_7615984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7615994 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_7615994 : Nat := 118140960795 + 7615994 * 2 ^ 59
def prefixEnd_7615994 : Nat := 4983230072969 + 3 ^ 40 * 7615994 * 2
def baseEnd_7615994 : Nat := 3910665583758380622149687

theorem tailTrace_7615994 : CollatzResearch.WordTrace tailWord_7615994 prefixEnd_7615994 3910665583758380622149687 := by
  unfold tailWord_7615994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444530392640480266409759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185185414380374614043759357 69444530392640480266409759)
  ·
    refine ⟨104166795588960720399614639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69444530392640480266409759 104166795588960720399614639)
    ·
      refine ⟨156250193383441080599421959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104166795588960720399614639 156250193383441080599421959)
      ·
        refine ⟨234375290075161620899132939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156250193383441080599421959 234375290075161620899132939)
        ·
          refine ⟨351562935112742431348699409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234375290075161620899132939 351562935112742431348699409)
          ·
            refine ⟨263672201334556823511524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351562935112742431348699409 263672201334556823511524557)
            ·
              refine ⟨98877075500458808816821709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263672201334556823511524557 98877075500458808816821709)
              ·
                refine ⟨37078903312672053306308141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98877075500458808816821709 37078903312672053306308141)
                ·
                  refine ⟨13904588742252019989865553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37078903312672053306308141 13904588742252019989865553)
                  ·
                    refine ⟨10428441556689014992399165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13904588742252019989865553 10428441556689014992399165)
                    ·
                      refine ⟨3910665583758380622149687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428441556689014992399165 3910665583758380622149687)
                      ·
                        rfl

theorem cell23_7615994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_7615994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7615994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7615994 prefixEnd_7615994 := by exact prefixLift 7615994
  have htrace : WordTrace (prefixWord ++ tailWord_7615994) baseStart_7615994 baseEnd_7615994 := by
    simpa [prefixWord, tailWord_7615994, baseEnd_7615994] using wordTrace_append hprefix tailTrace_7615994
  have hstable : (prefixWord ++ tailWord_7615994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7615994).length < 2 ^ (prefixWord ++ tailWord_7615994).sum := by decide
  have hdescent : baseEnd_7615994 < baseStart_7615994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7615994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616002 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7616002 : Nat := 118140960795 + 7616002 * 2 ^ 59
def prefixEnd_7616002 : Nat := 4983230072969 + 3 ^ 40 * 7616002 * 2
def baseEnd_7616002 : Nat := 3910669691603616590849651

theorem tailTrace_7616002 : CollatzResearch.WordTrace tailWord_7616002 prefixEnd_7616002 3910669691603616590849651 := by
  unfold tailWord_7616002
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444603338633234607982565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185185608903021958954620173 69444603338633234607982565)
  ·
    refine ⟨13020863125993731488996731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69444603338633234607982565 13020863125993731488996731)
    ·
      refine ⟨19531294688990597233495097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13020863125993731488996731 19531294688990597233495097)
      ·
        refine ⟨14648471016742947925121323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19531294688990597233495097 14648471016742947925121323)
        ·
          refine ⟨21972706525114421887681985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648471016742947925121323 21972706525114421887681985)
          ·
            refine ⟨16479529893835816415761489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21972706525114421887681985 16479529893835816415761489)
            ·
              refine ⟨12359647420376862311821117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16479529893835816415761489 12359647420376862311821117)
              ·
                refine ⟨4634867782641323366932919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12359647420376862311821117 4634867782641323366932919)
                ·
                  refine ⟨6952301673961985050399379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634867782641323366932919 6952301673961985050399379)
                  ·
                    refine ⟨10428452510942977575599069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952301673961985050399379 10428452510942977575599069)
                    ·
                      refine ⟨3910669691603616590849651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428452510942977575599069 3910669691603616590849651)
                      ·
                        rfl

theorem cell23_7616002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7616002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616002 prefixEnd_7616002 := by exact prefixLift 7616002
  have htrace : WordTrace (prefixWord ++ tailWord_7616002) baseStart_7616002 baseEnd_7616002 := by
    simpa [prefixWord, tailWord_7616002, baseEnd_7616002] using wordTrace_append hprefix tailTrace_7616002
  have hstable : (prefixWord ++ tailWord_7616002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616002).length < 2 ^ (prefixWord ++ tailWord_7616002).sum := by decide
  have hdescent : baseEnd_7616002 < baseStart_7616002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616014 : List Nat := [4, 1, 1, 2, 4, 1, 10]
def baseStart_7616014 : Nat := 118140960795 + 7616014 * 2 ^ 59
def prefixEnd_7616014 : Nat := 4983230072969 + 3 ^ 40 * 7616014 * 2
def baseEnd_7616014 : Nat := 48279948807055191899995

theorem tailTrace_7616014 : CollatzResearch.WordTrace tailWord_7616014 prefixEnd_7616014 48279948807055191899995 := by
  unfold tailWord_7616014
  simp only [CollatzResearch.WordTrace]
  refine ⟨34722356378811183060170887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185185900686992976320911397 34722356378811183060170887)
  ·
    refine ⟨52083534568216774590256331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34722356378811183060170887 52083534568216774590256331)
    ·
      refine ⟨78125301852325161885384497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52083534568216774590256331 78125301852325161885384497)
      ·
        refine ⟨58593976389243871414038373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78125301852325161885384497 58593976389243871414038373)
        ·
          refine ⟨10986370572983225890132195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58593976389243871414038373 10986370572983225890132195)
          ·
            refine ⟨16479555859474838835198293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986370572983225890132195 16479555859474838835198293)
            ·
              refine ⟨48279948807055191899995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16479555859474838835198293 48279948807055191899995)
              ·
                rfl

theorem cell23_7616014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 10].length) (baseStart_7616014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616014 prefixEnd_7616014 := by exact prefixLift 7616014
  have htrace : WordTrace (prefixWord ++ tailWord_7616014) baseStart_7616014 baseEnd_7616014 := by
    simpa [prefixWord, tailWord_7616014, baseEnd_7616014] using wordTrace_append hprefix tailTrace_7616014
  have hstable : (prefixWord ++ tailWord_7616014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616014).length < 2 ^ (prefixWord ++ tailWord_7616014).sum := by decide
  have hdescent : baseEnd_7616014 < baseStart_7616014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616084 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7616084 : Nat := 118140960795 + 7616084 * 2 ^ 59
def prefixEnd_7616084 : Nat := 4983230072969 + 3 ^ 40 * 7616084 * 2
def baseEnd_7616084 : Nat := 3910711797017285270024273

theorem tailTrace_7616084 : CollatzResearch.WordTrace tailWord_7616084 prefixEnd_7616084 3910711797017285270024273 := by
  unfold tailWord_7616084
  simp only [CollatzResearch.WordTrace]
  refine ⟨138890702070117933218207653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185187602760157244290943537 138890702070117933218207653)
  ·
    refine ⟨26042006638147112478413935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138890702070117933218207653 26042006638147112478413935)
    ·
      refine ⟨39063009957220668717620903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26042006638147112478413935 39063009957220668717620903)
      ·
        refine ⟨58594514935831003076431355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39063009957220668717620903 58594514935831003076431355)
        ·
          refine ⟨87891772403746504614647033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58594514935831003076431355 87891772403746504614647033)
          ·
            refine ⟨65918829302809878460985275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87891772403746504614647033 65918829302809878460985275)
            ·
              refine ⟨98878243954214817691477913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65918829302809878460985275 98878243954214817691477913)
              ·
                refine ⟨74158682965661113268608435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98878243954214817691477913 74158682965661113268608435)
                ·
                  refine ⟨111238024448491669902912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74158682965661113268608435 111238024448491669902912653)
                  ·
                    refine ⟨41714259168184376213592245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111238024448491669902912653 41714259168184376213592245)
                    ·
                      refine ⟨3910711797017285270024273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41714259168184376213592245 3910711797017285270024273)
                      ·
                        rfl

theorem cell23_7616084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7616084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616084 prefixEnd_7616084 := by exact prefixLift 7616084
  have htrace : WordTrace (prefixWord ++ tailWord_7616084) baseStart_7616084 baseEnd_7616084 := by
    simpa [prefixWord, tailWord_7616084, baseEnd_7616084] using wordTrace_append hprefix tailTrace_7616084
  have hstable : (prefixWord ++ tailWord_7616084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616084).length < 2 ^ (prefixWord ++ tailWord_7616084).sum := by decide
  have hdescent : baseEnd_7616084 < baseStart_7616084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616086 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7616086 : Nat := 118140960795 + 7616086 * 2 ^ 59
def prefixEnd_7616086 : Nat := 4983230072969 + 3 ^ 40 * 7616086 * 2
def baseEnd_7616086 : Nat := 1303570941326198087399755

theorem tailTrace_7616086 : CollatzResearch.WordTrace tailWord_7616086 prefixEnd_7616086 1303570941326198087399755 := by
  unfold tailWord_7616086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361342317889288798624257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185187651390819080518658741 17361342317889288798624257)
  ·
    refine ⟨13021006738416966598968193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17361342317889288798624257 13021006738416966598968193)
    ·
      refine ⟨9765755053812724949226145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13021006738416966598968193 9765755053812724949226145)
      ·
        refine ⟨7324316290359543711919609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9765755053812724949226145 7324316290359543711919609)
        ·
          refine ⟨5493237217769657783939707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324316290359543711919609 5493237217769657783939707)
          ·
            refine ⟨8239855826654486675909561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493237217769657783939707 8239855826654486675909561)
            ·
              refine ⟨6179891869990865006932171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8239855826654486675909561 6179891869990865006932171)
              ·
                refine ⟨9269837804986297510398257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179891869990865006932171 9269837804986297510398257)
                ·
                  refine ⟨6952378353739723132798693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269837804986297510398257 6952378353739723132798693)
                  ·
                    refine ⟨1303570941326198087399755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952378353739723132798693 1303570941326198087399755)
                    ·
                      rfl

theorem cell23_7616086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7616086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616086 prefixEnd_7616086 := by exact prefixLift 7616086
  have htrace : WordTrace (prefixWord ++ tailWord_7616086) baseStart_7616086 baseEnd_7616086 := by
    simpa [prefixWord, tailWord_7616086, baseEnd_7616086] using wordTrace_append hprefix tailTrace_7616086
  have hstable : (prefixWord ++ tailWord_7616086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616086).length < 2 ^ (prefixWord ++ tailWord_7616086).sum := by decide
  have hdescent : baseEnd_7616086 < baseStart_7616086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616092 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7616092 : Nat := 118140960795 + 7616092 * 2 ^ 59
def prefixEnd_7616092 : Nat := 4983230072969 + 3 ^ 40 * 7616092 * 2
def baseEnd_7616092 : Nat := 3910715904862521238724237

theorem tailTrace_7616092 : CollatzResearch.WordTrace tailWord_7616092 prefixEnd_7616092 3910715904862521238724237 := by
  unfold tailWord_7616092
  simp only [CollatzResearch.WordTrace]
  refine ⟨138890847962103441901353265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185187797282804589201804353 138890847962103441901353265)
  ·
    refine ⟨104168135971577581426014949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138890847962103441901353265 104168135971577581426014949)
    ·
      refine ⟨19531525494670796517377803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104168135971577581426014949 19531525494670796517377803)
      ·
        refine ⟨29297288242006194776066705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19531525494670796517377803 29297288242006194776066705)
        ·
          refine ⟨21972966181504646082050029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29297288242006194776066705 21972966181504646082050029)
          ·
            refine ⟨8239862318064242280768761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21972966181504646082050029 8239862318064242280768761)
            ·
              refine ⟨6179896738548181710576571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8239862318064242280768761 6179896738548181710576571)
              ·
                refine ⟨9269845107822272565864857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179896738548181710576571 9269845107822272565864857)
                ·
                  refine ⟨6952383830866704424398643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269845107822272565864857 6952383830866704424398643)
                  ·
                    refine ⟨10428575746300056636597965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952383830866704424398643 10428575746300056636597965)
                    ·
                      refine ⟨3910715904862521238724237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428575746300056636597965 3910715904862521238724237)
                      ·
                        rfl

theorem cell23_7616092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7616092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616092 prefixEnd_7616092 := by exact prefixLift 7616092
  have htrace : WordTrace (prefixWord ++ tailWord_7616092) baseStart_7616092 baseEnd_7616092 := by
    simpa [prefixWord, tailWord_7616092, baseEnd_7616092] using wordTrace_append hprefix tailTrace_7616092
  have hstable : (prefixWord ++ tailWord_7616092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616092).length < 2 ^ (prefixWord ++ tailWord_7616092).sum := by decide
  have hdescent : baseEnd_7616092 < baseStart_7616092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616121 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 5]
def baseStart_7616121 : Nat := 118140960795 + 7616121 * 2 ^ 59
def prefixEnd_7616121 : Nat := 4983230072969 + 3 ^ 40 * 7616121 * 2
def baseEnd_7616121 : Nat := 434525643977944625029067

theorem tailTrace_7616121 : CollatzResearch.WordTrace tailWord_7616121 prefixEnd_7616121 434525643977944625029067 := by
  unfold tailWord_7616121
  simp only [CollatzResearch.WordTrace]
  refine ⟨277782753641101821755512217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185188502427401214503674811 277782753641101821755512217)
  ·
    refine ⟨208337065230826366316634163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277782753641101821755512217 208337065230826366316634163)
    ·
      refine ⟨312505597846239549474951245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208337065230826366316634163 312505597846239549474951245)
      ·
        refine ⟨117189599192339831053106717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312505597846239549474951245 117189599192339831053106717)
        ·
          refine ⟨43946099697127436644915019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117189599192339831053106717 43946099697127436644915019)
          ·
            refine ⟨65919149545691154967372529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43946099697127436644915019 65919149545691154967372529)
            ·
              refine ⟨49439362159268366225529397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65919149545691154967372529 49439362159268366225529397)
              ·
                refine ⟨4634940202431409333643381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49439362159268366225529397 4634940202431409333643381)
                ·
                  refine ⟨434525643977944625029067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634940202431409333643381 434525643977944625029067)
                  ·
                    rfl

theorem cell23_7616121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 5].length) (baseStart_7616121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616121 prefixEnd_7616121 := by exact prefixLift 7616121
  have htrace : WordTrace (prefixWord ++ tailWord_7616121) baseStart_7616121 baseEnd_7616121 := by
    simpa [prefixWord, tailWord_7616121, baseEnd_7616121] using wordTrace_append hprefix tailTrace_7616121
  have hstable : (prefixWord ++ tailWord_7616121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616121).length < 2 ^ (prefixWord ++ tailWord_7616121).sum := by decide
  have hdescent : baseEnd_7616121 < baseStart_7616121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616132 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7616132 : Nat := 118140960795 + 7616132 * 2 ^ 59
def prefixEnd_7616132 : Nat := 4983230072969 + 3 ^ 40 * 7616132 * 2
def baseEnd_7616132 : Nat := 3910736444088701082224053

theorem tailTrace_7616132 : CollatzResearch.WordTrace tailWord_7616132 prefixEnd_7616132 3910736444088701082224053 := by
  unfold tailWord_7616132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138891577422030985317081325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185188769896041313756108433 138891577422030985317081325)
  ·
    refine ⟨52084341533261619493905497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138891577422030985317081325 52084341533261619493905497)
    ·
      refine ⟨39063256149946214620429123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52084341533261619493905497 39063256149946214620429123)
      ·
        refine ⟨58594884224919321930643685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39063256149946214620429123 58594884224919321930643685)
        ·
          refine ⟨10986540792172372861995691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58594884224919321930643685 10986540792172372861995691)
          ·
            refine ⟨16479811188258559292993537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986540792172372861995691 16479811188258559292993537)
            ·
              refine ⟨12359858391193919469745153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16479811188258559292993537 12359858391193919469745153)
              ·
                refine ⟨9269893793395439602308865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12359858391193919469745153 9269893793395439602308865)
                ·
                  refine ⟨6952420345046579701731649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269893793395439602308865 6952420345046579701731649)
                  ·
                    refine ⟨5214315258784934776298737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6952420345046579701731649 5214315258784934776298737)
                    ·
                      refine ⟨3910736444088701082224053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214315258784934776298737 3910736444088701082224053)
                      ·
                        rfl

theorem cell23_7616132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7616132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616132 prefixEnd_7616132 := by exact prefixLift 7616132
  have htrace : WordTrace (prefixWord ++ tailWord_7616132) baseStart_7616132 baseEnd_7616132 := by
    simpa [prefixWord, tailWord_7616132, baseEnd_7616132] using wordTrace_append hprefix tailTrace_7616132
  have hstable : (prefixWord ++ tailWord_7616132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616132).length < 2 ^ (prefixWord ++ tailWord_7616132).sum := by decide
  have hdescent : baseEnd_7616132 < baseStart_7616132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616138 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_7616138 : Nat := 118140960795 + 7616138 * 2 ^ 59
def prefixEnd_7616138 : Nat := 4983230072969 + 3 ^ 40 * 7616138 * 2
def baseEnd_7616138 : Nat := 434526613885847562083225

theorem tailTrace_7616138 : CollatzResearch.WordTrace tailWord_7616138 prefixEnd_7616138 434526613885847562083225 := by
  unfold tailWord_7616138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69445843420510058414720267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185188915788026822439254045 69445843420510058414720267)
  ·
    refine ⟨104168765130765087622080401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69445843420510058414720267 104168765130765087622080401)
    ·
      refine ⟨78126573848073815716560301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104168765130765087622080401 78126573848073815716560301)
      ·
        refine ⟨29297465193027680893710113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78126573848073815716560301 29297465193027680893710113)
        ·
          refine ⟨21973098894770760670282585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29297465193027680893710113 21973098894770760670282585)
          ·
            refine ⟨16479824171078070502711939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21973098894770760670282585 16479824171078070502711939)
            ·
              refine ⟨24719736256617105754067909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16479824171078070502711939 24719736256617105754067909)
              ·
                refine ⟨4634950548115707328887733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24719736256617105754067909 4634950548115707328887733)
                ·
                  refine ⟨434526613885847562083225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634950548115707328887733 434526613885847562083225)
                  ·
                    rfl

theorem cell23_7616138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_7616138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616138 prefixEnd_7616138 := by exact prefixLift 7616138
  have htrace : WordTrace (prefixWord ++ tailWord_7616138) baseStart_7616138 baseEnd_7616138 := by
    simpa [prefixWord, tailWord_7616138, baseEnd_7616138] using wordTrace_append hprefix tailTrace_7616138
  have hstable : (prefixWord ++ tailWord_7616138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616138).length < 2 ^ (prefixWord ++ tailWord_7616138).sum := by decide
  have hdescent : baseEnd_7616138 < baseStart_7616138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616184 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_7616184 : Nat := 118140960795 + 7616184 * 2 ^ 59
def prefixEnd_7616184 : Nat := 4983230072969 + 3 ^ 40 * 7616184 * 2
def baseEnd_7616184 : Nat := 3910763145082734878773813

theorem tailTrace_7616184 : CollatzResearch.WordTrace tailWord_7616184 prefixEnd_7616184 3910763145082734878773813 := by
  unfold tailWord_7616184
  simp only [CollatzResearch.WordTrace]
  refine ⟨138892525719936791757527803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185190034293249055676703737 138892525719936791757527803)
  ·
    refine ⟨208338788579905187636291705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138892525719936791757527803 208338788579905187636291705)
    ·
      refine ⟨156254091434928890727218779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208338788579905187636291705 156254091434928890727218779)
      ·
        refine ⟨234381137152393336090828169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156254091434928890727218779 234381137152393336090828169)
        ·
          refine ⟨175785852864295002068121127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234381137152393336090828169 175785852864295002068121127)
          ·
            refine ⟨263678779296442503102181691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175785852864295002068121127 263678779296442503102181691)
            ·
              refine ⟨395518168944663754653272537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263678779296442503102181691 395518168944663754653272537)
              ·
                refine ⟨296638626708497815989954403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395518168944663754653272537 296638626708497815989954403)
                ·
                  refine ⟨444957940062746723984931605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296638626708497815989954403 444957940062746723984931605)
                  ·
                    refine ⟨20857403440441252686793669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 444957940062746723984931605 20857403440441252686793669)
                    ·
                      refine ⟨3910763145082734878773813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20857403440441252686793669 3910763145082734878773813)
                      ·
                        rfl

theorem cell23_7616184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_7616184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616184 prefixEnd_7616184 := by exact prefixLift 7616184
  have htrace : WordTrace (prefixWord ++ tailWord_7616184) baseStart_7616184 baseEnd_7616184 := by
    simpa [prefixWord, tailWord_7616184, baseEnd_7616184] using wordTrace_append hprefix tailTrace_7616184
  have hstable : (prefixWord ++ tailWord_7616184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616184).length < 2 ^ (prefixWord ++ tailWord_7616184).sum := by decide
  have hdescent : baseEnd_7616184 < baseStart_7616184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616188 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7616188 : Nat := 118140960795 + 7616188 * 2 ^ 59
def prefixEnd_7616188 : Nat := 4983230072969 + 3 ^ 40 * 7616188 * 2
def baseEnd_7616188 : Nat := 3910765199005352863123795

theorem tailTrace_7616188 : CollatzResearch.WordTrace tailWord_7616188 prefixEnd_7616188 3910765199005352863123795 := by
  unfold tailWord_7616188
  simp only [CollatzResearch.WordTrace]
  refine ⟨138892598665929546099100609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185190131554572728132134145 138892598665929546099100609)
  ·
    refine ⟨104169448999447159574325457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138892598665929546099100609 104169448999447159574325457)
    ·
      refine ⟨78127086749585369680744093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104169448999447159574325457 78127086749585369680744093)
      ·
        refine ⟨29297657531094513630279035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78127086749585369680744093 29297657531094513630279035)
        ·
          refine ⟨43946486296641770445418553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29297657531094513630279035 43946486296641770445418553)
          ·
            refine ⟨32959864722481327834063915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43946486296641770445418553 32959864722481327834063915)
            ·
              refine ⟨49439797083721991751095873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32959864722481327834063915 49439797083721991751095873)
              ·
                refine ⟨37079847812791493813321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49439797083721991751095873 37079847812791493813321905)
                ·
                  refine ⟨27809885859593620359991429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37079847812791493813321905 27809885859593620359991429)
                  ·
                    refine ⟨5214353598673803817498393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27809885859593620359991429 5214353598673803817498393)
                    ·
                      refine ⟨3910765199005352863123795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214353598673803817498393 3910765199005352863123795)
                      ·
                        rfl

theorem cell23_7616188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7616188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616188 prefixEnd_7616188 := by exact prefixLift 7616188
  have htrace : WordTrace (prefixWord ++ tailWord_7616188) baseStart_7616188 baseEnd_7616188 := by
    simpa [prefixWord, tailWord_7616188, baseEnd_7616188] using wordTrace_append hprefix tailTrace_7616188
  have hstable : (prefixWord ++ tailWord_7616188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616188).length < 2 ^ (prefixWord ++ tailWord_7616188).sum := by decide
  have hdescent : baseEnd_7616188 < baseStart_7616188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616191 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_7616191 : Nat := 118140960795 + 7616191 * 2 ^ 59
def prefixEnd_7616191 : Nat := 4983230072969 + 3 ^ 40 * 7616191 * 2
def baseEnd_7616191 : Nat := 3910766739447316351386281

theorem tailTrace_7616191 : CollatzResearch.WordTrace tailWord_7616191 prefixEnd_7616191 3910766739447316351386281 := by
  unfold tailWord_7616191
  simp only [CollatzResearch.WordTrace]
  refine ⟨277785306750848223710560427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185190204500565482473706951 277785306750848223710560427)
  ·
    refine ⟨416677960126272335565840641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277785306750848223710560427 416677960126272335565840641)
    ·
      refine ⟨312508470094704251674380481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416677960126272335565840641 312508470094704251674380481)
      ·
        refine ⟨234381352571028188755785361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312508470094704251674380481 234381352571028188755785361)
        ·
          refine ⟨175786014428271141566839021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234381352571028188755785361 175786014428271141566839021)
          ·
            refine ⟨65919755410601678087564633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175786014428271141566839021 65919755410601678087564633)
            ·
              refine ⟨49439816557951258565673475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65919755410601678087564633 49439816557951258565673475)
              ·
                refine ⟨74159724836926887848510213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49439816557951258565673475 74159724836926887848510213)
                ·
                  refine ⟨13904948406923791471595665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74159724836926887848510213 13904948406923791471595665)
                  ·
                    refine ⟨10428711305192843603696749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13904948406923791471595665 10428711305192843603696749)
                    ·
                      refine ⟨3910766739447316351386281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428711305192843603696749 3910766739447316351386281)
                      ·
                        rfl

theorem cell23_7616191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_7616191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616191 prefixEnd_7616191 := by exact prefixLift 7616191
  have htrace : WordTrace (prefixWord ++ tailWord_7616191) baseStart_7616191 baseEnd_7616191 := by
    simpa [prefixWord, tailWord_7616191, baseEnd_7616191] using wordTrace_append hprefix tailTrace_7616191
  have hstable : (prefixWord ++ tailWord_7616191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616191).length < 2 ^ (prefixWord ++ tailWord_7616191).sum := by decide
  have hdescent : baseEnd_7616191 < baseStart_7616191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616232 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 1, 4]
def baseStart_7616232 : Nat := 118140960795 + 7616232 * 2 ^ 59
def prefixEnd_7616232 : Nat := 4983230072969 + 3 ^ 40 * 7616232 * 2
def baseEnd_7616232 : Nat := 1303595930718050230324531

theorem tailTrace_7616232 : CollatzResearch.WordTrace tailWord_7616232 prefixEnd_7616232 1303595930718050230324531 := by
  unfold tailWord_7616232
  simp only [CollatzResearch.WordTrace]
  refine ⟨138893401071849843856401475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185191201429133125141868633 138893401071849843856401475)
  ·
    refine ⟨208340101607774765784602213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138893401071849843856401475 208340101607774765784602213)
    ·
      refine ⟨39063769051457768584612915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208340101607774765784602213 39063769051457768584612915)
      ·
        refine ⟨58595653577186652876919373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39063769051457768584612915 58595653577186652876919373)
        ·
          refine ⟨21973370091444994828844765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58595653577186652876919373 21973370091444994828844765)
          ·
            refine ⟨8240013784291873060816787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21973370091444994828844765 8240013784291873060816787)
            ·
              refine ⟨12360020676437809591225181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240013784291873060816787 12360020676437809591225181)
              ·
                refine ⟨4635007753664178596709443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12360020676437809591225181 4635007753664178596709443)
                ·
                  refine ⟨6952511630496267895064165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635007753664178596709443 6952511630496267895064165)
                  ·
                    refine ⟨1303595930718050230324531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952511630496267895064165 1303595930718050230324531)
                    ·
                      rfl

theorem cell23_7616232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_7616232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616232 prefixEnd_7616232 := by exact prefixLift 7616232
  have htrace : WordTrace (prefixWord ++ tailWord_7616232) baseStart_7616232 baseEnd_7616232 := by
    simpa [prefixWord, tailWord_7616232, baseEnd_7616232] using wordTrace_append hprefix tailTrace_7616232
  have hstable : (prefixWord ++ tailWord_7616232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616232).length < 2 ^ (prefixWord ++ tailWord_7616232).sum := by decide
  have hdescent : baseEnd_7616232 < baseStart_7616232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616255 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 3]
def baseStart_7616255 : Nat := 118140960795 + 7616255 * 2 ^ 59
def prefixEnd_7616255 : Nat := 4983230072969 + 3 ^ 40 * 7616255 * 2
def baseEnd_7616255 : Nat := 3910799602209204100985987

theorem tailTrace_7616255 : CollatzResearch.WordTrace tailWord_7616255 prefixEnd_7616255 3910799602209204100985987 := by
  unfold tailWord_7616255
  simp only [CollatzResearch.WordTrace]
  refine ⟨277787641022616362640890219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185191760681744241760593479 277787641022616362640890219)
  ·
    refine ⟨416681461533924543961335329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277787641022616362640890219 416681461533924543961335329)
    ·
      refine ⟨312511096150443407971001497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416681461533924543961335329 312511096150443407971001497)
      ·
        refine ⟨234383322112832555978251123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312511096150443407971001497 234383322112832555978251123)
        ·
          refine ⟨351574983169248833967376685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234383322112832555978251123 351574983169248833967376685)
          ·
            refine ⟨131840618688468312737766257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351574983169248833967376685 131840618688468312737766257)
            ·
              refine ⟨98880464016351234553324693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131840618688468312737766257 98880464016351234553324693)
              ·
                refine ⟨4635021750766464119687095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98880464016351234553324693 4635021750766464119687095)
                ·
                  refine ⟨6952532626149696179530643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635021750766464119687095 6952532626149696179530643)
                  ·
                    refine ⟨10428798939224544269295965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952532626149696179530643 10428798939224544269295965)
                    ·
                      refine ⟨3910799602209204100985987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428798939224544269295965 3910799602209204100985987)
                      ·
                        rfl

theorem cell23_7616255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_7616255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616255 prefixEnd_7616255 := by exact prefixLift 7616255
  have htrace : WordTrace (prefixWord ++ tailWord_7616255) baseStart_7616255 baseEnd_7616255 := by
    simpa [prefixWord, tailWord_7616255, baseEnd_7616255] using wordTrace_append hprefix tailTrace_7616255
  have hstable : (prefixWord ++ tailWord_7616255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616255).length < 2 ^ (prefixWord ++ tailWord_7616255).sum := by decide
  have hdescent : baseEnd_7616255 < baseStart_7616255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616258 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7616258 : Nat := 118140960795 + 7616258 * 2 ^ 59
def prefixEnd_7616258 : Nat := 4983230072969 + 3 ^ 40 * 7616258 * 2
def baseEnd_7616258 : Nat := 1303600380883722529749491

theorem tailTrace_7616258 : CollatzResearch.WordTrace tailWord_7616258 prefixEnd_7616258 1303600380883722529749491 := by
  unfold tailWord_7616258
  simp only [CollatzResearch.WordTrace]
  refine ⟨69446937610401373538312357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185191833627736996102166285 69446937610401373538312357)
  ·
    refine ⟨13021300801950257538433567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69446937610401373538312357 13021300801950257538433567)
    ·
      refine ⟨19531951202925386307650351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021300801950257538433567 19531951202925386307650351)
      ·
        refine ⟨29297926804388079461475527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19531951202925386307650351 29297926804388079461475527)
        ·
          refine ⟨43946890206582119192213291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29297926804388079461475527 43946890206582119192213291)
          ·
            refine ⟨65920335309873178788319937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43946890206582119192213291 65920335309873178788319937)
            ·
              refine ⟨49440251482404884091239953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65920335309873178788319937 49440251482404884091239953)
              ·
                refine ⟨37080188611803663068429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49440251482404884091239953 37080188611803663068429965)
                ·
                  refine ⟨13905070729426373650661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37080188611803663068429965 13905070729426373650661237)
                  ·
                    refine ⟨1303600380883722529749491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13905070729426373650661237 1303600380883722529749491)
                    ·
                      rfl

theorem cell23_7616258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7616258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616258 prefixEnd_7616258 := by exact prefixLift 7616258
  have htrace : WordTrace (prefixWord ++ tailWord_7616258) baseStart_7616258 baseEnd_7616258 := by
    simpa [prefixWord, tailWord_7616258, baseEnd_7616258] using wordTrace_append hprefix tailTrace_7616258
  have hstable : (prefixWord ++ tailWord_7616258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616258).length < 2 ^ (prefixWord ++ tailWord_7616258).sum := by decide
  have hdescent : baseEnd_7616258 < baseStart_7616258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616271 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 6, 4]
def baseStart_7616271 : Nat := 118140960795 + 7616271 * 2 ^ 59
def prefixEnd_7616271 : Nat := 4983230072969 + 3 ^ 40 * 7616271 * 2
def baseEnd_7616271 : Nat := 1303602605966558679461971

theorem tailTrace_7616271 : CollatzResearch.WordTrace tailWord_7616271 prefixEnd_7616271 1303602605966558679461971 := by
  unfold tailWord_7616271
  simp only [CollatzResearch.WordTrace]
  refine ⟨277788224590558397373472667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185192149727038931582315111 277788224590558397373472667)
  ·
    refine ⟨416682336885837596060209001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277788224590558397373472667 416682336885837596060209001)
    ·
      refine ⟨312511752664378197045156751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416682336885837596060209001 312511752664378197045156751)
      ·
        refine ⟨468767628996567295567735127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312511752664378197045156751 468767628996567295567735127)
        ·
          refine ⟨703151443494850943351602691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468767628996567295567735127 703151443494850943351602691)
          ·
            refine ⟨1054727165242276415027404037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703151443494850943351602691 1054727165242276415027404037)
            ·
              refine ⟨197761343482926827817638257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1054727165242276415027404037 197761343482926827817638257)
              ·
                refine ⟨148321007612195120863228693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197761343482926827817638257 148321007612195120863228693)
                ·
                  refine ⟨6952547231821646290463845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148321007612195120863228693 6952547231821646290463845)
                  ·
                    refine ⟨1303602605966558679461971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952547231821646290463845 1303602605966558679461971)
                    ·
                      rfl

theorem cell23_7616271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_7616271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616271 prefixEnd_7616271 := by exact prefixLift 7616271
  have htrace : WordTrace (prefixWord ++ tailWord_7616271) baseStart_7616271 baseEnd_7616271 := by
    simpa [prefixWord, tailWord_7616271, baseEnd_7616271] using wordTrace_append hprefix tailTrace_7616271
  have hstable : (prefixWord ++ tailWord_7616271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616271).length < 2 ^ (prefixWord ++ tailWord_7616271).sum := by decide
  have hdescent : baseEnd_7616271 < baseStart_7616271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616291 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7616291 : Nat := 118140960795 + 7616291 * 2 ^ 59
def prefixEnd_7616291 : Nat := 4983230072969 + 3 ^ 40 * 7616291 * 2
def baseEnd_7616291 : Nat := 3910818087512765960135821

theorem tailTrace_7616291 : CollatzResearch.WordTrace tailWord_7616291 prefixEnd_7616291 3910818087512765960135821 := by
  unfold tailWord_7616291
  simp only [CollatzResearch.WordTrace]
  refine ⟨277788954050485940789200727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185192636033657293859467151 277788954050485940789200727)
  ·
    refine ⟨416683431075728911183801091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277788954050485940789200727 416683431075728911183801091)
    ·
      refine ⟨625025146613593366775701637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416683431075728911183801091 625025146613593366775701637)
      ·
        refine ⟨117192214990048756270444057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 625025146613593366775701637 117192214990048756270444057)
        ·
          refine ⟨87894161242536567202833043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117192214990048756270444057 87894161242536567202833043)
          ·
            refine ⟨131841241863804850804249565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87894161242536567202833043 131841241863804850804249565)
            ·
              refine ⟨49440465698926819051593587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131841241863804850804249565 49440465698926819051593587)
              ·
                refine ⟨74160698548390228577390381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49440465698926819051593587 74160698548390228577390381)
                ·
                  refine ⟨27810261955646335716521393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74160698548390228577390381 27810261955646335716521393)
                  ·
                    refine ⟨20857696466734751787391045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27810261955646335716521393 20857696466734751787391045)
                    ·
                      refine ⟨3910818087512765960135821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20857696466734751787391045 3910818087512765960135821)
                      ·
                        rfl

theorem cell23_7616291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7616291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616291 prefixEnd_7616291 := by exact prefixLift 7616291
  have htrace : WordTrace (prefixWord ++ tailWord_7616291) baseStart_7616291 baseEnd_7616291 := by
    simpa [prefixWord, tailWord_7616291, baseEnd_7616291] using wordTrace_append hprefix tailTrace_7616291
  have hstable : (prefixWord ++ tailWord_7616291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616291).length < 2 ^ (prefixWord ++ tailWord_7616291).sum := by decide
  have hdescent : baseEnd_7616291 < baseStart_7616291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616301 : List Nat := [1, 5, 3, 14]
def baseStart_7616301 : Nat := 118140960795 + 7616301 * 2 ^ 59
def prefixEnd_7616301 : Nat := 4983230072969 + 3 ^ 40 * 7616301 * 2
def baseEnd_7616301 : Nat := 1788213636177096900325

theorem tailTrace_7616301 : CollatzResearch.WordTrace tailWord_7616301 prefixEnd_7616301 1788213636177096900325 := by
  unfold tailWord_7616301
  simp only [CollatzResearch.WordTrace]
  refine ⟨277789318780449712497064757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185192879186966474998043171 277789318780449712497064757)
  ·
    refine ⟨26042748635667160546599821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277789318780449712497064757 26042748635667160546599821)
    ·
      refine ⟨9766030738375185204974933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26042748635667160546599821 9766030738375185204974933)
      ·
        refine ⟨1788213636177096900325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9766030738375185204974933 1788213636177096900325)
        ·
          rfl

theorem cell23_7616301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 14].length) (baseStart_7616301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616301 prefixEnd_7616301 := by exact prefixLift 7616301
  have htrace : WordTrace (prefixWord ++ tailWord_7616301) baseStart_7616301 baseEnd_7616301 := by
    simpa [prefixWord, tailWord_7616301, baseEnd_7616301] using wordTrace_append hprefix tailTrace_7616301
  have hstable : (prefixWord ++ tailWord_7616301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616301).length < 2 ^ (prefixWord ++ tailWord_7616301).sum := by decide
  have hdescent : baseEnd_7616301 < baseStart_7616301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616305 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_7616305 : Nat := 118140960795 + 7616305 * 2 ^ 59
def prefixEnd_7616305 : Nat := 4983230072969 + 3 ^ 40 * 7616305 * 2
def baseEnd_7616305 : Nat := 1303608425413976301786919

theorem tailTrace_7616305 : CollatzResearch.WordTrace tailWord_7616305 prefixEnd_7616305 1303608425413976301786919 := by
  unfold tailWord_7616305
  simp only [CollatzResearch.WordTrace]
  refine ⟨277789464672435221180210369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185192976448290147453473579 277789464672435221180210369)
  ·
    refine ⟨208342098504326415885157777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277789464672435221180210369 208342098504326415885157777)
    ·
      refine ⟨156256573878244811913868333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208342098504326415885157777 156256573878244811913868333)
      ·
        refine ⟨58596215204341804467700625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156256573878244811913868333 58596215204341804467700625)
        ·
          refine ⟨43947161403256353350775469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58596215204341804467700625 43947161403256353350775469)
          ·
            refine ⟨16480185526221132506540801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43947161403256353350775469 16480185526221132506540801)
            ·
              refine ⟨12360139144665849379905601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16480185526221132506540801 12360139144665849379905601)
              ·
                refine ⟨9270104358499387034929201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360139144665849379905601 9270104358499387034929201)
                ·
                  refine ⟨6952578268874540276196901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270104358499387034929201 6952578268874540276196901)
                  ·
                    refine ⟨1303608425413976301786919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952578268874540276196901 1303608425413976301786919)
                    ·
                      rfl

theorem cell23_7616305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_7616305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616305 prefixEnd_7616305 := by exact prefixLift 7616305
  have htrace : WordTrace (prefixWord ++ tailWord_7616305) baseStart_7616305 baseEnd_7616305 := by
    simpa [prefixWord, tailWord_7616305, baseEnd_7616305] using wordTrace_append hprefix tailTrace_7616305
  have hstable : (prefixWord ++ tailWord_7616305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616305).length < 2 ^ (prefixWord ++ tailWord_7616305).sum := by decide
  have hdescent : baseEnd_7616305 < baseStart_7616305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616318 : List Nat := [4, 2, 1, 2, 2, 1, 3, 8]
def baseStart_7616318 : Nat := 118140960795 + 7616318 * 2 ^ 59
def prefixEnd_7616318 : Nat := 4983230072969 + 3 ^ 40 * 7616318 * 2
def baseEnd_7616318 : Nat := 144845627832979161277711

theorem tailTrace_7616318 : CollatzResearch.WordTrace tailWord_7616318 prefixEnd_7616318 144845627832979161277711 := by
  unfold tailWord_7616318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34723742352673515550054201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185193292547592082933622405 34723742352673515550054201)
  ·
    refine ⟨26042806764505136662540651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34723742352673515550054201 26042806764505136662540651)
    ·
      refine ⟨39064210146757704993810977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26042806764505136662540651 39064210146757704993810977)
      ·
        refine ⟨29298157610068278745358233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39064210146757704993810977 29298157610068278745358233)
        ·
          refine ⟨21973618207551209059018675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298157610068278745358233 21973618207551209059018675)
          ·
            refine ⟨32960427311326813588528013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21973618207551209059018675 32960427311326813588528013)
            ·
              refine ⟨12360160241747555095698005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32960427311326813588528013 12360160241747555095698005)
              ·
                refine ⟨144845627832979161277711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12360160241747555095698005 144845627832979161277711)
                ·
                  rfl

theorem cell23_7616318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_7616318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616318 prefixEnd_7616318 := by exact prefixLift 7616318
  have htrace : WordTrace (prefixWord ++ tailWord_7616318) baseStart_7616318 baseEnd_7616318 := by
    simpa [prefixWord, tailWord_7616318, baseEnd_7616318] using wordTrace_append hprefix tailTrace_7616318
  have hstable : (prefixWord ++ tailWord_7616318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616318).length < 2 ^ (prefixWord ++ tailWord_7616318).sum := by decide
  have hdescent : baseEnd_7616318 < baseStart_7616318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616328 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_7616328 : Nat := 118140960795 + 7616328 * 2 ^ 59
def prefixEnd_7616328 : Nat := 4983230072969 + 3 ^ 40 * 7616328 * 2
def baseEnd_7616328 : Nat := 3910837086296982315373151

theorem tailTrace_7616328 : CollatzResearch.WordTrace tailWord_7616328 prefixEnd_7616328 3910837086296982315373151 := by
  unfold tailWord_7616328
  simp only [CollatzResearch.WordTrace]
  refine ⟨138895151775675948054148819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185193535700901264072198425 138895151775675948054148819)
  ·
    refine ⟨208342727663513922081223229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138895151775675948054148819 208342727663513922081223229)
    ·
      refine ⟨78128522873817720780458711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208342727663513922081223229 78128522873817720780458711)
      ·
        refine ⟨117192784310726581170688067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78128522873817720780458711 117192784310726581170688067)
        ·
          refine ⟨175789176466089871756032101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117192784310726581170688067 175789176466089871756032101)
          ·
            refine ⟨32960470587391850954256019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175789176466089871756032101 32960470587391850954256019)
            ·
              refine ⟨49440705881087776431384029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32960470587391850954256019 49440705881087776431384029)
              ·
                refine ⟨18540264705407916161769011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49440705881087776431384029 18540264705407916161769011)
                ·
                  refine ⟨27810397058111874242653517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18540264705407916161769011 27810397058111874242653517)
                  ·
                    refine ⟨10428898896791952840995069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27810397058111874242653517 10428898896791952840995069)
                    ·
                      refine ⟨3910837086296982315373151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428898896791952840995069 3910837086296982315373151)
                      ·
                        rfl

theorem cell23_7616328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_7616328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616328 prefixEnd_7616328 := by exact prefixLift 7616328
  have htrace : WordTrace (prefixWord ++ tailWord_7616328) baseStart_7616328 baseEnd_7616328 := by
    simpa [prefixWord, tailWord_7616328, baseEnd_7616328] using wordTrace_append hprefix tailTrace_7616328
  have hstable : (prefixWord ++ tailWord_7616328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616328).length < 2 ^ (prefixWord ++ tailWord_7616328).sum := by decide
  have hdescent : baseEnd_7616328 < baseStart_7616328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616371 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_7616371 : Nat := 118140960795 + 7616371 * 2 ^ 59
def prefixEnd_7616371 : Nat := 4983230072969 + 3 ^ 40 * 7616371 * 2
def baseEnd_7616371 : Nat := 3910859165965125647135453

theorem tailTrace_7616371 : CollatzResearch.WordTrace tailWord_7616371 prefixEnd_7616371 3910859165965125647135453 := by
  unfold tailWord_7616371
  simp only [CollatzResearch.WordTrace]
  refine ⟨277791871890196114452112967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185194581260130742968075311 277791871890196114452112967)
  ·
    refine ⟨416687807835294171678169451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277791871890196114452112967 416687807835294171678169451)
    ·
      refine ⟨625031711752941257517254177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416687807835294171678169451 625031711752941257517254177)
      ·
        refine ⟨468773783814705943137940633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625031711752941257517254177 468773783814705943137940633)
        ·
          refine ⟨351580337861029457353455475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468773783814705943137940633 351580337861029457353455475)
          ·
            refine ⟨527370506791544186030183213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351580337861029457353455475 527370506791544186030183213)
            ·
              refine ⟨197763940046829069761318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527370506791544186030183213 197763940046829069761318705)
              ·
                refine ⟨148322955035121802320989029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197763940046829069761318705 148322955035121802320989029)
                ·
                  refine ⟨27810554069085337935185443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148322955035121802320989029 27810554069085337935185443)
                  ·
                    refine ⟨41715831103628006902778165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27810554069085337935185443 41715831103628006902778165)
                    ·
                      refine ⟨3910859165965125647135453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41715831103628006902778165 3910859165965125647135453)
                      ·
                        rfl

theorem cell23_7616371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_7616371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616371 prefixEnd_7616371 := by exact prefixLift 7616371
  have htrace : WordTrace (prefixWord ++ tailWord_7616371) baseStart_7616371 baseEnd_7616371 := by
    simpa [prefixWord, tailWord_7616371, baseEnd_7616371] using wordTrace_append hprefix tailTrace_7616371
  have hstable : (prefixWord ++ tailWord_7616371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616371).length < 2 ^ (prefixWord ++ tailWord_7616371).sum := by decide
  have hdescent : baseEnd_7616371 < baseStart_7616371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616388 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7616388 : Nat := 118140960795 + 7616388 * 2 ^ 59
def prefixEnd_7616388 : Nat := 4983230072969 + 3 ^ 40 * 7616388 * 2
def baseEnd_7616388 : Nat := 3910867895136252080622875

theorem tailTrace_7616388 : CollatzResearch.WordTrace tailWord_7616388 prefixEnd_7616388 3910867895136252080622875 := by
  unfold tailWord_7616388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138896245965567263177740909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185194994620756350903654545 138896245965567263177740909)
  ·
    refine ⟨52086092237087723691652841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138896245965567263177740909 52086092237087723691652841)
    ·
      refine ⟨39064569177815792768739631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52086092237087723691652841 39064569177815792768739631)
      ·
        refine ⟨58596853766723689153109447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39064569177815792768739631 58596853766723689153109447)
        ·
          refine ⟨87895280650085533729664171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58596853766723689153109447 87895280650085533729664171)
          ·
            refine ⟨131842920975128300594496257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87895280650085533729664171 131842920975128300594496257)
            ·
              refine ⟨98882190731346225445872193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131842920975128300594496257 98882190731346225445872193)
              ·
                refine ⟨74161643048509669084404145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98882190731346225445872193 74161643048509669084404145)
                ·
                  refine ⟨55621232286382251813303109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74161643048509669084404145 55621232286382251813303109)
                  ·
                    refine ⟨10428981053696672214994333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55621232286382251813303109 10428981053696672214994333)
                    ·
                      refine ⟨3910867895136252080622875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10428981053696672214994333 3910867895136252080622875)
                      ·
                        rfl

theorem cell23_7616388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7616388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616388 prefixEnd_7616388 := by exact prefixLift 7616388
  have htrace : WordTrace (prefixWord ++ tailWord_7616388) baseStart_7616388 baseEnd_7616388 := by
    simpa [prefixWord, tailWord_7616388, baseEnd_7616388] using wordTrace_append hprefix tailTrace_7616388
  have hstable : (prefixWord ++ tailWord_7616388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616388).length < 2 ^ (prefixWord ++ tailWord_7616388).sum := by decide
  have hdescent : baseEnd_7616388 < baseStart_7616388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616430 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7616430 : Nat := 118140960795 + 7616430 * 2 ^ 59
def prefixEnd_7616430 : Nat := 4983230072969 + 3 ^ 40 * 7616430 * 2
def baseEnd_7616430 : Nat := 3910889461323740916297683

theorem tailTrace_7616430 : CollatzResearch.WordTrace tailWord_7616430 prefixEnd_7616430 3910889461323740916297683 := by
  unfold tailWord_7616430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724252974622795941063843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185196015864654911685673829 34724252974622795941063843)
  ·
    refine ⟨52086379461934193911595765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724252974622795941063843 52086379461934193911595765)
    ·
      refine ⟨4883098074556330679212103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52086379461934193911595765 4883098074556330679212103)
      ·
        refine ⟨7324647111834496018818155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883098074556330679212103 7324647111834496018818155)
        ·
          refine ⟨10986970667751744028227233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324647111834496018818155 10986970667751744028227233)
          ·
            refine ⟨8240228000813808021170425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10986970667751744028227233 8240228000813808021170425)
            ·
              refine ⟨6180171000610356015877819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240228000813808021170425 6180171000610356015877819)
              ·
                refine ⟨9270256500915534023816729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180171000610356015877819 9270256500915534023816729)
                ·
                  refine ⟨6952692375686650517862547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270256500915534023816729 6952692375686650517862547)
                  ·
                    refine ⟨10429038563529975776793821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952692375686650517862547 10429038563529975776793821)
                    ·
                      refine ⟨3910889461323740916297683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429038563529975776793821 3910889461323740916297683)
                      ·
                        rfl

theorem cell23_7616430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7616430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616430 prefixEnd_7616430 := by exact prefixLift 7616430
  have htrace : WordTrace (prefixWord ++ tailWord_7616430) baseStart_7616430 baseEnd_7616430 := by
    simpa [prefixWord, tailWord_7616430, baseEnd_7616430] using wordTrace_append hprefix tailTrace_7616430
  have hstable : (prefixWord ++ tailWord_7616430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616430).length < 2 ^ (prefixWord ++ tailWord_7616430).sum := by decide
  have hdescent : baseEnd_7616430 < baseStart_7616430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616458 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_7616458 : Nat := 118140960795 + 7616458 * 2 ^ 59
def prefixEnd_7616458 : Nat := 4983230072969 + 3 ^ 40 * 7616458 * 2
def baseEnd_7616458 : Nat := 3910903838782066806747553

theorem tailTrace_7616458 : CollatzResearch.WordTrace tailWord_7616458 prefixEnd_7616458 3910903838782066806747553 := by
  unfold tailWord_7616458
  simp only [CollatzResearch.WordTrace]
  refine ⟨69448761260220232077632507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185196696693920618873686685 69448761260220232077632507)
  ·
    refine ⟨104173141890330348116448761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69448761260220232077632507 104173141890330348116448761)
    ·
      refine ⟨78129856417747761087336571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104173141890330348116448761 78129856417747761087336571)
      ·
        refine ⟨117194784626621641631004857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78129856417747761087336571 117194784626621641631004857)
        ·
          refine ⟨87896088469966231223253643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117194784626621641631004857 87896088469966231223253643)
          ·
            refine ⟨131844132704949346834880465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87896088469966231223253643 131844132704949346834880465)
            ·
              refine ⟨98883099528712010126160349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131844132704949346834880465 98883099528712010126160349)
              ·
                refine ⟨37081162323267003797310131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98883099528712010126160349 37081162323267003797310131)
                ·
                  refine ⟨55621743484900505695965197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37081162323267003797310131 55621743484900505695965197)
                  ·
                    refine ⟨20858153806837689635986949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55621743484900505695965197 20858153806837689635986949)
                    ·
                      refine ⟨3910903838782066806747553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20858153806837689635986949 3910903838782066806747553)
                      ·
                        rfl

theorem cell23_7616458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_7616458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616458 prefixEnd_7616458 := by exact prefixLift 7616458
  have htrace : WordTrace (prefixWord ++ tailWord_7616458) baseStart_7616458 baseEnd_7616458 := by
    simpa [prefixWord, tailWord_7616458, baseEnd_7616458] using wordTrace_append hprefix tailTrace_7616458
  have hstable : (prefixWord ++ tailWord_7616458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616458).length < 2 ^ (prefixWord ++ tailWord_7616458).sum := by decide
  have hdescent : baseEnd_7616458 < baseStart_7616458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616476 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 5]
def baseStart_7616476 : Nat := 118140960795 + 7616476 * 2 ^ 59
def prefixEnd_7616476 : Nat := 4983230072969 + 3 ^ 40 * 7616476 * 2
def baseEnd_7616476 : Nat := 434545897937094192924719

theorem tailTrace_7616476 : CollatzResearch.WordTrace tailWord_7616476 prefixEnd_7616476 434545897937094192924719 := by
  unfold tailWord_7616476
  simp only [CollatzResearch.WordTrace]
  refine ⟨138897850777407858692342641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185197134369877144923123521 138897850777407858692342641)
  ·
    refine ⟨104173388083055894019256981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138897850777407858692342641 104173388083055894019256981)
    ·
      refine ⟨4883127566393245032152671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104173388083055894019256981 4883127566393245032152671)
      ·
        refine ⟨7324691349589867548229007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883127566393245032152671 7324691349589867548229007)
        ·
          refine ⟨10987037024384801322343511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324691349589867548229007 10987037024384801322343511)
          ·
            refine ⟨16480555536577201983515267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987037024384801322343511 16480555536577201983515267)
            ·
              refine ⟨24720833304865802975272901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16480555536577201983515267 24720833304865802975272901)
              ·
                refine ⟨4635156244662338057863669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24720833304865802975272901 4635156244662338057863669)
                ·
                  refine ⟨434545897937094192924719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635156244662338057863669 434545897937094192924719)
                  ·
                    rfl

theorem cell23_7616476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_7616476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616476 prefixEnd_7616476 := by exact prefixLift 7616476
  have htrace : WordTrace (prefixWord ++ tailWord_7616476) baseStart_7616476 baseEnd_7616476 := by
    simpa [prefixWord, tailWord_7616476, baseEnd_7616476] using wordTrace_append hprefix tailTrace_7616476
  have hstable : (prefixWord ++ tailWord_7616476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616476).length < 2 ^ (prefixWord ++ tailWord_7616476).sum := by decide
  have hdescent : baseEnd_7616476 < baseStart_7616476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616488 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7616488 : Nat := 118140960795 + 7616488 * 2 ^ 59
def prefixEnd_7616488 : Nat := 4983230072969 + 3 ^ 40 * 7616488 * 2
def baseEnd_7616488 : Nat := 3910919243201701689372415

theorem tailTrace_7616488 : CollatzResearch.WordTrace tailWord_7616488 prefixEnd_7616488 3910919243201701689372415 := by
  unfold tailWord_7616488
  simp only [CollatzResearch.WordTrace]
  refine ⟨138898069615386121717061059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185197426153848162289414745 138898069615386121717061059)
  ·
    refine ⟨208347104423079182575591589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138898069615386121717061059 208347104423079182575591589)
    ·
      refine ⟨39065082079327346732923423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208347104423079182575591589 39065082079327346732923423)
      ·
        refine ⟨58597623118991020099385135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39065082079327346732923423 58597623118991020099385135)
        ·
          refine ⟨87896434678486530149077703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58597623118991020099385135 87896434678486530149077703)
          ·
            refine ⟨131844652017729795223616555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87896434678486530149077703 131844652017729795223616555)
            ·
              refine ⟨197766978026594692835424833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131844652017729795223616555 197766978026594692835424833)
              ·
                refine ⟨148325233519946019626568625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197766978026594692835424833 148325233519946019626568625)
                ·
                  refine ⟨111243925139959514719926469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148325233519946019626568625 111243925139959514719926469)
                  ·
                    refine ⟨20858235963742409009986213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111243925139959514719926469 20858235963742409009986213)
                    ·
                      refine ⟨3910919243201701689372415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20858235963742409009986213 3910919243201701689372415)
                      ·
                        rfl

theorem cell23_7616488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7616488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616488 prefixEnd_7616488 := by exact prefixLift 7616488
  have htrace : WordTrace (prefixWord ++ tailWord_7616488) baseStart_7616488 baseEnd_7616488 := by
    simpa [prefixWord, tailWord_7616488, baseEnd_7616488] using wordTrace_append hprefix tailTrace_7616488
  have hstable : (prefixWord ++ tailWord_7616488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616488).length < 2 ^ (prefixWord ++ tailWord_7616488).sum := by decide
  have hdescent : baseEnd_7616488 < baseStart_7616488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616519 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 1, 4]
def baseStart_7616519 : Nat := 118140960795 + 7616519 * 2 ^ 59
def prefixEnd_7616519 : Nat := 4983230072969 + 3 ^ 40 * 7616519 * 2
def baseEnd_7616519 : Nat := 1303645053700663689361591

theorem tailTrace_7616519 : CollatzResearch.WordTrace tailWord_7616519 prefixEnd_7616519 1303645053700663689361591 := by
  unfold tailWord_7616519
  simp only [CollatzResearch.WordTrace]
  refine ⟨277797269893659935728500611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185198179929106623819000407 277797269893659935728500611)
  ·
    refine ⟨416695904840489903592750917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277797269893659935728500611 416695904840489903592750917)
    ·
      refine ⟨78130482157591856923640797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416695904840489903592750917 78130482157591856923640797)
      ·
        refine ⟨29298930809096946346365299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78130482157591856923640797 29298930809096946346365299)
        ·
          refine ⟨43948396213645419519547949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29298930809096946346365299 43948396213645419519547949)
          ·
            refine ⟨16480648580117032319830481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43948396213645419519547949 16480648580117032319830481)
            ·
              refine ⟨12360486435087774239872861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16480648580117032319830481 12360486435087774239872861)
              ·
                refine ⟨4635182413157915339952323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12360486435087774239872861 4635182413157915339952323)
                ·
                  refine ⟨6952773619736873009928485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635182413157915339952323 6952773619736873009928485)
                  ·
                    refine ⟨1303645053700663689361591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952773619736873009928485 1303645053700663689361591)
                    ·
                      rfl

theorem cell23_7616519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_7616519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616519 prefixEnd_7616519 := by exact prefixLift 7616519
  have htrace : WordTrace (prefixWord ++ tailWord_7616519) baseStart_7616519 baseEnd_7616519 := by
    simpa [prefixWord, tailWord_7616519, baseEnd_7616519] using wordTrace_append hprefix tailTrace_7616519
  have hstable : (prefixWord ++ tailWord_7616519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616519).length < 2 ^ (prefixWord ++ tailWord_7616519).sum := by decide
  have hdescent : baseEnd_7616519 < baseStart_7616519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616562 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_7616562 : Nat := 118140960795 + 7616562 * 2 ^ 59
def prefixEnd_7616562 : Nat := 4983230072969 + 3 ^ 40 * 7616562 * 2
def baseEnd_7616562 : Nat := 1303652413590044799949025

theorem tailTrace_7616562 : CollatzResearch.WordTrace tailWord_7616562 prefixEnd_7616562 1303652413590044799949025 := by
  unfold tailWord_7616562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69449709558126038518078985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185199225488336102714877293 69449709558126038518078985)
  ·
    refine ⟨52087282168594528888559239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69449709558126038518078985 52087282168594528888559239)
    ·
      refine ⟨78130923252891793332838859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52087282168594528888559239 78130923252891793332838859)
      ·
        refine ⟨117196384879337689999258289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78130923252891793332838859 117196384879337689999258289)
        ·
          refine ⟨87897288659503267499443717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117196384879337689999258289 87897288659503267499443717)
          ·
            refine ⟨16480741623656862656145697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87897288659503267499443717 16480741623656862656145697)
            ·
              refine ⟨12360556217742646992109273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16480741623656862656145697 12360556217742646992109273)
              ·
                refine ⟨9270417163306985244081955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360556217742646992109273 9270417163306985244081955)
                ·
                  refine ⟨13905625744960477866122933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270417163306985244081955 13905625744960477866122933)
                  ·
                    refine ⟨1303652413590044799949025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13905625744960477866122933 1303652413590044799949025)
                    ·
                      rfl

theorem cell23_7616562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_7616562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616562 prefixEnd_7616562 := by exact prefixLift 7616562
  have htrace : WordTrace (prefixWord ++ tailWord_7616562) baseStart_7616562 baseEnd_7616562 := by
    simpa [prefixWord, tailWord_7616562, baseEnd_7616562] using wordTrace_append hprefix tailTrace_7616562
  have hstable : (prefixWord ++ tailWord_7616562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616562).length < 2 ^ (prefixWord ++ tailWord_7616562).sum := by decide
  have hdescent : baseEnd_7616562 < baseStart_7616562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616565 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7616565 : Nat := 118140960795 + 7616565 * 2 ^ 59
def prefixEnd_7616565 : Nat := 4983230072969 + 3 ^ 40 * 7616565 * 2
def baseEnd_7616565 : Nat := 3910958781212097888109561

theorem tailTrace_7616565 : CollatzResearch.WordTrace tailWord_7616565 prefixEnd_7616565 3910958781212097888109561 := by
  unfold tailWord_7616565
  simp only [CollatzResearch.WordTrace]
  refine ⟨277798947651493285584675149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185199298434328857056450099 277798947651493285584675149)
  ·
    refine ⟨104174605369309982094253181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277798947651493285584675149 104174605369309982094253181)
    ·
      refine ⟨39065477013491243285344943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104174605369309982094253181 39065477013491243285344943)
      ·
        refine ⟨58598215520236864928017415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39065477013491243285344943 58598215520236864928017415)
        ·
          refine ⟨87897323280355297392026123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58598215520236864928017415 87897323280355297392026123)
          ·
            refine ⟨131845984920532946088039185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87897323280355297392026123 131845984920532946088039185)
            ·
              refine ⟨98884488690399709566029389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131845984920532946088039185 98884488690399709566029389)
              ·
                refine ⟨37081683258899891087261021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98884488690399709566029389 37081683258899891087261021)
                ·
                  refine ⟨13905631222087459157722883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37081683258899891087261021 13905631222087459157722883)
                  ·
                    refine ⟨20858446833131188736584325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13905631222087459157722883 20858446833131188736584325)
                    ·
                      refine ⟨3910958781212097888109561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20858446833131188736584325 3910958781212097888109561)
                      ·
                        rfl

theorem cell23_7616565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7616565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616565 prefixEnd_7616565 := by exact prefixLift 7616565
  have htrace : WordTrace (prefixWord ++ tailWord_7616565) baseStart_7616565 baseEnd_7616565 := by
    simpa [prefixWord, tailWord_7616565, baseEnd_7616565] using wordTrace_append hprefix tailTrace_7616565
  have hstable : (prefixWord ++ tailWord_7616565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616565).length < 2 ^ (prefixWord ++ tailWord_7616565).sum := by decide
  have hdescent : baseEnd_7616565 < baseStart_7616565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616575 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 4, 4]
def baseStart_7616575 : Nat := 118140960795 + 7616575 * 2 ^ 59
def prefixEnd_7616575 : Nat := 4983230072969 + 3 ^ 40 * 7616575 * 2
def baseEnd_7616575 : Nat := 1303654638672880949661505

theorem tailTrace_7616575 : CollatzResearch.WordTrace tailWord_7616575 prefixEnd_7616575 1303654638672880949661505 := by
  unfold tailWord_7616575
  simp only [CollatzResearch.WordTrace]
  refine ⟨277799312381457057292539179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185199541587638038195026119 277799312381457057292539179)
  ·
    refine ⟨416698968572185585938808769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277799312381457057292539179 416698968572185585938808769)
    ·
      refine ⟨312524226429139189454106577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416698968572185585938808769 312524226429139189454106577)
      ·
        refine ⟨234393169821854392090579933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312524226429139189454106577 234393169821854392090579933)
        ·
          refine ⟨87897438683195397033967475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234393169821854392090579933 87897438683195397033967475)
          ·
            refine ⟨131846158024793095550951213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87897438683195397033967475 131846158024793095550951213)
            ·
              refine ⟨49442309259297410831606705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131846158024793095550951213 49442309259297410831606705)
              ·
                refine ⟨37081731944473058123705029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49442309259297410831606705 37081731944473058123705029)
                ·
                  refine ⟨6952824739588698398194693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37081731944473058123705029 6952824739588698398194693)
                  ·
                    refine ⟨1303654638672880949661505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952824739588698398194693 1303654638672880949661505)
                    ·
                      rfl

theorem cell23_7616575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_7616575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616575 prefixEnd_7616575 := by exact prefixLift 7616575
  have htrace : WordTrace (prefixWord ++ tailWord_7616575) baseStart_7616575 baseEnd_7616575 := by
    simpa [prefixWord, tailWord_7616575, baseEnd_7616575] using wordTrace_append hprefix tailTrace_7616575
  have hstable : (prefixWord ++ tailWord_7616575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616575).length < 2 ^ (prefixWord ++ tailWord_7616575).sum := by decide
  have hdescent : baseEnd_7616575 < baseStart_7616575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616576 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 1, 1, 3]
def baseStart_7616576 : Nat := 118140960795 + 7616576 * 2 ^ 59
def prefixEnd_7616576 : Nat := 4983230072969 + 3 ^ 40 * 7616576 * 2
def baseEnd_7616576 : Nat := 3910964429499297345072011

theorem tailTrace_7616576 : CollatzResearch.WordTrace tailWord_7616576 prefixEnd_7616576 3910964429499297345072011 := by
  unfold tailWord_7616576
  simp only [CollatzResearch.WordTrace]
  refine ⟨138899674427226717231662791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185199565902968956308883721 138899674427226717231662791)
  ·
    refine ⟨208349511640840075847494187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138899674427226717231662791 208349511640840075847494187)
    ·
      refine ⟨312524267461260113771241281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208349511640840075847494187 312524267461260113771241281)
      ·
        refine ⟨234393200595945085328430961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312524267461260113771241281 234393200595945085328430961)
        ·
          refine ⟨175794900446958813996323221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234393200595945085328430961 175794900446958813996323221)
          ·
            refine ⟨8240385958451194406077651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175794900446958813996323221 8240385958451194406077651)
            ·
              refine ⟨12360578937676791609116477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240385958451194406077651 12360578937676791609116477)
              ·
                refine ⟨4635217101628796853418679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12360578937676791609116477 4635217101628796853418679)
                ·
                  refine ⟨6952825652443195280128019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635217101628796853418679 6952825652443195280128019)
                  ·
                    refine ⟨10429238478664792920192029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952825652443195280128019 10429238478664792920192029)
                    ·
                      refine ⟨3910964429499297345072011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429238478664792920192029 3910964429499297345072011)
                      ·
                        rfl

theorem cell23_7616576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_7616576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616576 prefixEnd_7616576 := by exact prefixLift 7616576
  have htrace : WordTrace (prefixWord ++ tailWord_7616576) baseStart_7616576 baseEnd_7616576 := by
    simpa [prefixWord, tailWord_7616576, baseEnd_7616576] using wordTrace_append hprefix tailTrace_7616576
  have hstable : (prefixWord ++ tailWord_7616576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616576).length < 2 ^ (prefixWord ++ tailWord_7616576).sum := by decide
  have hdescent : baseEnd_7616576 < baseStart_7616576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616585 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_7616585 : Nat := 118140960795 + 7616585 * 2 ^ 59
def prefixEnd_7616585 : Nat := 4983230072969 + 3 ^ 40 * 7616585 * 2
def baseEnd_7616585 : Nat := 3910969050825187809859469

theorem tailTrace_7616585 : CollatzResearch.WordTrace tailWord_7616585 prefixEnd_7616585 3910969050825187809859469 := by
  unfold tailWord_7616585
  simp only [CollatzResearch.WordTrace]
  refine ⟨277799677111420829000403209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185199784740947219333602139 277799677111420829000403209)
  ·
    refine ⟨208349757833565621750302407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277799677111420829000403209 208349757833565621750302407)
    ·
      refine ⟨312524636750348432625453611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208349757833565621750302407 312524636750348432625453611)
      ·
        refine ⟨468786955125522648938180417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312524636750348432625453611 468786955125522648938180417)
        ·
          refine ⟨351590216344141986703635313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468786955125522648938180417 351590216344141986703635313)
          ·
            refine ⟨263692662258106490027726485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351590216344141986703635313 263692662258106490027726485)
            ·
              refine ⟨12360593543348741720049679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263692662258106490027726485 12360593543348741720049679)
              ·
                refine ⟨18540890315023112580074519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12360593543348741720049679 18540890315023112580074519)
                ·
                  refine ⟨27811335472534668870111779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18540890315023112580074519 27811335472534668870111779)
                  ·
                    refine ⟨41717003208802003305167669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27811335472534668870111779 41717003208802003305167669)
                    ·
                      refine ⟨3910969050825187809859469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41717003208802003305167669 3910969050825187809859469)
                      ·
                        rfl

theorem cell23_7616585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_7616585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616585 prefixEnd_7616585 := by exact prefixLift 7616585
  have htrace : WordTrace (prefixWord ++ tailWord_7616585) baseStart_7616585 baseEnd_7616585 := by
    simpa [prefixWord, tailWord_7616585, baseEnd_7616585] using wordTrace_append hprefix tailTrace_7616585
  have hstable : (prefixWord ++ tailWord_7616585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616585).length < 2 ^ (prefixWord ++ tailWord_7616585).sum := by decide
  have hdescent : baseEnd_7616585 < baseStart_7616585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616588 : List Nat := [2, 2, 1, 3, 1, 1, 13]
def baseStart_7616588 : Nat := 118140960795 + 7616588 * 2 ^ 59
def prefixEnd_7616588 : Nat := 4983230072969 + 3 ^ 40 * 7616588 * 2
def baseEnd_7616588 : Nat := 48283587546508040717555

theorem tailTrace_7616588 : CollatzResearch.WordTrace tailWord_7616588 prefixEnd_7616588 48283587546508040717555 := by
  unfold tailWord_7616588
  simp only [CollatzResearch.WordTrace]
  refine ⟨138899893265204980256381209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185199857686939973675174945 138899893265204980256381209)
  ·
    refine ⟨104174919948903735192285907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138899893265204980256381209 104174919948903735192285907)
    ·
      refine ⟨156262379923355602788428861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104174919948903735192285907 156262379923355602788428861)
      ·
        refine ⟨58598392471258351045660823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156262379923355602788428861 58598392471258351045660823)
        ·
          refine ⟨87897588706887526568491235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58598392471258351045660823 87897588706887526568491235)
          ·
            refine ⟨131846383060331289852736853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87897588706887526568491235 131846383060331289852736853)
            ·
              refine ⟨48283587546508040717555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 131846383060331289852736853 48283587546508040717555)
              ·
                rfl

theorem cell23_7616588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 13].length) (baseStart_7616588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616588 prefixEnd_7616588 := by exact prefixLift 7616588
  have htrace : WordTrace (prefixWord ++ tailWord_7616588) baseStart_7616588 baseEnd_7616588 := by
    simpa [prefixWord, tailWord_7616588, baseEnd_7616588] using wordTrace_append hprefix tailTrace_7616588
  have hstable : (prefixWord ++ tailWord_7616588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616588).length < 2 ^ (prefixWord ++ tailWord_7616588).sum := by decide
  have hdescent : baseEnd_7616588 < baseStart_7616588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616599 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_7616599 : Nat := 118140960795 + 7616599 * 2 ^ 59
def prefixEnd_7616599 : Nat := 4983230072969 + 3 ^ 40 * 7616599 * 2
def baseEnd_7616599 : Nat := 3910976239554350755084405

theorem tailTrace_7616599 : CollatzResearch.WordTrace tailWord_7616599 prefixEnd_7616599 3910976239554350755084405 := by
  unfold tailWord_7616599
  simp only [CollatzResearch.WordTrace]
  refine ⟨277800187733370109391412851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185200125155580072927608567 277800187733370109391412851)
  ·
    refine ⟨416700281600055164087119277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277800187733370109391412851 416700281600055164087119277)
    ·
      refine ⟨156262605600020686532669729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416700281600055164087119277 156262605600020686532669729)
      ·
        refine ⟨117196954200015514899502297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156262605600020686532669729 117196954200015514899502297)
        ·
          refine ⟨87897715650011636174626723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117196954200015514899502297 87897715650011636174626723)
          ·
            refine ⟨131846573475017454261940085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87897715650011636174626723 131846573475017454261940085)
            ·
              refine ⟨12360616263282886337056883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131846573475017454261940085 12360616263282886337056883)
              ·
                refine ⟨18540924394924329505585325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12360616263282886337056883 18540924394924329505585325)
                ·
                  refine ⟨6952846648096623564594497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18540924394924329505585325 6952846648096623564594497)
                  ·
                    refine ⟨5214634986072467673445873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6952846648096623564594497 5214634986072467673445873)
                    ·
                      refine ⟨3910976239554350755084405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214634986072467673445873 3910976239554350755084405)
                      ·
                        rfl

theorem cell23_7616599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_7616599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616599 prefixEnd_7616599 := by exact prefixLift 7616599
  have htrace : WordTrace (prefixWord ++ tailWord_7616599) baseStart_7616599 baseEnd_7616599 := by
    simpa [prefixWord, tailWord_7616599, baseEnd_7616599] using wordTrace_append hprefix tailTrace_7616599
  have hstable : (prefixWord ++ tailWord_7616599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616599).length < 2 ^ (prefixWord ++ tailWord_7616599).sum := by decide
  have hdescent : baseEnd_7616599 < baseStart_7616599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616649 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_7616649 : Nat := 118140960795 + 7616649 * 2 ^ 59
def prefixEnd_7616649 : Nat := 4983230072969 + 3 ^ 40 * 7616649 * 2
def baseEnd_7616649 : Nat := 3911001913587075559459175

theorem tailTrace_7616649 : CollatzResearch.WordTrace tailWord_7616649 prefixEnd_7616649 3911001913587075559459175 := by
  unfold tailWord_7616649
  simp only [CollatzResearch.WordTrace]
  refine ⟨277802011383188967930733001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185201340922125978620488667 277802011383188967930733001)
  ·
    refine ⟨208351508537391725948049751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277802011383188967930733001 208351508537391725948049751)
    ·
      refine ⟨312527262806087588922074627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208351508537391725948049751 312527262806087588922074627)
      ·
        refine ⟨468790894209131383383111941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312527262806087588922074627 468790894209131383383111941)
        ·
          refine ⟨87898292664212134384333489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468790894209131383383111941 87898292664212134384333489)
          ·
            refine ⟨65923719498159100788250117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87898292664212134384333489 65923719498159100788250117)
            ·
              refine ⟨12360697405904831397796897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65923719498159100788250117 12360697405904831397796897)
              ·
                refine ⟨9270523054428623548347673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360697405904831397796897 9270523054428623548347673)
                ·
                  refine ⟨6952892290821467661260755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270523054428623548347673 6952892290821467661260755)
                  ·
                    refine ⟨10429338436232201491891133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952892290821467661260755 10429338436232201491891133)
                    ·
                      refine ⟨3911001913587075559459175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429338436232201491891133 3911001913587075559459175)
                      ·
                        rfl

theorem cell23_7616649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_7616649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616649 prefixEnd_7616649 := by exact prefixLift 7616649
  have htrace : WordTrace (prefixWord ++ tailWord_7616649) baseStart_7616649 baseEnd_7616649 := by
    simpa [prefixWord, tailWord_7616649, baseEnd_7616649] using wordTrace_append hprefix tailTrace_7616649
  have hstable : (prefixWord ++ tailWord_7616649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616649).length < 2 ^ (prefixWord ++ tailWord_7616649).sum := by decide
  have hdescent : baseEnd_7616649 < baseStart_7616649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616650 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_7616650 : Nat := 118140960795 + 7616650 * 2 ^ 59
def prefixEnd_7616650 : Nat := 4983230072969 + 3 ^ 40 * 7616650 * 2
def baseEnd_7616650 : Nat := 3911002427067730055546671

theorem tailTrace_7616650 : CollatzResearch.WordTrace tailWord_7616650 prefixEnd_7616650 3911002427067730055546671 := by
  unfold tailWord_7616650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69450511964046336275379851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185201365237456896734346269 69450511964046336275379851)
  ·
    refine ⟨104175767946069504413069777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69450511964046336275379851 104175767946069504413069777)
    ·
      refine ⟨78131825959552128309802333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104175767946069504413069777 78131825959552128309802333)
      ·
        refine ⟨29299434734832048116175875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78131825959552128309802333 29299434734832048116175875)
        ·
          refine ⟨43949152102248072174263813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29299434734832048116175875 43949152102248072174263813)
          ·
            refine ⟨8240466019171513532674465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43949152102248072174263813 8240466019171513532674465)
            ·
              refine ⟨6180349514378635149505849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240466019171513532674465 6180349514378635149505849)
              ·
                refine ⟨4635262135783976362129387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180349514378635149505849 4635262135783976362129387)
                ·
                  refine ⟨6952893203675964543194081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635262135783976362129387 6952893203675964543194081)
                  ·
                    refine ⟨5214669902756973407395561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6952893203675964543194081 5214669902756973407395561)
                    ·
                      refine ⟨3911002427067730055546671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214669902756973407395561 3911002427067730055546671)
                      ·
                        rfl

theorem cell23_7616650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_7616650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616650 prefixEnd_7616650 := by exact prefixLift 7616650
  have htrace : WordTrace (prefixWord ++ tailWord_7616650) baseStart_7616650 baseEnd_7616650 := by
    simpa [prefixWord, tailWord_7616650, baseEnd_7616650] using wordTrace_append hprefix tailTrace_7616650
  have hstable : (prefixWord ++ tailWord_7616650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616650).length < 2 ^ (prefixWord ++ tailWord_7616650).sum := by decide
  have hdescent : baseEnd_7616650 < baseStart_7616650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616693 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7616693 : Nat := 118140960795 + 7616693 * 2 ^ 59
def prefixEnd_7616693 : Nat := 4983230072969 + 3 ^ 40 * 7616693 * 2
def baseEnd_7616693 : Nat := 3911024506735873387308973

theorem tailTrace_7616693 : CollatzResearch.WordTrace tailWord_7616693 prefixEnd_7616693 3911024506735873387308973 := by
  unfold tailWord_7616693
  simp only [CollatzResearch.WordTrace]
  refine ⟨277803616195029563445334733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185202410796686375630223155 277803616195029563445334733)
  ·
    refine ⟨104176356073136086292000525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277803616195029563445334733 104176356073136086292000525)
    ·
      refine ⟨39066133527426032359500197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104176356073136086292000525 39066133527426032359500197)
      ·
        refine ⟨7324900036392381067406287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39066133527426032359500197 7324900036392381067406287)
        ·
          refine ⟨10987350054588571601109431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324900036392381067406287 10987350054588571601109431)
          ·
            refine ⟨16481025081882857401664147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987350054588571601109431 16481025081882857401664147)
            ·
              refine ⟨24721537622824286102496221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16481025081882857401664147 24721537622824286102496221)
              ·
                refine ⟨9270576608559107288436083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24721537622824286102496221 9270576608559107288436083)
                ·
                  refine ⟨13905864912838660932654125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270576608559107288436083 13905864912838660932654125)
                  ·
                    refine ⟨5214699342314497849745297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13905864912838660932654125 5214699342314497849745297)
                    ·
                      refine ⟨3911024506735873387308973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214699342314497849745297 3911024506735873387308973)
                      ·
                        rfl

theorem cell23_7616693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7616693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616693 prefixEnd_7616693 := by exact prefixLift 7616693
  have htrace : WordTrace (prefixWord ++ tailWord_7616693) baseStart_7616693 baseEnd_7616693 := by
    simpa [prefixWord, tailWord_7616693, baseEnd_7616693] using wordTrace_append hprefix tailTrace_7616693
  have hstable : (prefixWord ++ tailWord_7616693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616693).length < 2 ^ (prefixWord ++ tailWord_7616693).sum := by decide
  have hdescent : baseEnd_7616693 < baseStart_7616693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616735 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_7616735 : Nat := 118140960795 + 7616735 * 2 ^ 59
def prefixEnd_7616735 : Nat := 4983230072969 + 3 ^ 40 * 7616735 * 2
def baseEnd_7616735 : Nat := 3911046072923362222983779

theorem tailTrace_7616735 : CollatzResearch.WordTrace tailWord_7616735 prefixEnd_7616735 3911046072923362222983779 := by
  unfold tailWord_7616735
  simp only [CollatzResearch.WordTrace]
  refine ⟨277805148060877404618363659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185203432040584936412242439 277805148060877404618363659)
  ·
    refine ⟨416707722091316106927545489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277805148060877404618363659 416707722091316106927545489)
    ·
      refine ⟨312530791568487080195659117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416707722091316106927545489 312530791568487080195659117)
      ·
        refine ⟨117199046838182655073372169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312530791568487080195659117 117199046838182655073372169)
        ·
          refine ⟨87899285128636991305029127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117199046838182655073372169 87899285128636991305029127)
          ·
            refine ⟨131848927692955486957543691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87899285128636991305029127 131848927692955486957543691)
            ·
              refine ⟨197773391539433230436315537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131848927692955486957543691 197773391539433230436315537)
              ·
                refine ⟨148330043654574922827236653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197773391539433230436315537 148330043654574922827236653)
                ·
                  refine ⟨55623766370465596060213745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148330043654574922827236653 55623766370465596060213745)
                  ·
                    refine ⟨41717824777849197045160309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55623766370465596060213745 41717824777849197045160309)
                    ·
                      refine ⟨3911046072923362222983779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41717824777849197045160309 3911046072923362222983779)
                      ·
                        rfl

theorem cell23_7616735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_7616735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616735 prefixEnd_7616735 := by exact prefixLift 7616735
  have htrace : WordTrace (prefixWord ++ tailWord_7616735) baseStart_7616735 baseEnd_7616735 := by
    simpa [prefixWord, tailWord_7616735, baseEnd_7616735] using wordTrace_append hprefix tailTrace_7616735
  have hstable : (prefixWord ++ tailWord_7616735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616735).length < 2 ^ (prefixWord ++ tailWord_7616735).sum := by decide
  have hdescent : baseEnd_7616735 < baseStart_7616735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616762 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_7616762 : Nat := 118140960795 + 7616762 * 2 ^ 59
def prefixEnd_7616762 : Nat := 4983230072969 + 3 ^ 40 * 7616762 * 2
def baseEnd_7616762 : Nat := 3911059936901033617346155

theorem tailTrace_7616762 : CollatzResearch.WordTrace tailWord_7616762 prefixEnd_7616762 3911059936901033617346155 := by
  unfold tailWord_7616762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69451533207944897057399135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185204088554519725486397693 69451533207944897057399135)
  ·
    refine ⟨104177299811917345586098703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69451533207944897057399135 104177299811917345586098703)
    ·
      refine ⟨156265949717876018379148055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104177299811917345586098703 156265949717876018379148055)
      ·
        refine ⟨234398924576814027568722083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156265949717876018379148055 234398924576814027568722083)
        ·
          refine ⟨351598386865221041353083125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234398924576814027568722083 351598386865221041353083125)
          ·
            refine ⟨32962348768614472626851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351598386865221041353083125 32962348768614472626851543)
            ·
              refine ⟨49443523152921708940277315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32962348768614472626851543 49443523152921708940277315)
              ·
                refine ⟨74165284729382563410415973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49443523152921708940277315 74165284729382563410415973)
                ·
                  refine ⟨13905990886759230639452995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74165284729382563410415973 13905990886759230639452995)
                  ·
                    refine ⟨20858986330138845959179493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13905990886759230639452995 20858986330138845959179493)
                    ·
                      refine ⟨3911059936901033617346155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20858986330138845959179493 3911059936901033617346155)
                      ·
                        rfl

theorem cell23_7616762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_7616762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616762 prefixEnd_7616762 := by exact prefixLift 7616762
  have htrace : WordTrace (prefixWord ++ tailWord_7616762) baseStart_7616762 baseEnd_7616762 := by
    simpa [prefixWord, tailWord_7616762, baseEnd_7616762] using wordTrace_append hprefix tailTrace_7616762
  have hstable : (prefixWord ++ tailWord_7616762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616762).length < 2 ^ (prefixWord ++ tailWord_7616762).sum := by decide
  have hdescent : baseEnd_7616762 < baseStart_7616762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616799 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_7616799 : Nat := 118140960795 + 7616799 * 2 ^ 59
def prefixEnd_7616799 : Nat := 4983230072969 + 3 ^ 40 * 7616799 * 2
def baseEnd_7616799 : Nat := 3911078935685249972583485

theorem tailTrace_7616799 : CollatzResearch.WordTrace tailWord_7616799 prefixEnd_7616799 3911078935685249972583485 := by
  unfold tailWord_7616799
  simp only [CollatzResearch.WordTrace]
  refine ⟨277807482332645543548693451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185204988221763695699128967 277807482332645543548693451)
  ·
    refine ⟨416711223498968315323040177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277807482332645543548693451 416711223498968315323040177)
    ·
      refine ⟨312533417624226236492280133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416711223498968315323040177 312533417624226236492280133)
      ·
        refine ⟨58600015804542419342302525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312533417624226236492280133 58600015804542419342302525)
        ·
          refine ⟨21975005926703407253363447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58600015804542419342302525 21975005926703407253363447)
          ·
            refine ⟨32962508890055110880045171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975005926703407253363447 32962508890055110880045171)
            ·
              refine ⟨49443763335082666320067757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32962508890055110880045171 49443763335082666320067757)
              ·
                refine ⟨18541411250655999870025409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49443763335082666320067757 18541411250655999870025409)
                ·
                  refine ⟨13906058437991999902519057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18541411250655999870025409 13906058437991999902519057)
                  ·
                    refine ⟨10429543828493999926889293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13906058437991999902519057 10429543828493999926889293)
                    ·
                      refine ⟨3911078935685249972583485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429543828493999926889293 3911078935685249972583485)
                      ·
                        rfl

theorem cell23_7616799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_7616799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616799 prefixEnd_7616799 := by exact prefixLift 7616799
  have htrace : WordTrace (prefixWord ++ tailWord_7616799) baseStart_7616799 baseEnd_7616799 := by
    simpa [prefixWord, tailWord_7616799, baseEnd_7616799] using wordTrace_append hprefix tailTrace_7616799
  have hstable : (prefixWord ++ tailWord_7616799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616799).length < 2 ^ (prefixWord ++ tailWord_7616799).sum := by decide
  have hdescent : baseEnd_7616799 < baseStart_7616799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616839 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_7616839 : Nat := 118140960795 + 7616839 * 2 ^ 59
def prefixEnd_7616839 : Nat := 4983230072969 + 3 ^ 40 * 7616839 * 2
def baseEnd_7616839 : Nat := 3911099474911429816083301

theorem tailTrace_7616839 : CollatzResearch.WordTrace tailWord_7616839 prefixEnd_7616839 3911099474911429816083301 := by
  unfold tailWord_7616839
  simp only [CollatzResearch.WordTrace]
  refine ⟨277808941252500630380149571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185205960835000420253433047 277808941252500630380149571)
  ·
    refine ⟨416713411878750945570224357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277808941252500630380149571 416713411878750945570224357)
    ·
      refine ⟨78133764727265802294417067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416713411878750945570224357 78133764727265802294417067)
      ·
        refine ⟨117200647090898703441625601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78133764727265802294417067 117200647090898703441625601)
        ·
          refine ⟨87900485318174027581219201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117200647090898703441625601 87900485318174027581219201)
          ·
            refine ⟨65925363988630520685914401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87900485318174027581219201 65925363988630520685914401)
            ·
              refine ⟨49444022991472890514435801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65925363988630520685914401 49444022991472890514435801)
              ·
                refine ⟨37083017243604667885826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49444022991472890514435801 37083017243604667885826851)
                ·
                  refine ⟨55624525865407001828740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37083017243604667885826851 55624525865407001828740277)
                  ·
                    refine ⟨5214799299881906421444401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55624525865407001828740277 5214799299881906421444401)
                    ·
                      refine ⟨3911099474911429816083301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214799299881906421444401 3911099474911429816083301)
                      ·
                        rfl

theorem cell23_7616839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_7616839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616839 prefixEnd_7616839 := by exact prefixLift 7616839
  have htrace : WordTrace (prefixWord ++ tailWord_7616839) baseStart_7616839 baseEnd_7616839 := by
    simpa [prefixWord, tailWord_7616839, baseEnd_7616839] using wordTrace_append hprefix tailTrace_7616839
  have hstable : (prefixWord ++ tailWord_7616839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616839).length < 2 ^ (prefixWord ++ tailWord_7616839).sum := by decide
  have hdescent : baseEnd_7616839 < baseStart_7616839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616866 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7616866 : Nat := 118140960795 + 7616866 * 2 ^ 59
def prefixEnd_7616866 : Nat := 4983230072969 + 3 ^ 40 * 7616866 * 2
def baseEnd_7616866 : Nat := 1303704446296367070148559

theorem tailTrace_7616866 : CollatzResearch.WordTrace tailWord_7616866 prefixEnd_7616866 1303704446296367070148559 := by
  unfold tailWord_7616866
  simp only [CollatzResearch.WordTrace]
  refine ⟨69452481505850703497845613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185206617348935209327588301 69452481505850703497845613)
  ·
    refine ⟨26044680564694013811692105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69452481505850703497845613 26044680564694013811692105)
    ·
      refine ⟨19533510423520510358769079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26044680564694013811692105 19533510423520510358769079)
      ·
        refine ⟨29300265635280765538153619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19533510423520510358769079 29300265635280765538153619)
        ·
          refine ⟨43950398452921148307230429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29300265635280765538153619 43950398452921148307230429)
          ·
            refine ⟨16481399419845430615211411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43950398452921148307230429 16481399419845430615211411)
            ·
              refine ⟨24722099129768145922817117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16481399419845430615211411 24722099129768145922817117)
              ·
                refine ⟨9270787173663054721056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24722099129768145922817117 9270787173663054721056419)
                ·
                  refine ⟨13906180760494582081584629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270787173663054721056419 13906180760494582081584629)
                  ·
                    refine ⟨1303704446296367070148559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13906180760494582081584629 1303704446296367070148559)
                    ·
                      rfl

theorem cell23_7616866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7616866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616866 prefixEnd_7616866 := by exact prefixLift 7616866
  have htrace : WordTrace (prefixWord ++ tailWord_7616866) baseStart_7616866 baseEnd_7616866 := by
    simpa [prefixWord, tailWord_7616866, baseEnd_7616866] using wordTrace_append hprefix tailTrace_7616866
  have hstable : (prefixWord ++ tailWord_7616866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616866).length < 2 ^ (prefixWord ++ tailWord_7616866).sum := by decide
  have hdescent : baseEnd_7616866 < baseStart_7616866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616879 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 2, 4]
def baseStart_7616879 : Nat := 118140960795 + 7616879 * 2 ^ 59
def prefixEnd_7616879 : Nat := 4983230072969 + 3 ^ 40 * 7616879 * 2
def baseEnd_7616879 : Nat := 1303706671379203219861039

theorem tailTrace_7616879 : CollatzResearch.WordTrace tailWord_7616879 prefixEnd_7616879 1303706671379203219861039 := by
  unfold tailWord_7616879
  simp only [CollatzResearch.WordTrace]
  refine ⟨277810400172355717211605691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185206933448237144807737127 277810400172355717211605691)
  ·
    refine ⟨416715600258533575817408537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277810400172355717211605691 416715600258533575817408537)
    ·
      refine ⟨312536700193900181863056403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416715600258533575817408537 312536700193900181863056403)
      ·
        refine ⟨468805050290850272794584605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312536700193900181863056403 468805050290850272794584605)
        ·
          refine ⟨175801893859068852297969227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468805050290850272794584605 175801893859068852297969227)
          ·
            refine ⟨263702840788603278446953841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175801893859068852297969227 263702840788603278446953841)
            ·
              refine ⟨197777130591452458835215381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263702840788603278446953841 197777130591452458835215381)
              ·
                refine ⟨9270802996474334007900721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197777130591452458835215381 9270802996474334007900721)
                ·
                  refine ⟨6953102247355750505925541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270802996474334007900721 6953102247355750505925541)
                  ·
                    refine ⟨1303706671379203219861039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953102247355750505925541 1303706671379203219861039)
                    ·
                      rfl

theorem cell23_7616879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_7616879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616879 prefixEnd_7616879 := by exact prefixLift 7616879
  have htrace : WordTrace (prefixWord ++ tailWord_7616879) baseStart_7616879 baseEnd_7616879 := by
    simpa [prefixWord, tailWord_7616879, baseEnd_7616879] using wordTrace_append hprefix tailTrace_7616879
  have hstable : (prefixWord ++ tailWord_7616879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616879).length < 2 ^ (prefixWord ++ tailWord_7616879).sum := by decide
  have hdescent : baseEnd_7616879 < baseStart_7616879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616899 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6]
def baseStart_7616899 : Nat := 118140960795 + 7616899 * 2 ^ 59
def prefixEnd_7616899 : Nat := 4983230072969 + 3 ^ 40 * 7616899 * 2
def baseEnd_7616899 : Nat := 3911130283750699581333025

theorem tailTrace_7616899 : CollatzResearch.WordTrace tailWord_7616899 prefixEnd_7616899 3911130283750699581333025 := by
  unfold tailWord_7616899
  simp only [CollatzResearch.WordTrace]
  refine ⟨277811129632283260627333751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185207419754855507084889167 277811129632283260627333751)
  ·
    refine ⟨416716694448424890941000627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277811129632283260627333751 416716694448424890941000627)
    ·
      refine ⟨625075041672637336411500941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416716694448424890941000627 625075041672637336411500941)
      ·
        refine ⟨234403140627239001154312853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625075041672637336411500941 234403140627239001154312853)
        ·
          refine ⟨10987647216901828179108415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234403140627239001154312853 10987647216901828179108415)
          ·
            refine ⟨16481470825352742268662623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987647216901828179108415 16481470825352742268662623)
            ·
              refine ⟨24722206238029113402993935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16481470825352742268662623 24722206238029113402993935)
              ·
                refine ⟨37083309357043670104490903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24722206238029113402993935 37083309357043670104490903)
                ·
                  refine ⟨55624964035565505156736355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37083309357043670104490903 55624964035565505156736355)
                  ·
                    refine ⟨83437446053348257735104533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55624964035565505156736355 83437446053348257735104533)
                    ·
                      refine ⟨3911130283750699581333025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83437446053348257735104533 3911130283750699581333025)
                      ·
                        rfl

theorem cell23_7616899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_7616899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616899 prefixEnd_7616899 := by exact prefixLift 7616899
  have htrace : WordTrace (prefixWord ++ tailWord_7616899) baseStart_7616899 baseEnd_7616899 := by
    simpa [prefixWord, tailWord_7616899, baseEnd_7616899] using wordTrace_append hprefix tailTrace_7616899
  have hstable : (prefixWord ++ tailWord_7616899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616899).length < 2 ^ (prefixWord ++ tailWord_7616899).sum := by decide
  have hdescent : baseEnd_7616899 < baseStart_7616899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616919 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_7616919 : Nat := 118140960795 + 7616919 * 2 ^ 59
def prefixEnd_7616919 : Nat := 4983230072969 + 3 ^ 40 * 7616919 * 2
def baseEnd_7616919 : Nat := 3911140553363789503082933

theorem tailTrace_7616919 : CollatzResearch.WordTrace tailWord_7616919 prefixEnd_7616919 3911140553363789503082933 := by
  unfold tailWord_7616919
  simp only [CollatzResearch.WordTrace]
  refine ⟨277811859092210804043061811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185207906061473869362041207 277811859092210804043061811)
  ·
    refine ⟨416717788638316206064592717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277811859092210804043061811 416717788638316206064592717)
    ·
      refine ⟨156269170739368577274222269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416717788638316206064592717 156269170739368577274222269)
      ·
        refine ⟨58600939027263216477833351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156269170739368577274222269 58600939027263216477833351)
        ·
          refine ⟨87901408540894824716750027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58600939027263216477833351 87901408540894824716750027)
          ·
            refine ⟨131852112811342237075125041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87901408540894824716750027 131852112811342237075125041)
            ·
              refine ⟨98889084608506677806343781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131852112811342237075125041 98889084608506677806343781)
              ·
                refine ⟨18541703364095002088689459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98889084608506677806343781 18541703364095002088689459)
                ·
                  refine ⟨27812555046142503133034189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18541703364095002088689459 27812555046142503133034189)
                  ·
                    refine ⟨10429708142303438674887821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27812555046142503133034189 10429708142303438674887821)
                    ·
                      refine ⟨3911140553363789503082933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429708142303438674887821 3911140553363789503082933)
                      ·
                        rfl

theorem cell23_7616919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_7616919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616919 prefixEnd_7616919 := by exact prefixLift 7616919
  have htrace : WordTrace (prefixWord ++ tailWord_7616919) baseStart_7616919 baseEnd_7616919 := by
    simpa [prefixWord, tailWord_7616919, baseEnd_7616919] using wordTrace_append hprefix tailTrace_7616919
  have hstable : (prefixWord ++ tailWord_7616919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616919).length < 2 ^ (prefixWord ++ tailWord_7616919).sum := by decide
  have hdescent : baseEnd_7616919 < baseStart_7616919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616926 : List Nat := [4, 3, 1, 2, 1, 3, 9]
def baseStart_7616926 : Nat := 118140960795 + 7616926 * 2 ^ 59
def prefixEnd_7616926 : Nat := 4983230072969 + 3 ^ 40 * 7616926 * 2
def baseEnd_7616926 : Nat := 48285730218868777477721

theorem tailTrace_7616926 : CollatzResearch.WordTrace tailWord_7616926 prefixEnd_7616926 48285730218868777477721 := by
  unfold tailWord_7616926
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726514300398180529820829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185208076268790296159044421 34726514300398180529820829)
  ·
    refine ⟨13022442862649317698682811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34726514300398180529820829 13022442862649317698682811)
    ·
      refine ⟨19533664293973976548024217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13022442862649317698682811 19533664293973976548024217)
      ·
        refine ⟨14650248220480482411018163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19533664293973976548024217 14650248220480482411018163)
        ·
          refine ⟨21975372330720723616527245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14650248220480482411018163 21975372330720723616527245)
          ·
            refine ⟨8240764624020271356197717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21975372330720723616527245 8240764624020271356197717)
            ·
              refine ⟨48285730218868777477721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8240764624020271356197717 48285730218868777477721)
              ·
                rfl

theorem cell23_7616926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 9].length) (baseStart_7616926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616926 prefixEnd_7616926 := by exact prefixLift 7616926
  have htrace : WordTrace (prefixWord ++ tailWord_7616926) baseStart_7616926 baseEnd_7616926 := by
    simpa [prefixWord, tailWord_7616926, baseEnd_7616926] using wordTrace_append hprefix tailTrace_7616926
  have hstable : (prefixWord ++ tailWord_7616926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616926).length < 2 ^ (prefixWord ++ tailWord_7616926).sum := by decide
  have hdescent : baseEnd_7616926 < baseStart_7616926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616946 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_7616946 : Nat := 118140960795 + 7616946 * 2 ^ 59
def prefixEnd_7616946 : Nat := 4983230072969 + 3 ^ 40 * 7616946 * 2
def baseEnd_7616946 : Nat := 3911154417341460897445309

theorem tailTrace_7616946 : CollatzResearch.WordTrace tailWord_7616946 prefixEnd_7616946 3911154417341460897445309 := by
  unfold tailWord_7616946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69453210965778246913573673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185208562575408658436196461 69453210965778246913573673)
  ·
    refine ⟨52089908224333685185180255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69453210965778246913573673 52089908224333685185180255)
    ·
      refine ⟨78134862336500527777770383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52089908224333685185180255 78134862336500527777770383)
      ·
        refine ⟨117202293504750791666655575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78134862336500527777770383 117202293504750791666655575)
        ·
          refine ⟨175803440257126187499983363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117202293504750791666655575 175803440257126187499983363)
          ·
            refine ⟨263705160385689281249975045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175803440257126187499983363 263705160385689281249975045)
            ·
              refine ⟨49444717572316740234370321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263705160385689281249975045 49444717572316740234370321)
              ·
                refine ⟨37083538179237555175777741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49444717572316740234370321 37083538179237555175777741)
                ·
                  refine ⟨13906326817214083190916653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37083538179237555175777741 13906326817214083190916653)
                  ·
                    refine ⟨5214872556455281196593745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13906326817214083190916653 5214872556455281196593745)
                    ·
                      refine ⟨3911154417341460897445309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214872556455281196593745 3911154417341460897445309)
                      ·
                        rfl

theorem cell23_7616946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_7616946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616946 prefixEnd_7616946 := by exact prefixLift 7616946
  have htrace : WordTrace (prefixWord ++ tailWord_7616946) baseStart_7616946 baseEnd_7616946 := by
    simpa [prefixWord, tailWord_7616946, baseEnd_7616946] using wordTrace_append hprefix tailTrace_7616946
  have hstable : (prefixWord ++ tailWord_7616946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616946).length < 2 ^ (prefixWord ++ tailWord_7616946).sum := by decide
  have hdescent : baseEnd_7616946 < baseStart_7616946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616952 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_7616952 : Nat := 118140960795 + 7616952 * 2 ^ 59
def prefixEnd_7616952 : Nat := 4983230072969 + 3 ^ 40 * 7616952 * 2
def baseEnd_7616952 : Nat := 1303719166075129291323427

theorem tailTrace_7616952 : CollatzResearch.WordTrace tailWord_7616952 prefixEnd_7616952 1303719166075129291323427 := by
  unfold tailWord_7616952
  simp only [CollatzResearch.WordTrace]
  refine ⟨138906531350545625339506555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185208708467394167119342073 138906531350545625339506555)
  ·
    refine ⟨208359797025818438009259833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138906531350545625339506555 208359797025818438009259833)
    ·
      refine ⟨156269847769363828506944875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208359797025818438009259833 156269847769363828506944875)
      ·
        refine ⟨234404771654045742760417313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156269847769363828506944875 234404771654045742760417313)
        ·
          refine ⟨175803578740534307070312985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234404771654045742760417313 175803578740534307070312985)
          ·
            refine ⟨131852684055400730302734739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175803578740534307070312985 131852684055400730302734739)
            ·
              refine ⟨197779026083101095454102109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131852684055400730302734739 197779026083101095454102109)
              ·
                refine ⟨74167134781162910795288291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197779026083101095454102109 74167134781162910795288291)
                ·
                  refine ⟨111250702171744366192932437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74167134781162910795288291 111250702171744366192932437)
                  ·
                    refine ⟨1303719166075129291323427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111250702171744366192932437 1303719166075129291323427)
                    ·
                      rfl

theorem cell23_7616952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_7616952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616952 prefixEnd_7616952 := by exact prefixLift 7616952
  have htrace : WordTrace (prefixWord ++ tailWord_7616952) baseStart_7616952 baseEnd_7616952 := by
    simpa [prefixWord, tailWord_7616952, baseEnd_7616952] using wordTrace_append hprefix tailTrace_7616952
  have hstable : (prefixWord ++ tailWord_7616952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616952).length < 2 ^ (prefixWord ++ tailWord_7616952).sum := by decide
  have hdescent : baseEnd_7616952 < baseStart_7616952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616953 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7616953 : Nat := 118140960795 + 7616953 * 2 ^ 59
def prefixEnd_7616953 : Nat := 4983230072969 + 3 ^ 40 * 7616953 * 2
def baseEnd_7616953 : Nat := 3911158011706042370057777

theorem tailTrace_7616953 : CollatzResearch.WordTrace tailWord_7616953 prefixEnd_7616953 3911158011706042370057777 := by
  unfold tailWord_7616953
  simp only [CollatzResearch.WordTrace]
  refine ⟨277813099174087627849799513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185208732782725085233199675 277813099174087627849799513)
  ·
    refine ⟨208359824380565720887349635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277813099174087627849799513 208359824380565720887349635)
    ·
      refine ⟨312539736570848581331024453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208359824380565720887349635 312539736570848581331024453)
      ·
        refine ⟨58601200607034108999567085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312539736570848581331024453 58601200607034108999567085)
        ·
          refine ⟨21975450227637790874837657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58601200607034108999567085 21975450227637790874837657)
          ·
            refine ⟨16481587670728343156128243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21975450227637790874837657 16481587670728343156128243)
            ·
              refine ⟨24722381506092514734192365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16481587670728343156128243 24722381506092514734192365)
              ·
                refine ⟨9270893064784693025322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24722381506092514734192365 9270893064784693025322137)
                ·
                  refine ⟨6953169798588519768991603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270893064784693025322137 6953169798588519768991603)
                  ·
                    refine ⟨10429754697882779653487405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953169798588519768991603 10429754697882779653487405)
                    ·
                      refine ⟨3911158011706042370057777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10429754697882779653487405 3911158011706042370057777)
                      ·
                        rfl

theorem cell23_7616953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7616953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616953 prefixEnd_7616953 := by exact prefixLift 7616953
  have htrace : WordTrace (prefixWord ++ tailWord_7616953) baseStart_7616953 baseEnd_7616953 := by
    simpa [prefixWord, tailWord_7616953, baseEnd_7616953] using wordTrace_append hprefix tailTrace_7616953
  have hstable : (prefixWord ++ tailWord_7616953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616953).length < 2 ^ (prefixWord ++ tailWord_7616953).sum := by decide
  have hdescent : baseEnd_7616953 < baseStart_7616953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7616999 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 7]
def baseStart_7616999 : Nat := 118140960795 + 7616999 * 2 ^ 59
def prefixEnd_7616999 : Nat := 4983230072969 + 3 ^ 40 * 7616999 * 2
def baseEnd_7616999 : Nat := 434575736868461021120285

theorem tailTrace_7616999 : CollatzResearch.WordTrace tailWord_7616999 prefixEnd_7616999 434575736868461021120285 := by
  unfold tailWord_7616999
  simp only [CollatzResearch.WordTrace]
  refine ⟨277814776931920977705974051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185209851287947318470649367 277814776931920977705974051)
  ·
    refine ⟨416722165397881466558961077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277814776931920977705974051 416722165397881466558961077)
    ·
      refine ⟨39067703006051387489902601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416722165397881466558961077 39067703006051387489902601)
      ·
        refine ⟨29300777254538540617426951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39067703006051387489902601 29300777254538540617426951)
        ·
          refine ⟨43951165881807810926140427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29300777254538540617426951 43951165881807810926140427)
          ·
            refine ⟨65926748822711716389210641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43951165881807810926140427 65926748822711716389210641)
            ·
              refine ⟨49445061617033787291907981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65926748822711716389210641 49445061617033787291907981)
              ·
                refine ⟨18541898106387670234465493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49445061617033787291907981 18541898106387670234465493)
                ·
                  refine ⟨434575736868461021120285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18541898106387670234465493 434575736868461021120285)
                  ·
                    rfl

theorem cell23_7616999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 7].length) (baseStart_7616999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7616999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7616999 prefixEnd_7616999 := by exact prefixLift 7616999
  have htrace : WordTrace (prefixWord ++ tailWord_7616999) baseStart_7616999 baseEnd_7616999 := by
    simpa [prefixWord, tailWord_7616999, baseEnd_7616999] using wordTrace_append hprefix tailTrace_7616999
  have hstable : (prefixWord ++ tailWord_7616999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7616999).length < 2 ^ (prefixWord ++ tailWord_7616999).sum := by decide
  have hdescent : baseEnd_7616999 < baseStart_7616999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7616999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617006 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7617006 : Nat := 118140960795 + 7617006 * 2 ^ 59
def prefixEnd_7617006 : Nat := 4983230072969 + 3 ^ 40 * 7617006 * 2
def baseEnd_7617006 : Nat := 3911185226180730662695033

theorem tailTrace_7617006 : CollatzResearch.WordTrace tailWord_7617006 prefixEnd_7617006 3911185226180730662695033 := by
  unfold tailWord_7617006
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726879030361952237684859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185210021495263745267652581 34726879030361952237684859)
  ·
    refine ⟨52090318545542928356527289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34726879030361952237684859 52090318545542928356527289)
    ·
      refine ⟨39067738909157196267395467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52090318545542928356527289 39067738909157196267395467)
      ·
        refine ⟨58601608363735794401093201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39067738909157196267395467 58601608363735794401093201)
        ·
          refine ⟨43951206272801845800819901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58601608363735794401093201 43951206272801845800819901)
          ·
            refine ⟨16481702352300692175307463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43951206272801845800819901 16481702352300692175307463)
            ·
              refine ⟨24722553528451038262961195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16481702352300692175307463 24722553528451038262961195)
              ·
                refine ⟨37083830292676557394441793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24722553528451038262961195 37083830292676557394441793)
                ·
                  refine ⟨27812872719507418045831345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37083830292676557394441793 27812872719507418045831345)
                  ·
                    refine ⟨20859654539630563534373509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27812872719507418045831345 20859654539630563534373509)
                    ·
                      refine ⟨3911185226180730662695033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20859654539630563534373509 3911185226180730662695033)
                      ·
                        rfl

theorem cell23_7617006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7617006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617006 prefixEnd_7617006 := by exact prefixLift 7617006
  have htrace : WordTrace (prefixWord ++ tailWord_7617006) baseStart_7617006 baseEnd_7617006 := by
    simpa [prefixWord, tailWord_7617006, baseEnd_7617006] using wordTrace_append hprefix tailTrace_7617006
  have hstable : (prefixWord ++ tailWord_7617006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617006).length < 2 ^ (prefixWord ++ tailWord_7617006).sum := by decide
  have hdescent : baseEnd_7617006 < baseStart_7617006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617010 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7617010 : Nat := 118140960795 + 7617010 * 2 ^ 59
def prefixEnd_7617010 : Nat := 4983230072969 + 3 ^ 40 * 7617010 * 2
def baseEnd_7617010 : Nat := 3911187280103348647045015

theorem tailTrace_7617010 : CollatzResearch.WordTrace tailWord_7617010 prefixEnd_7617010 3911187280103348647045015 := by
  unfold tailWord_7617010
  simp only [CollatzResearch.WordTrace]
  refine ⟨69453794533720281646156121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185210118756587417723082989 69453794533720281646156121)
  ·
    refine ⟨52090345900290211234617091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69453794533720281646156121 52090345900290211234617091)
    ·
      refine ⟨78135518850435316851925637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52090345900290211234617091 78135518850435316851925637)
      ·
        refine ⟨14650409784456621909736057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78135518850435316851925637 14650409784456621909736057)
        ·
          refine ⟨10987807338342466432302043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14650409784456621909736057 10987807338342466432302043)
          ·
            refine ⟨16481711007513699648453065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987807338342466432302043 16481711007513699648453065)
            ·
              refine ⟨12361283255635274736339799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16481711007513699648453065 12361283255635274736339799)
              ·
                refine ⟨18541924883452912104509699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361283255635274736339799 18541924883452912104509699)
                ·
                  refine ⟨27812887325179368156764549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18541924883452912104509699 27812887325179368156764549)
                  ·
                    refine ⟨5214916373471131529393353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27812887325179368156764549 5214916373471131529393353)
                    ·
                      refine ⟨3911187280103348647045015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214916373471131529393353 3911187280103348647045015)
                      ·
                        rfl

theorem cell23_7617010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7617010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617010 prefixEnd_7617010 := by exact prefixLift 7617010
  have htrace : WordTrace (prefixWord ++ tailWord_7617010) baseStart_7617010 baseEnd_7617010 := by
    simpa [prefixWord, tailWord_7617010, baseEnd_7617010] using wordTrace_append hprefix tailTrace_7617010
  have hstable : (prefixWord ++ tailWord_7617010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617010).length < 2 ^ (prefixWord ++ tailWord_7617010).sum := by decide
  have hdescent : baseEnd_7617010 < baseStart_7617010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617044 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7617044 : Nat := 118140960795 + 7617044 * 2 ^ 59
def prefixEnd_7617044 : Nat := 4983230072969 + 3 ^ 40 * 7617044 * 2
def baseEnd_7617044 : Nat := 3911204738445601514019859

theorem tailTrace_7617044 : CollatzResearch.WordTrace tailWord_7617044 prefixEnd_7617044 3911204738445601514019859 := by
  unfold tailWord_7617044
  simp only [CollatzResearch.WordTrace]
  refine ⟨138908209108378975195681093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185210945477838633594241457 138908209108378975195681093)
  ·
    refine ⟨26045289207821057849190205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138908209108378975195681093 26045289207821057849190205)
    ·
      refine ⟨9766983452932896693446327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26045289207821057849190205 9766983452932896693446327)
      ·
        refine ⟨14650475179399345040169491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766983452932896693446327 14650475179399345040169491)
        ·
          refine ⟨21975712769099017560254237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14650475179399345040169491 21975712769099017560254237)
          ·
            refine ⟨8240892288412131585095339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21975712769099017560254237 8240892288412131585095339)
            ·
              refine ⟨12361338432618197377643009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240892288412131585095339 12361338432618197377643009)
              ·
                refine ⟨9271003824463648033232257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12361338432618197377643009 9271003824463648033232257)
                ·
                  refine ⟨6953252868347736024924193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9271003824463648033232257 6953252868347736024924193)
                  ·
                    refine ⟨5214939651260802018693145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6953252868347736024924193 5214939651260802018693145)
                    ·
                      refine ⟨3911204738445601514019859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5214939651260802018693145 3911204738445601514019859)
                      ·
                        rfl

theorem cell23_7617044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7617044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617044 prefixEnd_7617044 := by exact prefixLift 7617044
  have htrace : WordTrace (prefixWord ++ tailWord_7617044) baseStart_7617044 baseEnd_7617044 := by
    simpa [prefixWord, tailWord_7617044, baseEnd_7617044] using wordTrace_append hprefix tailTrace_7617044
  have hstable : (prefixWord ++ tailWord_7617044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617044).length < 2 ^ (prefixWord ++ tailWord_7617044).sum := by decide
  have hdescent : baseEnd_7617044 < baseStart_7617044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617066 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7617066 : Nat := 118140960795 + 7617066 * 2 ^ 59
def prefixEnd_7617066 : Nat := 4983230072969 + 3 ^ 40 * 7617066 * 2
def baseEnd_7617066 : Nat := 3911216035020000427944757

theorem tailTrace_7617066 : CollatzResearch.WordTrace tailWord_7617066 prefixEnd_7617066 3911216035020000427944757 := by
  unfold tailWord_7617066
  simp only [CollatzResearch.WordTrace]
  refine ⟨69454305155669562037165763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185211480415118832099108701 69454305155669562037165763)
  ·
    refine ⟨104181457733504343055748645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69454305155669562037165763 104181457733504343055748645)
    ·
      refine ⟨19534023325032064322952871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104181457733504343055748645 19534023325032064322952871)
      ·
        refine ⟨29301034987548096484429307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534023325032064322952871 29301034987548096484429307)
        ·
          refine ⟨43951552481322144726643961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29301034987548096484429307 43951552481322144726643961)
          ·
            refine ⟨32963664360991608544982971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43951552481322144726643961 32963664360991608544982971)
            ·
              refine ⟨49445496541487412817474457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32963664360991608544982971 49445496541487412817474457)
              ·
                refine ⟨37084122406115559613105843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49445496541487412817474457 37084122406115559613105843)
                ·
                  refine ⟨55626183609173339419658765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37084122406115559613105843 55626183609173339419658765)
                  ·
                    refine ⟨20859818853440002282372037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55626183609173339419658765 20859818853440002282372037)
                    ·
                      refine ⟨3911216035020000427944757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20859818853440002282372037 3911216035020000427944757)
                      ·
                        rfl

theorem cell23_7617066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7617066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617066 prefixEnd_7617066 := by exact prefixLift 7617066
  have htrace : WordTrace (prefixWord ++ tailWord_7617066) baseStart_7617066 baseEnd_7617066 := by
    simpa [prefixWord, tailWord_7617066, baseEnd_7617066] using wordTrace_append hprefix tailTrace_7617066
  have hstable : (prefixWord ++ tailWord_7617066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617066).length < 2 ^ (prefixWord ++ tailWord_7617066).sum := by decide
  have hdescent : baseEnd_7617066 < baseStart_7617066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617079 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_7617079 : Nat := 118140960795 + 7617079 * 2 ^ 59
def prefixEnd_7617079 : Nat := 4983230072969 + 3 ^ 40 * 7617079 * 2
def baseEnd_7617079 : Nat := 3911222710268508877082197

theorem tailTrace_7617079 : CollatzResearch.WordTrace tailWord_7617079 prefixEnd_7617079 3911222710268508877082197 := by
  unfold tailWord_7617079
  simp only [CollatzResearch.WordTrace]
  refine ⟨277817694771631151368886291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185211796514420767579257527 277817694771631151368886291)
  ·
    refine ⟨416726542157446727053329437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277817694771631151368886291 416726542157446727053329437)
    ·
      refine ⟨156272453309042522644998539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416726542157446727053329437 156272453309042522644998539)
      ·
        refine ⟨234408679963563783967497809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156272453309042522644998539 234408679963563783967497809)
        ·
          refine ⟨175806509972672837975623357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234408679963563783967497809 175806509972672837975623357)
          ·
            refine ⟨65927441239752314240858759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175806509972672837975623357 65927441239752314240858759)
            ·
              refine ⟨98891161859628471361288139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65927441239752314240858759 98891161859628471361288139)
              ·
                refine ⟨148336742789442707041932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98891161859628471361288139 148336742789442707041932209)
                ·
                  refine ⟨111252557092082030281449157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148336742789442707041932209 111252557092082030281449157)
                  ·
                    refine ⟨20859854454765380677771717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111252557092082030281449157 20859854454765380677771717)
                    ·
                      refine ⟨3911222710268508877082197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20859854454765380677771717 3911222710268508877082197)
                      ·
                        rfl

theorem cell23_7617079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_7617079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617079 prefixEnd_7617079 := by exact prefixLift 7617079
  have htrace : WordTrace (prefixWord ++ tailWord_7617079) baseStart_7617079 baseEnd_7617079 := by
    simpa [prefixWord, tailWord_7617079, baseEnd_7617079] using wordTrace_append hprefix tailTrace_7617079
  have hstable : (prefixWord ++ tailWord_7617079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617079).length < 2 ^ (prefixWord ++ tailWord_7617079).sum := by decide
  have hdescent : baseEnd_7617079 < baseStart_7617079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617106 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_7617106 : Nat := 118140960795 + 7617106 * 2 ^ 59
def prefixEnd_7617106 : Nat := 4983230072969 + 3 ^ 40 * 7617106 * 2
def baseEnd_7617106 : Nat := 434581841582908919049397

theorem tailTrace_7617106 : CollatzResearch.WordTrace tailWord_7617106 prefixEnd_7617106 434581841582908919049397 := by
  unfold tailWord_7617106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69454669885633333745029793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185212453028355556653412781 69454669885633333745029793)
  ·
    refine ⟨52091002414225000308772345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69454669885633333745029793 52091002414225000308772345)
    ·
      refine ⟨39068251810668750231579259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52091002414225000308772345 39068251810668750231579259)
      ·
        refine ⟨58602377716003125347368889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39068251810668750231579259 58602377716003125347368889)
        ·
          refine ⟨43951783287002344010526667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58602377716003125347368889 43951783287002344010526667)
          ·
            refine ⟨65927674930503516015790001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43951783287002344010526667 65927674930503516015790001)
            ·
              refine ⟨49445756197877637011842501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65927674930503516015790001 49445756197877637011842501)
              ·
                refine ⟨9271079287102056939720469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49445756197877637011842501 9271079287102056939720469)
                ·
                  refine ⟨434581841582908919049397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9271079287102056939720469 434581841582908919049397)
                  ·
                    rfl

theorem cell23_7617106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_7617106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617106 prefixEnd_7617106 := by exact prefixLift 7617106
  have htrace : WordTrace (prefixWord ++ tailWord_7617106) baseStart_7617106 baseEnd_7617106 := by
    simpa [prefixWord, tailWord_7617106, baseEnd_7617106] using wordTrace_append hprefix tailTrace_7617106
  have hstable : (prefixWord ++ tailWord_7617106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617106).length < 2 ^ (prefixWord ++ tailWord_7617106).sum := by decide
  have hdescent : baseEnd_7617106 < baseStart_7617106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617109 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7617109 : Nat := 118140960795 + 7617109 * 2 ^ 59
def prefixEnd_7617109 : Nat := 4983230072969 + 3 ^ 40 * 7617109 * 2
def baseEnd_7617109 : Nat := 3911238114688143759707059

theorem tailTrace_7617109 : CollatzResearch.WordTrace tailWord_7617109 prefixEnd_7617109 3911238114688143759707059 := by
  unfold tailWord_7617109
  simp only [CollatzResearch.WordTrace]
  refine ⟨277818788961522466492478381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185212525974348310994985587 277818788961522466492478381)
  ·
    refine ⟨104182045860570924934679393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277818788961522466492478381 104182045860570924934679393)
    ·
      refine ⟨78136534395428193701009545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104182045860570924934679393 78136534395428193701009545)
      ·
        refine ⟨58602400796571145275757159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78136534395428193701009545 58602400796571145275757159)
        ·
          refine ⟨87903601194856717913635739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58602400796571145275757159 87903601194856717913635739)
          ·
            refine ⟨131855401792285076870453609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87903601194856717913635739 131855401792285076870453609)
            ·
              refine ⟨98891551344213807652840207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131855401792285076870453609 98891551344213807652840207)
              ·
                refine ⟨148337327016320711479260311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98891551344213807652840207 148337327016320711479260311)
                ·
                  refine ⟨222505990524481067218890467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148337327016320711479260311 222505990524481067218890467)
                  ·
                    refine ⟨333758985786721600828335701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222505990524481067218890467 333758985786721600828335701)
                    ·
                      refine ⟨3911238114688143759707059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333758985786721600828335701 3911238114688143759707059)
                      ·
                        rfl

theorem cell23_7617109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7617109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617109 prefixEnd_7617109 := by exact prefixLift 7617109
  have htrace : WordTrace (prefixWord ++ tailWord_7617109) baseStart_7617109 baseEnd_7617109 := by
    simpa [prefixWord, tailWord_7617109, baseEnd_7617109] using wordTrace_append hprefix tailTrace_7617109
  have hstable : (prefixWord ++ tailWord_7617109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617109).length < 2 ^ (prefixWord ++ tailWord_7617109).sum := by decide
  have hdescent : baseEnd_7617109 < baseStart_7617109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617143 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_7617143 : Nat := 118140960795 + 7617143 * 2 ^ 59
def prefixEnd_7617143 : Nat := 4983230072969 + 3 ^ 40 * 7617143 * 2
def baseEnd_7617143 : Nat := 3911255573030396626681903

theorem tailTrace_7617143 : CollatzResearch.WordTrace tailWord_7617143 prefixEnd_7617143 3911255573030396626681903 := by
  unfold tailWord_7617143
  simp only [CollatzResearch.WordTrace]
  refine ⟨277820029043399290299216083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185213352695599526866144055 277820029043399290299216083)
  ·
    refine ⟨416730043565098935448824125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277820029043399290299216083 416730043565098935448824125)
    ·
      refine ⟨156273766336912100793309047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416730043565098935448824125 156273766336912100793309047)
      ·
        refine ⟨234410649505368151189963571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156273766336912100793309047 234410649505368151189963571)
        ·
          refine ⟨351615974258052226784945357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234410649505368151189963571 351615974258052226784945357)
          ·
            refine ⟨131855990346769585044354509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351615974258052226784945357 131855990346769585044354509)
            ·
              refine ⟨49445996380038594391632941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131855990346769585044354509 49445996380038594391632941)
              ·
                refine ⟨18542248642514472896862353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49445996380038594391632941 18542248642514472896862353)
                ·
                  refine ⟨13906686481885854672646765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18542248642514472896862353 13906686481885854672646765)
                  ·
                    refine ⟨5215007430707195502242537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13906686481885854672646765 5215007430707195502242537)
                    ·
                      refine ⟨3911255573030396626681903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5215007430707195502242537 3911255573030396626681903)
                      ·
                        rfl

theorem cell23_7617143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_7617143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617143 prefixEnd_7617143 := by exact prefixLift 7617143
  have htrace : WordTrace (prefixWord ++ tailWord_7617143) baseStart_7617143 baseEnd_7617143 := by
    simpa [prefixWord, tailWord_7617143, baseEnd_7617143] using wordTrace_append hprefix tailTrace_7617143
  have hstable : (prefixWord ++ tailWord_7617143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617143).length < 2 ^ (prefixWord ++ tailWord_7617143).sum := by decide
  have hdescent : baseEnd_7617143 < baseStart_7617143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617166 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7617166 : Nat := 118140960795 + 7617166 * 2 ^ 59
def prefixEnd_7617166 : Nat := 4983230072969 + 3 ^ 40 * 7617166 * 2
def baseEnd_7617166 : Nat := 1303755794361816678898099

theorem tailTrace_7617166 : CollatzResearch.WordTrace tailWord_7617166 prefixEnd_7617166 1303755794361816678898099 := by
  unfold tailWord_7617166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34727608490289495653412919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185213911948210643484868901 34727608490289495653412919)
  ·
    refine ⟨52091412735434243480119379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34727608490289495653412919 52091412735434243480119379)
    ·
      refine ⟨78137119103151365220179069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52091412735434243480119379 78137119103151365220179069)
      ·
        refine ⟨29301419663681761957567151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78137119103151365220179069 29301419663681761957567151)
        ·
          refine ⟨43952129495522642936350727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29301419663681761957567151 43952129495522642936350727)
          ·
            refine ⟨65928194243283964404526091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43952129495522642936350727 65928194243283964404526091)
            ·
              refine ⟨98892291364925946606789137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65928194243283964404526091 98892291364925946606789137)
              ·
                refine ⟨74169218523694459955091853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98892291364925946606789137 74169218523694459955091853)
                ·
                  refine ⟨27813456946385422483159445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74169218523694459955091853 27813456946385422483159445)
                  ·
                    refine ⟨1303755794361816678898099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27813456946385422483159445 1303755794361816678898099)
                    ·
                      rfl

theorem cell23_7617166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7617166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617166 prefixEnd_7617166 := by exact prefixLift 7617166
  have htrace : WordTrace (prefixWord ++ tailWord_7617166) baseStart_7617166 baseEnd_7617166 := by
    simpa [prefixWord, tailWord_7617166, baseEnd_7617166] using wordTrace_append hprefix tailTrace_7617166
  have hstable : (prefixWord ++ tailWord_7617166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617166).length < 2 ^ (prefixWord ++ tailWord_7617166).sum := by decide
  have hdescent : baseEnd_7617166 < baseStart_7617166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617176 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7617176 : Nat := 118140960795 + 7617176 * 2 ^ 59
def prefixEnd_7617176 : Nat := 4983230072969 + 3 ^ 40 * 7617176 * 2
def baseEnd_7617176 : Nat := 3911272517891994997569251

theorem tailTrace_7617176 : CollatzResearch.WordTrace tailWord_7617176 prefixEnd_7617176 3911272517891994997569251 := by
  unfold tailWord_7617176
  simp only [CollatzResearch.WordTrace]
  refine ⟨138910616326139868467583691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185214155101519824623444921 138910616326139868467583691)
  ·
    refine ⟨208365924489209802701375537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138910616326139868467583691 208365924489209802701375537)
    ·
      refine ⟨156274443366907352026031653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208365924489209802701375537 156274443366907352026031653)
      ·
        refine ⟨29301458131295128504880935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156274443366907352026031653 29301458131295128504880935)
        ·
          refine ⟨43952187196942692757321403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29301458131295128504880935 43952187196942692757321403)
          ·
            refine ⟨65928280795414039135982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43952187196942692757321403 65928280795414039135982105)
            ·
              refine ⟨49446210596560529351986579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65928280795414039135982105 49446210596560529351986579)
              ·
                refine ⟨74169315894840794027979869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49446210596560529351986579 74169315894840794027979869)
                ·
                  refine ⟨27813493460565297760492451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74169315894840794027979869 27813493460565297760492451)
                  ·
                    refine ⟨41720240190847946640738677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27813493460565297760492451 41720240190847946640738677)
                    ·
                      refine ⟨3911272517891994997569251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41720240190847946640738677 3911272517891994997569251)
                      ·
                        rfl

theorem cell23_7617176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7617176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617176 prefixEnd_7617176 := by exact prefixLift 7617176
  have htrace : WordTrace (prefixWord ++ tailWord_7617176) baseStart_7617176 baseEnd_7617176 := by
    simpa [prefixWord, tailWord_7617176, baseEnd_7617176] using wordTrace_append hprefix tailTrace_7617176
  have hstable : (prefixWord ++ tailWord_7617176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617176).length < 2 ^ (prefixWord ++ tailWord_7617176).sum := by decide
  have hdescent : baseEnd_7617176 < baseStart_7617176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7617207 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_7617207 : Nat := 118140960795 + 7617207 * 2 ^ 59
def prefixEnd_7617207 : Nat := 4983230072969 + 3 ^ 40 * 7617207 * 2
def baseEnd_7617207 : Nat := 3911288435792284376281609

theorem tailTrace_7617207 : CollatzResearch.WordTrace tailWord_7617207 prefixEnd_7617207 3911288435792284376281609 := by
  unfold tailWord_7617207
  simp only [CollatzResearch.WordTrace]
  refine ⟨277822363315167429229545875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185214908876778286153030583 277822363315167429229545875)
  ·
    refine ⟨416733544972751143844318813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277822363315167429229545875 416733544972751143844318813)
    ·
      refine ⟨156275079364781678941619555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416733544972751143844318813 156275079364781678941619555)
      ·
        refine ⟨234412619047172518412429333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156275079364781678941619555 234412619047172518412429333)
        ·
          refine ⟨10988091517836211800582625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234412619047172518412429333 10988091517836211800582625)
          ·
            refine ⟨8241068638377158850436969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10988091517836211800582625 8241068638377158850436969)
            ·
              refine ⟨6180801478782869137827727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241068638377158850436969 6180801478782869137827727)
              ·
                refine ⟨9271202218174303706741591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180801478782869137827727 9271202218174303706741591)
                ·
                  refine ⟨13906803327261455560112387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271202218174303706741591 13906803327261455560112387)
                  ·
                    refine ⟨20860204990892183340168581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13906803327261455560112387 20860204990892183340168581)
                    ·
                      refine ⟨3911288435792284376281609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20860204990892183340168581 3911288435792284376281609)
                      ·
                        rfl

theorem cell23_7617207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_7617207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7617207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7617207 prefixEnd_7617207 := by exact prefixLift 7617207
  have htrace : WordTrace (prefixWord ++ tailWord_7617207) baseStart_7617207 baseEnd_7617207 := by
    simpa [prefixWord, tailWord_7617207, baseEnd_7617207] using wordTrace_append hprefix tailTrace_7617207
  have hstable : (prefixWord ++ tailWord_7617207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7617207).length < 2 ^ (prefixWord ++ tailWord_7617207).sum := by decide
  have hdescent : baseEnd_7617207 < baseStart_7617207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7617207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
