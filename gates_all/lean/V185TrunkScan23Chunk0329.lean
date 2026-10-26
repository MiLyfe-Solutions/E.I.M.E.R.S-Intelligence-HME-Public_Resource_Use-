import V185TrunkScan23Chunk0328

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1944662 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1944662 : Nat := 118140960795 + 1944662 * 2 ^ 59
def prefixEnd_1944662 : Nat := 4983230072969 + 3 ^ 40 * 1944662 * 2
def baseEnd_1944662 : Nat := 998546316533775734681669

theorem tailTrace_1944662 : CollatzResearch.WordTrace tailWord_1944662 prefixEnd_1944662 998546316533775734681669 := by
  unfold tailWord_1944662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432978130051823167071265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47285100053886113782093493 4432978130051823167071265)
  ·
    refine ⟨3324733597538867375303449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4432978130051823167071265 3324733597538867375303449)
    ·
      refine ⟨2493550198154150531477587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3324733597538867375303449 2493550198154150531477587)
      ·
        refine ⟨3740325297231225797216381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493550198154150531477587 3740325297231225797216381)
        ·
          refine ⟨1402621986461709673956143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3740325297231225797216381 1402621986461709673956143)
          ·
            refine ⟨2103932979692564510934215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402621986461709673956143 2103932979692564510934215)
            ·
              refine ⟨3155899469538846766401323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103932979692564510934215 3155899469538846766401323)
              ·
                refine ⟨4733849204308270149601985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155899469538846766401323 4733849204308270149601985)
                ·
                  refine ⟨3550386903231202612201489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733849204308270149601985 3550386903231202612201489)
                  ·
                    refine ⟨2662790177423401959151117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550386903231202612201489 2662790177423401959151117)
                    ·
                      refine ⟨998546316533775734681669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2662790177423401959151117 998546316533775734681669)
                      ·
                        rfl

theorem cell23_1944662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1944662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944662 prefixEnd_1944662 := by exact prefixLift 1944662
  have htrace : WordTrace (prefixWord ++ tailWord_1944662) baseStart_1944662 baseEnd_1944662 := by
    simpa [prefixWord, tailWord_1944662, baseEnd_1944662] using wordTrace_append hprefix tailTrace_1944662
  have hstable : (prefixWord ++ tailWord_1944662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944662).length < 2 ^ (prefixWord ++ tailWord_1944662).sum := by decide
  have hdescent : baseEnd_1944662 < baseStart_1944662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944664 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1944664 : Nat := 118140960795 + 1944664 * 2 ^ 59
def prefixEnd_1944664 : Nat := 4983230072969 + 3 ^ 40 * 1944664 * 2
def baseEnd_1944664 : Nat := 998547343495084726856659

theorem tailTrace_1944664 : CollatzResearch.WordTrace tailWord_1944664 prefixEnd_1944664 998547343495084726856659 := by
  unfold tailWord_1944664
  simp only [CollatzResearch.WordTrace]
  refine ⟨35463861513410962507356523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47285148684547950009808697 35463861513410962507356523)
  ·
    refine ⟨53195792270116443761034785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35463861513410962507356523 53195792270116443761034785)
    ·
      refine ⟨39896844202587332820776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53195792270116443761034785 39896844202587332820776089)
      ·
        refine ⟨29922633151940499615582067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39896844202587332820776089 29922633151940499615582067)
        ·
          refine ⟨44883949727910749423373101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29922633151940499615582067 44883949727910749423373101)
          ·
            refine ⟨16831481147966531033764913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44883949727910749423373101 16831481147966531033764913)
            ·
              refine ⟨12623610860974898275323685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16831481147966531033764913 12623610860974898275323685)
              ·
                refine ⟨2366927036432793426623191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12623610860974898275323685 2366927036432793426623191)
                ·
                  refine ⟨3550390554649190139934787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366927036432793426623191 3550390554649190139934787)
                  ·
                    refine ⟨5325585831973785209902181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550390554649190139934787 5325585831973785209902181)
                    ·
                      refine ⟨998547343495084726856659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5325585831973785209902181 998547343495084726856659)
                      ·
                        rfl

theorem cell23_1944664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1944664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944664 prefixEnd_1944664 := by exact prefixLift 1944664
  have htrace : WordTrace (prefixWord ++ tailWord_1944664) baseStart_1944664 baseEnd_1944664 := by
    simpa [prefixWord, tailWord_1944664, baseEnd_1944664] using wordTrace_append hprefix tailTrace_1944664
  have hstable : (prefixWord ++ tailWord_1944664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944664).length < 2 ^ (prefixWord ++ tailWord_1944664).sum := by decide
  have hdescent : baseEnd_1944664 < baseStart_1944664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944681 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 1, 1, 4]
def baseStart_1944681 : Nat := 118140960795 + 1944681 * 2 ^ 59
def prefixEnd_1944681 : Nat := 4983230072969 + 3 ^ 40 * 1944681 * 2
def baseEnd_1944681 : Nat := 998556072666211160344081

theorem tailTrace_1944681 : CollatzResearch.WordTrace tailWord_1944681 prefixEnd_1944681 998556072666211160344081 := by
  unfold tailWord_1944681
  simp only [CollatzResearch.WordTrace]
  refine ⟨70928343067760336918081897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47285562045173557945387931 70928343067760336918081897)
  ·
    refine ⟨53196257300820252688561423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70928343067760336918081897 53196257300820252688561423)
    ·
      refine ⟨79794385951230379032842135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53196257300820252688561423 79794385951230379032842135)
      ·
        refine ⟨119691578926845568549263203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79794385951230379032842135 119691578926845568549263203)
        ·
          refine ⟨179537368390268352823894805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119691578926845568549263203 179537368390268352823894805)
          ·
            refine ⟨8415814143293829038620069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179537368390268352823894805 8415814143293829038620069)
            ·
              refine ⟨1577965151867592944741263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8415814143293829038620069 1577965151867592944741263)
              ·
                refine ⟨2366947727801389417111895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577965151867592944741263 2366947727801389417111895)
                ·
                  refine ⟨3550421591702084125667843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366947727801389417111895 3550421591702084125667843)
                  ·
                    refine ⟨5325632387553126188501765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550421591702084125667843 5325632387553126188501765)
                    ·
                      refine ⟨998556072666211160344081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5325632387553126188501765 998556072666211160344081)
                      ·
                        rfl

theorem cell23_1944681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 1, 4].length) (baseStart_1944681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944681 prefixEnd_1944681 := by exact prefixLift 1944681
  have htrace : WordTrace (prefixWord ++ tailWord_1944681) baseStart_1944681 baseEnd_1944681 := by
    simpa [prefixWord, tailWord_1944681, baseEnd_1944681] using wordTrace_append hprefix tailTrace_1944681
  have hstable : (prefixWord ++ tailWord_1944681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944681).length < 2 ^ (prefixWord ++ tailWord_1944681).sum := by decide
  have hdescent : baseEnd_1944681 < baseStart_1944681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944694 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1944694 : Nat := 118140960795 + 1944694 * 2 ^ 59
def prefixEnd_1944694 : Nat := 4983230072969 + 3 ^ 40 * 1944694 * 2
def baseEnd_1944694 : Nat := 998562747914719609481521

theorem tailTrace_1944694 : CollatzResearch.WordTrace tailWord_1944694 prefixEnd_1944694 998562747914719609481521 := by
  unfold tailWord_1944694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433051076044577508644071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47285878144475493425536757 4433051076044577508644071)
  ·
    refine ⟨6649576614066866262966107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433051076044577508644071 6649576614066866262966107)
    ·
      refine ⟨9974364921100299394449161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6649576614066866262966107 9974364921100299394449161)
      ·
        refine ⟨7480773690825224545836871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9974364921100299394449161 7480773690825224545836871)
        ·
          refine ⟨11221160536237836818755307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480773690825224545836871 11221160536237836818755307)
          ·
            refine ⟨16831740804356755228132961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11221160536237836818755307 16831740804356755228132961)
            ·
              refine ⟨12623805603267566421099721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16831740804356755228132961 12623805603267566421099721)
              ·
                refine ⟨9467854202450674815824791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12623805603267566421099721 9467854202450674815824791)
                ·
                  refine ⟨14201781303676012223737187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467854202450674815824791 14201781303676012223737187)
                  ·
                    refine ⟨21302671955514018335605781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14201781303676012223737187 21302671955514018335605781)
                    ·
                      refine ⟨998562747914719609481521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21302671955514018335605781 998562747914719609481521)
                      ·
                        rfl

theorem cell23_1944694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1944694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944694 prefixEnd_1944694 := by exact prefixLift 1944694
  have htrace : WordTrace (prefixWord ++ tailWord_1944694) baseStart_1944694 baseEnd_1944694 := by
    simpa [prefixWord, tailWord_1944694, baseEnd_1944694] using wordTrace_append hprefix tailTrace_1944694
  have hstable : (prefixWord ++ tailWord_1944694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944694).length < 2 ^ (prefixWord ++ tailWord_1944694).sum := by decide
  have hdescent : baseEnd_1944694 < baseStart_1944694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944708 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1944708 : Nat := 118140960795 + 1944708 * 2 ^ 59
def prefixEnd_1944708 : Nat := 4983230072969 + 3 ^ 40 * 1944708 * 2
def baseEnd_1944708 : Nat := 332856645547960851568819

theorem tailTrace_1944708 : CollatzResearch.WordTrace tailWord_1944708 prefixEnd_1944708 332856645547960851568819 := by
  unfold tailWord_1944708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35464663919331260264657389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47286218559108347019543185 35464663919331260264657389)
  ·
    refine ⟨13299248969749222599246521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35464663919331260264657389 13299248969749222599246521)
    ·
      refine ⟨9974436727311916949434891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13299248969749222599246521 9974436727311916949434891)
      ·
        refine ⟨14961655090967875424152337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974436727311916949434891 14961655090967875424152337)
        ·
          refine ⟨11221241318225906568114253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14961655090967875424152337 11221241318225906568114253)
          ·
            refine ⟨4207965494334714963042845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11221241318225906568114253 4207965494334714963042845)
            ·
              refine ⟨1577987060375518111141067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4207965494334714963042845 1577987060375518111141067)
              ·
                refine ⟨2366980590563277166711601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577987060375518111141067 2366980590563277166711601)
                ·
                  refine ⟨1775235442922457875033701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366980590563277166711601 1775235442922457875033701)
                  ·
                    refine ⟨332856645547960851568819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1775235442922457875033701 332856645547960851568819)
                    ·
                      rfl

theorem cell23_1944708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1944708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944708 prefixEnd_1944708 := by exact prefixLift 1944708
  have htrace : WordTrace (prefixWord ++ tailWord_1944708) baseStart_1944708 baseEnd_1944708 := by
    simpa [prefixWord, tailWord_1944708, baseEnd_1944708] using wordTrace_append hprefix tailTrace_1944708
  have hstable : (prefixWord ++ tailWord_1944708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944708).length < 2 ^ (prefixWord ++ tailWord_1944708).sum := by decide
  have hdescent : baseEnd_1944708 < baseStart_1944708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944718 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1944718 : Nat := 118140960795 + 1944718 * 2 ^ 59
def prefixEnd_1944718 : Nat := 4983230072969 + 3 ^ 40 * 1944718 * 2
def baseEnd_1944718 : Nat := 998575071450427515581411

theorem tailTrace_1944718 : CollatzResearch.WordTrace tailWord_1944718 prefixEnd_1944718 998575071450427515581411 := by
  unfold tailWord_1944718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866211571078286529647351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47286461712417528158119205 8866211571078286529647351)
  ·
    refine ⟨13299317356617429794471027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866211571078286529647351 13299317356617429794471027)
    ·
      refine ⟨19948976034926144691706541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13299317356617429794471027 19948976034926144691706541)
      ·
        refine ⟨7480866013097304259389953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19948976034926144691706541 7480866013097304259389953)
        ·
          refine ⟨5610649509822978194542465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7480866013097304259389953 5610649509822978194542465)
          ·
            refine ⟨4207987132367233645906849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610649509822978194542465 4207987132367233645906849)
            ·
              refine ⟨3155990349275425234430137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207987132367233645906849 3155990349275425234430137)
              ·
                refine ⟨2366992761956568925822603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155990349275425234430137 2366992761956568925822603)
                ·
                  refine ⟨3550489142934853388733905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366992761956568925822603 3550489142934853388733905)
                  ·
                    refine ⟨2662866857201140041550429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3550489142934853388733905 2662866857201140041550429)
                    ·
                      refine ⟨998575071450427515581411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2662866857201140041550429 998575071450427515581411)
                      ·
                        rfl

theorem cell23_1944718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1944718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944718 prefixEnd_1944718 := by exact prefixLift 1944718
  have htrace : WordTrace (prefixWord ++ tailWord_1944718) baseStart_1944718 baseEnd_1944718 := by
    simpa [prefixWord, tailWord_1944718, baseEnd_1944718] using wordTrace_append hprefix tailTrace_1944718
  have hstable : (prefixWord ++ tailWord_1944718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944718).length < 2 ^ (prefixWord ++ tailWord_1944718).sum := by decide
  have hdescent : baseEnd_1944718 < baseStart_1944718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944732 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1944732 : Nat := 118140960795 + 1944732 * 2 ^ 59
def prefixEnd_1944732 : Nat := 4983230072969 + 3 ^ 40 * 1944732 * 2
def baseEnd_1944732 : Nat := 998582260179590460806347

theorem tailTrace_1944732 : CollatzResearch.WordTrace tailWord_1944732 prefixEnd_1944732 998582260179590460806347 := by
  unfold tailWord_1944732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35465101595287786314094225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47286802127050381752125633 35465101595287786314094225)
  ·
    refine ⟨26598826196465839735570669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35465101595287786314094225 26598826196465839735570669)
    ·
      refine ⟨9974559823674689900839001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26598826196465839735570669 9974559823674689900839001)
      ·
        refine ⟨7480919867756017425629251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9974559823674689900839001 7480919867756017425629251)
        ·
          refine ⟨11221379801634026138443877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480919867756017425629251 11221379801634026138443877)
          ·
            refine ⟨2104008712806379900958227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11221379801634026138443877 2104008712806379900958227)
            ·
              refine ⟨3156013069209569851437341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104008712806379900958227 3156013069209569851437341)
              ·
                refine ⟨1183504900953588694289003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3156013069209569851437341 1183504900953588694289003)
                ·
                  refine ⟨1775257351430383041433505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183504900953588694289003 1775257351430383041433505)
                  ·
                    refine ⟨1331443013572787281075129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775257351430383041433505 1331443013572787281075129)
                    ·
                      refine ⟨998582260179590460806347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331443013572787281075129 998582260179590460806347)
                      ·
                        rfl

theorem cell23_1944732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1944732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944732 prefixEnd_1944732 := by exact prefixLift 1944732
  have htrace : WordTrace (prefixWord ++ tailWord_1944732) baseStart_1944732 baseEnd_1944732 := by
    simpa [prefixWord, tailWord_1944732, baseEnd_1944732] using wordTrace_append hprefix tailTrace_1944732
  have hstable : (prefixWord ++ tailWord_1944732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944732).length < 2 ^ (prefixWord ++ tailWord_1944732).sum := by decide
  have hdescent : baseEnd_1944732 < baseStart_1944732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944749 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_1944749 : Nat := 118140960795 + 1944749 * 2 ^ 59
def prefixEnd_1944749 : Nat := 4983230072969 + 3 ^ 40 * 1944749 * 2
def baseEnd_1944749 : Nat := 998590989350716894293769

theorem tailTrace_1944749 : CollatzResearch.WordTrace tailWord_1944749 prefixEnd_1944749 998590989350716894293769 := by
  unfold tailWord_1944749
  simp only [CollatzResearch.WordTrace]
  refine ⟨70930823231513984531557301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47287215487675989687704867 70930823231513984531557301)
  ·
    refine ⟨6649764677954436049833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70930823231513984531557301 6649764677954436049833497)
    ·
      refine ⟨4987323508465827037375123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6649764677954436049833497 4987323508465827037375123)
      ·
        refine ⟨7480985262698740556062685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4987323508465827037375123 7480985262698740556062685)
        ·
          refine ⟨2805369473512027708523507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7480985262698740556062685 2805369473512027708523507)
          ·
            refine ⟨4208054210268041562785261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805369473512027708523507 4208054210268041562785261)
            ·
              refine ⟨1578020328850515586044473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208054210268041562785261 1578020328850515586044473)
              ·
                refine ⟨1183515246637886689533355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578020328850515586044473 1183515246637886689533355)
                ·
                  refine ⟨1775272869956830034300033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183515246637886689533355 1775272869956830034300033)
                  ·
                    refine ⟨1331454652467622525725025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775272869956830034300033 1331454652467622525725025)
                    ·
                      refine ⟨998590989350716894293769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331454652467622525725025 998590989350716894293769)
                      ·
                        rfl

theorem cell23_1944749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_1944749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944749 prefixEnd_1944749 := by exact prefixLift 1944749
  have htrace : WordTrace (prefixWord ++ tailWord_1944749) baseStart_1944749 baseEnd_1944749 := by
    simpa [prefixWord, tailWord_1944749, baseEnd_1944749] using wordTrace_append hprefix tailTrace_1944749
  have hstable : (prefixWord ++ tailWord_1944749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944749).length < 2 ^ (prefixWord ++ tailWord_1944749).sum := by decide
  have hdescent : baseEnd_1944749 < baseStart_1944749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944771 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 6, 2, 2]
def baseStart_1944771 : Nat := 118140960795 + 1944771 * 2 ^ 59
def prefixEnd_1944771 : Nat := 4983230072969 + 3 ^ 40 * 1944771 * 2
def baseEnd_1944771 : Nat := 998602285925115808218667

theorem tailTrace_1944771 : CollatzResearch.WordTrace tailWord_1944771 prefixEnd_1944771 998602285925115808218667 := by
  unfold tailWord_1944771
  simp only [CollatzResearch.WordTrace]
  refine ⟨70931625637434282288858167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47287750424956188192572111 70931625637434282288858167)
  ·
    refine ⟨106397438456151423433287251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70931625637434282288858167 106397438456151423433287251)
    ·
      refine ⟨159596157684227135149930877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106397438456151423433287251 159596157684227135149930877)
      ·
        refine ⟨59848559131585175681224079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159596157684227135149930877 59848559131585175681224079)
        ·
          refine ⟨89772838697377763521836119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59848559131585175681224079 89772838697377763521836119)
          ·
            refine ⟨134659258046066645282754179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89772838697377763521836119 134659258046066645282754179)
            ·
              refine ⟨201988887069099967924131269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134659258046066645282754179 201988887069099967924131269)
              ·
                refine ⟨37872916325456243985774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201988887069099967924131269 37872916325456243985774613)
                ·
                  refine ⟨1775292952755761436833185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37872916325456243985774613 1775292952755761436833185)
                  ·
                    refine ⟨1331469714566821077624889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775292952755761436833185 1331469714566821077624889)
                    ·
                      refine ⟨998602285925115808218667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331469714566821077624889 998602285925115808218667)
                      ·
                        rfl

theorem cell23_1944771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_1944771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944771 prefixEnd_1944771 := by exact prefixLift 1944771
  have htrace : WordTrace (prefixWord ++ tailWord_1944771) baseStart_1944771 baseEnd_1944771 := by
    simpa [prefixWord, tailWord_1944771, baseEnd_1944771] using wordTrace_append hprefix tailTrace_1944771
  have hstable : (prefixWord ++ tailWord_1944771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944771).length < 2 ^ (prefixWord ++ tailWord_1944771).sum := by decide
  have hdescent : baseEnd_1944771 < baseStart_1944771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944811 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 5]
def baseStart_1944811 : Nat := 118140960795 + 1944811 * 2 ^ 59
def prefixEnd_1944811 : Nat := 4983230072969 + 3 ^ 40 * 1944811 * 2
def baseEnd_1944811 : Nat := 110958091683477294635387

theorem tailTrace_1944811 : CollatzResearch.WordTrace tailWord_1944811 prefixEnd_1944811 110958091683477294635387 := by
  unfold tailWord_1944811
  simp only [CollatzResearch.WordTrace]
  refine ⟨70933084557289369120314287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47288723038192912746876191 70933084557289369120314287)
  ·
    refine ⟨106399626835934053680471431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70933084557289369120314287 106399626835934053680471431)
    ·
      refine ⟨159599440253901080520707147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106399626835934053680471431 159599440253901080520707147)
      ·
        refine ⟨239399160380851620781060721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159599440253901080520707147 239399160380851620781060721)
        ·
          refine ⟨179549370285638715585795541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239399160380851620781060721 179549370285638715585795541)
          ·
            refine ⟨4208188366069657396542083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 179549370285638715585795541 4208188366069657396542083)
            ·
              refine ⟨6312282549104486094813125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208188366069657396542083 6312282549104486094813125)
              ·
                refine ⟨1183552977957091142777461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6312282549104486094813125 1183552977957091142777461)
                ·
                  refine ⟨110958091683477294635387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183552977957091142777461 110958091683477294635387)
                  ·
                    rfl

theorem cell23_1944811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 5].length) (baseStart_1944811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944811 prefixEnd_1944811 := by exact prefixLift 1944811
  have htrace : WordTrace (prefixWord ++ tailWord_1944811) baseStart_1944811 baseEnd_1944811 := by
    simpa [prefixWord, tailWord_1944811, baseEnd_1944811] using wordTrace_append hprefix tailTrace_1944811
  have hstable : (prefixWord ++ tailWord_1944811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944811).length < 2 ^ (prefixWord ++ tailWord_1944811).sum := by decide
  have hdescent : baseEnd_1944811 < baseStart_1944811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944881 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1944881 : Nat := 118140960795 + 1944881 * 2 ^ 59
def prefixEnd_1944881 : Nat := 4983230072969 + 3 ^ 40 * 1944881 * 2
def baseEnd_1944881 : Nat := 998658768797110377843161

theorem tailTrace_1944881 : CollatzResearch.WordTrace tailWord_1944881 prefixEnd_1944881 998658768797110377843161 := by
  unfold tailWord_1944881
  simp only [CollatzResearch.WordTrace]
  refine ⟨70935637667035771075362497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47290425111357180716908331 70935637667035771075362497)
  ·
    refine ⟨53201728250276828306521873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70935637667035771075362497 53201728250276828306521873)
    ·
      refine ⟨39901296187707621229891405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53201728250276828306521873 39901296187707621229891405)
      ·
        refine ⟨14962986070390357961209277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39901296187707621229891405 14962986070390357961209277)
        ·
          refine ⟨5611119776396384235453479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14962986070390357961209277 5611119776396384235453479)
          ·
            refine ⟨8416679664594576353180219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611119776396384235453479 8416679664594576353180219)
            ·
              refine ⟨12625019496891864529770329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416679664594576353180219 12625019496891864529770329)
              ·
                refine ⟨9468764622668898397327747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12625019496891864529770329 9468764622668898397327747)
                ·
                  refine ⟨14203146934003347595991621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9468764622668898397327747 14203146934003347595991621)
                  ·
                    refine ⟨2663090050125627674248429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14203146934003347595991621 2663090050125627674248429)
                    ·
                      refine ⟨998658768797110377843161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663090050125627674248429 998658768797110377843161)
                      ·
                        rfl

theorem cell23_1944881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1944881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944881 prefixEnd_1944881 := by exact prefixLift 1944881
  have htrace : WordTrace (prefixWord ++ tailWord_1944881) baseStart_1944881 baseEnd_1944881 := by
    simpa [prefixWord, tailWord_1944881, baseEnd_1944881] using wordTrace_append hprefix tailTrace_1944881
  have hstable : (prefixWord ++ tailWord_1944881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944881).length < 2 ^ (prefixWord ++ tailWord_1944881).sum := by decide
  have hdescent : baseEnd_1944881 < baseStart_1944881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944935 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 6]
def baseStart_1944935 : Nat := 118140960795 + 1944935 * 2 ^ 59
def prefixEnd_1944935 : Nat := 4983230072969 + 3 ^ 40 * 1944935 * 2
def baseEnd_1944935 : Nat := 110965166305828129618657

theorem tailTrace_1944935 : CollatzResearch.WordTrace tailWord_1944935 prefixEnd_1944935 110965166305828129618657 := by
  unfold tailWord_1944935
  simp only [CollatzResearch.WordTrace]
  refine ⟨70937607208840138297828259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47291738139226758865218839 70937607208840138297828259)
  ·
    refine ⟨106406410813260207446742389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70937607208840138297828259 106406410813260207446742389)
    ·
      refine ⟨9975601013743144448132099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106406410813260207446742389 9975601013743144448132099)
      ·
        refine ⟨14963401520614716672198149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9975601013743144448132099 14963401520614716672198149)
        ·
          refine ⟨2805637785115259376037153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14963401520614716672198149 2805637785115259376037153)
          ·
            refine ⟨2104228338836444532027865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805637785115259376037153 2104228338836444532027865)
            ·
              refine ⟨1578171254127333399020899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104228338836444532027865 1578171254127333399020899)
              ·
                refine ⟨2367256881191000098531349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578171254127333399020899 2367256881191000098531349)
                ·
                  refine ⟨110965166305828129618657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2367256881191000098531349 110965166305828129618657)
                  ·
                    rfl

theorem cell23_1944935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 6].length) (baseStart_1944935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944935 prefixEnd_1944935 := by exact prefixLift 1944935
  have htrace : WordTrace (prefixWord ++ tailWord_1944935) baseStart_1944935 baseEnd_1944935 := by
    simpa [prefixWord, tailWord_1944935, baseEnd_1944935] using wordTrace_append hprefix tailTrace_1944935
  have hstable : (prefixWord ++ tailWord_1944935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944935).length < 2 ^ (prefixWord ++ tailWord_1944935).sum := by decide
  have hdescent : baseEnd_1944935 < baseStart_1944935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944951 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1944951 : Nat := 118140960795 + 1944951 * 2 ^ 59
def prefixEnd_1944951 : Nat := 4983230072969 + 3 ^ 40 * 1944951 * 2
def baseEnd_1944951 : Nat := 998694712442925103967839

theorem tailTrace_1944951 : CollatzResearch.WordTrace tailWord_1944951 prefixEnd_1944951 998694712442925103967839 := by
  unfold tailWord_1944951
  simp only [CollatzResearch.WordTrace]
  refine ⟨70938190776782173030410707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47292127184521448686940471 70938190776782173030410707)
  ·
    refine ⟨106407286165173259545616061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70938190776782173030410707 106407286165173259545616061)
    ·
      refine ⟨39902732311939972329606023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106407286165173259545616061 39902732311939972329606023)
      ·
        refine ⟨59854098467909958494409035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39902732311939972329606023 59854098467909958494409035)
        ·
          refine ⟨89781147701864937741613553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59854098467909958494409035 89781147701864937741613553)
          ·
            refine ⟨67335860776398703306210165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89781147701864937741613553 67335860776398703306210165)
            ·
              refine ⟨6312736947787378434957203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67335860776398703306210165 6312736947787378434957203)
              ·
                refine ⟨9469105421681067652435805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312736947787378434957203 9469105421681067652435805)
                ·
                  refine ⟨3550914533130400369663427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9469105421681067652435805 3550914533130400369663427)
                  ·
                    refine ⟨5326371799695600554495141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3550914533130400369663427 5326371799695600554495141)
                    ·
                      refine ⟨998694712442925103967839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5326371799695600554495141 998694712442925103967839)
                      ·
                        rfl

theorem cell23_1944951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1944951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944951 prefixEnd_1944951 := by exact prefixLift 1944951
  have htrace : WordTrace (prefixWord ++ tailWord_1944951) baseStart_1944951 baseEnd_1944951 := by
    simpa [prefixWord, tailWord_1944951, baseEnd_1944951] using wordTrace_append hprefix tailTrace_1944951
  have hstable : (prefixWord ++ tailWord_1944951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944951).length < 2 ^ (prefixWord ++ tailWord_1944951).sum := by decide
  have hdescent : baseEnd_1944951 < baseStart_1944951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944991 : List Nat := [1, 1, 2, 5, 1, 2, 3, 8]
def baseStart_1944991 : Nat := 118140960795 + 1944991 * 2 ^ 59
def prefixEnd_1944991 : Nat := 4983230072969 + 3 ^ 40 * 1944991 * 2
def baseEnd_1944991 : Nat := 36989453765522405461765

theorem tailTrace_1944991 : CollatzResearch.WordTrace tailWord_1944991 prefixEnd_1944991 36989453765522405461765 := by
  unfold tailWord_1944991
  simp only [CollatzResearch.WordTrace]
  refine ⟨70939649696637259861866827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47293099797758173241244551 70939649696637259861866827)
  ·
    refine ⟨106409474544955889792800241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70939649696637259861866827 106409474544955889792800241)
    ·
      refine ⟨79807105908716917344600181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106409474544955889792800241 79807105908716917344600181)
      ·
        refine ⟨7481916178942211001056267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79807105908716917344600181 7481916178942211001056267)
        ·
          refine ⟨11222874268413316501584401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7481916178942211001056267 11222874268413316501584401)
          ·
            refine ⟨8417155701309987376188301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222874268413316501584401 8417155701309987376188301)
            ·
              refine ⟨3156433387991245266070613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417155701309987376188301 3156433387991245266070613)
              ·
                refine ⟨36989453765522405461765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3156433387991245266070613 36989453765522405461765)
                ·
                  rfl

theorem cell23_1944991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 8].length) (baseStart_1944991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944991 prefixEnd_1944991 := by exact prefixLift 1944991
  have htrace : WordTrace (prefixWord ++ tailWord_1944991) baseStart_1944991 baseEnd_1944991 := by
    simpa [prefixWord, tailWord_1944991, baseEnd_1944991] using wordTrace_append hprefix tailTrace_1944991
  have hstable : (prefixWord ++ tailWord_1944991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944991).length < 2 ^ (prefixWord ++ tailWord_1944991).sum := by decide
  have hdescent : baseEnd_1944991 < baseStart_1944991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945005 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1945005 : Nat := 118140960795 + 1945005 * 2 ^ 59
def prefixEnd_1945005 : Nat := 4983230072969 + 3 ^ 40 * 1945005 * 2
def baseEnd_1945005 : Nat := 998722440398267892692591

theorem tailTrace_1945005 : CollatzResearch.WordTrace tailWord_1945005 prefixEnd_1945005 998722440398267892692591 := by
  unfold tailWord_1945005
  simp only [CollatzResearch.WordTrace]
  refine ⟨70940160318586540252876469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47293440212391026835250979 70940160318586540252876469)
  ·
    refine ⟨6650640029867488148707169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70940160318586540252876469 6650640029867488148707169)
    ·
      refine ⟨4987980022400616111530377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6650640029867488148707169 4987980022400616111530377)
      ·
        refine ⟨3740985016800462083647783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4987980022400616111530377 3740985016800462083647783)
        ·
          refine ⟨5611477525200693125471675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740985016800462083647783 5611477525200693125471675)
          ·
            refine ⟨8417216287801039688207513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611477525200693125471675 8417216287801039688207513)
            ·
              refine ⟨6312912215850779766155635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8417216287801039688207513 6312912215850779766155635)
              ·
                refine ⟨9469368323776169649233453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312912215850779766155635 9469368323776169649233453)
                ·
                  refine ⟨3551013121416063618462545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9469368323776169649233453 3551013121416063618462545)
                  ·
                    refine ⟨2663259841062047713846909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3551013121416063618462545 2663259841062047713846909)
                    ·
                      refine ⟨998722440398267892692591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663259841062047713846909 998722440398267892692591)
                      ·
                        rfl

theorem cell23_1945005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1945005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945005 prefixEnd_1945005 := by exact prefixLift 1945005
  have htrace : WordTrace (prefixWord ++ tailWord_1945005) baseStart_1945005 baseEnd_1945005 := by
    simpa [prefixWord, tailWord_1945005, baseEnd_1945005] using wordTrace_append hprefix tailTrace_1945005
  have hstable : (prefixWord ++ tailWord_1945005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945005).length < 2 ^ (prefixWord ++ tailWord_1945005).sum := by decide
  have hdescent : baseEnd_1945005 < baseStart_1945005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945035 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 3]
def baseStart_1945035 : Nat := 118140960795 + 1945035 * 2 ^ 59
def prefixEnd_1945035 : Nat := 4983230072969 + 3 ^ 40 * 1945035 * 2
def baseEnd_1945035 : Nat := 998737844817902775317453

theorem tailTrace_1945035 : CollatzResearch.WordTrace tailWord_1945035 prefixEnd_1945035 998737844817902775317453 := by
  unfold tailWord_1945035
  simp only [CollatzResearch.WordTrace]
  refine ⟨70941254508477855376468559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47294169672318570250979039 70941254508477855376468559)
  ·
    refine ⟨106411881762716783064702839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70941254508477855376468559 106411881762716783064702839)
    ·
      refine ⟨159617822644075174597054259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106411881762716783064702839 159617822644075174597054259)
      ·
        refine ⟨239426733966112761895581389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159617822644075174597054259 239426733966112761895581389)
        ·
          refine ⟨89785025237292285710843021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239426733966112761895581389 89785025237292285710843021)
          ·
            refine ⟨33669384463984607141566133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89785025237292285710843021 33669384463984607141566133)
            ·
              refine ⟨3156504793498556919521825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33669384463984607141566133 3156504793498556919521825)
              ·
                refine ⟨2367378595123917689641369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156504793498556919521825 2367378595123917689641369)
                ·
                  refine ⟨1775533946342938267231027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367378595123917689641369 1775533946342938267231027)
                  ·
                    refine ⟨2663300919514407400846541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775533946342938267231027 2663300919514407400846541)
                    ·
                      refine ⟨998737844817902775317453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663300919514407400846541 998737844817902775317453)
                      ·
                        rfl

theorem cell23_1945035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 3].length) (baseStart_1945035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945035 prefixEnd_1945035 := by exact prefixLift 1945035
  have htrace : WordTrace (prefixWord ++ tailWord_1945035) baseStart_1945035 baseEnd_1945035 := by
    simpa [prefixWord, tailWord_1945035, baseEnd_1945035] using wordTrace_append hprefix tailTrace_1945035
  have hstable : (prefixWord ++ tailWord_1945035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945035).length < 2 ^ (prefixWord ++ tailWord_1945035).sum := by decide
  have hdescent : baseEnd_1945035 < baseStart_1945035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945071 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_1945071 : Nat := 118140960795 + 1945071 * 2 ^ 59
def prefixEnd_1945071 : Nat := 4983230072969 + 3 ^ 40 * 1945071 * 2
def baseEnd_1945071 : Nat := 998756330121464634467287

theorem tailTrace_1945071 : CollatzResearch.WordTrace tailWord_1945071 prefixEnd_1945071 998756330121464634467287 := by
  unfold tailWord_1945071
  simp only [CollatzResearch.WordTrace]
  refine ⟨70942567536347433524779067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47295045024231622349852711 70942567536347433524779067)
  ·
    refine ⟨106413851304521150287168601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70942567536347433524779067 106413851304521150287168601)
    ·
      refine ⟨79810388478390862715376451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106413851304521150287168601 79810388478390862715376451)
      ·
        refine ⟨119715582717586294073064677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79810388478390862715376451 119715582717586294073064677)
        ·
          refine ⟨22446671759547430138699627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119715582717586294073064677 22446671759547430138699627)
          ·
            refine ⟨33670007639321145208049441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22446671759547430138699627 33670007639321145208049441)
            ·
              refine ⟨25252505729490858906037081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33670007639321145208049441 25252505729490858906037081)
              ·
                refine ⟨18939379297118144179527811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25252505729490858906037081 18939379297118144179527811)
                ·
                  refine ⟨28409068945677216269291717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18939379297118144179527811 28409068945677216269291717)
                  ·
                    refine ⟨5326700427314478050492197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28409068945677216269291717 5326700427314478050492197)
                    ·
                      refine ⟨998756330121464634467287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5326700427314478050492197 998756330121464634467287)
                      ·
                        rfl

theorem cell23_1945071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_1945071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945071 prefixEnd_1945071 := by exact prefixLift 1945071
  have htrace : WordTrace (prefixWord ++ tailWord_1945071) baseStart_1945071 baseEnd_1945071 := by
    simpa [prefixWord, tailWord_1945071, baseEnd_1945071] using wordTrace_append hprefix tailTrace_1945071
  have hstable : (prefixWord ++ tailWord_1945071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945071).length < 2 ^ (prefixWord ++ tailWord_1945071).sum := by decide
  have hdescent : baseEnd_1945071 < baseStart_1945071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945078 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1945078 : Nat := 118140960795 + 1945078 * 2 ^ 59
def prefixEnd_1945078 : Nat := 4983230072969 + 3 ^ 40 * 1945078 * 2
def baseEnd_1945078 : Nat := 998759924486046107079755

theorem tailTrace_1945078 : CollatzResearch.WordTrace tailWord_1945078 prefixEnd_1945078 998759924486046107079755 := by
  unfold tailWord_1945078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433926427957629607517743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47295215231548049146855925 4433926427957629607517743)
  ·
    refine ⟨6650889641936444411276615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433926427957629607517743 6650889641936444411276615)
    ·
      refine ⟨9976334462904666616914923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650889641936444411276615 9976334462904666616914923)
      ·
        refine ⟨14964501694356999925372385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9976334462904666616914923 14964501694356999925372385)
        ·
          refine ⟨11223376270767749944029289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964501694356999925372385 11223376270767749944029289)
          ·
            refine ⟨8417532203075812458021967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223376270767749944029289 8417532203075812458021967)
            ·
              refine ⟨12626298304613718687032951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417532203075812458021967 12626298304613718687032951)
              ·
                refine ⟨18939447456920578030549427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12626298304613718687032951 18939447456920578030549427)
                ·
                  refine ⟨28409171185380867045824141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18939447456920578030549427 28409171185380867045824141)
                  ·
                    refine ⟨10653439194517825142184053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28409171185380867045824141 10653439194517825142184053)
                    ·
                      refine ⟨998759924486046107079755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10653439194517825142184053 998759924486046107079755)
                      ·
                        rfl

theorem cell23_1945078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1945078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945078 prefixEnd_1945078 := by exact prefixLift 1945078
  have htrace : WordTrace (prefixWord ++ tailWord_1945078) baseStart_1945078 baseEnd_1945078 := by
    simpa [prefixWord, tailWord_1945078, baseEnd_1945078] using wordTrace_append hprefix tailTrace_1945078
  have hstable : (prefixWord ++ tailWord_1945078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945078).length < 2 ^ (prefixWord ++ tailWord_1945078).sum := by decide
  have hdescent : baseEnd_1945078 < baseStart_1945078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945098 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_1945098 : Nat := 118140960795 + 1945098 * 2 ^ 59
def prefixEnd_1945098 : Nat := 4983230072969 + 3 ^ 40 * 1945098 * 2
def baseEnd_1945098 : Nat := 110974466011015114314407

theorem tailTrace_1945098 : CollatzResearch.WordTrace tailWord_1945098 prefixEnd_1945098 110974466011015114314407 := by
  unfold tailWord_1945098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735888076812404284002987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47295701538166411424007965 17735888076812404284002987)
  ·
    refine ⟨26603832115218606426004481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17735888076812404284002987 26603832115218606426004481)
    ·
      refine ⟨19952874086413954819503361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26603832115218606426004481 19952874086413954819503361)
      ·
        refine ⟨14964655564810466114627521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19952874086413954819503361 14964655564810466114627521)
        ·
          refine ⟨11223491673607849585970641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964655564810466114627521 11223491673607849585970641)
          ·
            refine ⟨8417618755205887189477981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223491673607849585970641 8417618755205887189477981)
            ·
              refine ⟨3156607033202207696054243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417618755205887189477981 3156607033202207696054243)
              ·
                refine ⟨4734910549803311544081365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156607033202207696054243 4734910549803311544081365)
                ·
                  refine ⟨110974466011015114314407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4734910549803311544081365 110974466011015114314407)
                  ·
                    rfl

theorem cell23_1945098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_1945098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945098 prefixEnd_1945098 := by exact prefixLift 1945098
  have htrace : WordTrace (prefixWord ++ tailWord_1945098) baseStart_1945098 baseEnd_1945098 := by
    simpa [prefixWord, tailWord_1945098, baseEnd_1945098] using wordTrace_append hprefix tailTrace_1945098
  have hstable : (prefixWord ++ tailWord_1945098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945098).length < 2 ^ (prefixWord ++ tailWord_1945098).sum := by decide
  have hdescent : baseEnd_1945098 < baseStart_1945098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945109 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_1945109 : Nat := 118140960795 + 1945109 * 2 ^ 59
def prefixEnd_1945109 : Nat := 4983230072969 + 3 ^ 40 * 1945109 * 2
def baseEnd_1945109 : Nat := 998775842386335485792113

theorem tailTrace_1945109 : CollatzResearch.WordTrace tailWord_1945109 prefixEnd_1945109 998775842386335485792113 := by
  unfold tailWord_1945109
  simp only [CollatzResearch.WordTrace]
  refine ⟨70943953510209766014662381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47295969006806510676441587 70943953510209766014662381)
  ·
    refine ⟨26603982566328662255498393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70943953510209766014662381 26603982566328662255498393)
    ·
      refine ⟨19952986924746496691623795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26603982566328662255498393 19952986924746496691623795)
      ·
        refine ⟨29929480387119745037435693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952986924746496691623795 29929480387119745037435693)
        ·
          refine ⟨11223555145169904389038385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29929480387119745037435693 11223555145169904389038385)
          ·
            refine ⟨8417666358877428291778789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223555145169904389038385 8417666358877428291778789)
            ·
              refine ⟨1578312442289517804708523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8417666358877428291778789 1578312442289517804708523)
              ·
                refine ⟨2367468663434276707062785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578312442289517804708523 2367468663434276707062785)
                ·
                  refine ⟨1775601497575707530297089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2367468663434276707062785 1775601497575707530297089)
                  ·
                    refine ⟨1331701123181780647722817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1775601497575707530297089 1331701123181780647722817)
                    ·
                      refine ⟨998775842386335485792113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331701123181780647722817 998775842386335485792113)
                      ·
                        rfl

theorem cell23_1945109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_1945109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945109 prefixEnd_1945109 := by exact prefixLift 1945109
  have htrace : WordTrace (prefixWord ++ tailWord_1945109) baseStart_1945109 baseEnd_1945109 := by
    simpa [prefixWord, tailWord_1945109, baseEnd_1945109] using wordTrace_append hprefix tailTrace_1945109
  have hstable : (prefixWord ++ tailWord_1945109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945109).length < 2 ^ (prefixWord ++ tailWord_1945109).sum := by decide
  have hdescent : baseEnd_1945109 < baseStart_1945109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945149 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 5]
def baseStart_1945149 : Nat := 118140960795 + 1945149 * 2 ^ 59
def prefixEnd_1945149 : Nat := 4983230072969 + 3 ^ 40 * 1945149 * 2
def baseEnd_1945149 : Nat := 110977375734723925476881

theorem tailTrace_1945149 : CollatzResearch.WordTrace tailWord_1945149 prefixEnd_1945149 110977375734723925476881 := by
  unfold tailWord_1945149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70945412430064852846118501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47296941620043235230745667 70945412430064852846118501)
  ·
    refine ⟨13302264830637159908647219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70945412430064852846118501 13302264830637159908647219)
    ·
      refine ⟨19953397245955739862970829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13302264830637159908647219 19953397245955739862970829)
      ·
        refine ⟨7482523967233402448614061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19953397245955739862970829 7482523967233402448614061)
        ·
          refine ⟨2805946487712525918230273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7482523967233402448614061 2805946487712525918230273)
          ·
            refine ⟨2104459865784394438672705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805946487712525918230273 2104459865784394438672705)
            ·
              refine ⟨1578344899338295829004529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104459865784394438672705 1578344899338295829004529)
              ·
                refine ⟨1183758674503721871753397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578344899338295829004529 1183758674503721871753397)
                ·
                  refine ⟨110977375734723925476881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183758674503721871753397 110977375734723925476881)
                  ·
                    rfl

theorem cell23_1945149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_1945149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945149 prefixEnd_1945149 := by exact prefixLift 1945149
  have htrace : WordTrace (prefixWord ++ tailWord_1945149) baseStart_1945149 baseEnd_1945149 := by
    simpa [prefixWord, tailWord_1945149, baseEnd_1945149] using wordTrace_append hprefix tailTrace_1945149
  have hstable : (prefixWord ++ tailWord_1945149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945149).length < 2 ^ (prefixWord ++ tailWord_1945149).sum := by decide
  have hdescent : baseEnd_1945149 < baseStart_1945149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945168 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_1945168 : Nat := 118140960795 + 1945168 * 2 ^ 59
def prefixEnd_1945168 : Nat := 4983230072969 + 3 ^ 40 * 1945168 * 2
def baseEnd_1945168 : Nat := 998806137744950754954341

theorem tailTrace_1945168 : CollatzResearch.WordTrace tailWord_1945168 prefixEnd_1945168 998806137744950754954341 := by
  unfold tailWord_1945168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35473052708498009545530079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47297403611330679394040105 35473052708498009545530079)
  ·
    refine ⟨53209579062747014318295119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35473052708498009545530079 53209579062747014318295119)
    ·
      refine ⟨79814368594120521477442679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53209579062747014318295119 79814368594120521477442679)
      ·
        refine ⟨119721552891180782216164019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79814368594120521477442679 119721552891180782216164019)
        ·
          refine ⟨179582329336771173324246029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119721552891180782216164019 179582329336771173324246029)
          ·
            refine ⟨67343373501289189996592261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179582329336771173324246029 67343373501289189996592261)
            ·
              refine ⟨12626882531491723124361049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67343373501289189996592261 12626882531491723124361049)
              ·
                refine ⟨9470161898618792343270787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12626882531491723124361049 9470161898618792343270787)
                ·
                  refine ⟨14205242847928188514906181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470161898618792343270787 14205242847928188514906181)
                  ·
                    refine ⟨2663483033986535346544909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14205242847928188514906181 2663483033986535346544909)
                    ·
                      refine ⟨998806137744950754954341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663483033986535346544909 998806137744950754954341)
                      ·
                        rfl

theorem cell23_1945168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_1945168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945168 prefixEnd_1945168 := by exact prefixLift 1945168
  have htrace : WordTrace (prefixWord ++ tailWord_1945168) baseStart_1945168 baseEnd_1945168 := by
    simpa [prefixWord, tailWord_1945168, baseEnd_1945168] using wordTrace_append hprefix tailTrace_1945168
  have hstable : (prefixWord ++ tailWord_1945168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945168).length < 2 ^ (prefixWord ++ tailWord_1945168).sum := by decide
  have hdescent : baseEnd_1945168 < baseStart_1945168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945175 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 3, 4]
def baseStart_1945175 : Nat := 118140960795 + 1945175 * 2 ^ 59
def prefixEnd_1945175 : Nat := 4983230072969 + 3 ^ 40 * 1945175 * 2
def baseEnd_1945175 : Nat := 332936577369844075855603

theorem tailTrace_1945175 : CollatzResearch.WordTrace tailWord_1945175 prefixEnd_1945175 332936577369844075855603 := by
  unfold tailWord_1945175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70946360727970659286564979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47297573818647106191043319 70946360727970659286564979)
  ·
    refine ⟨106419541091955988929847469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70946360727970659286564979 106419541091955988929847469)
    ·
      refine ⟨39907327909483495848692801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106419541091955988929847469 39907327909483495848692801)
      ·
        refine ⟨29930495932112621886519601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39907327909483495848692801 29930495932112621886519601)
        ·
          refine ⟨22447871949084466414889701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29930495932112621886519601 22447871949084466414889701)
          ·
            refine ⟨4208975990453337452791819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22447871949084466414889701 4208975990453337452791819)
            ·
              refine ⟨6313463985680006179187729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208975990453337452791819 6313463985680006179187729)
              ·
                refine ⟨4735097989260004634390797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313463985680006179187729 4735097989260004634390797)
                ·
                  refine ⟨1775661745972501737896549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4735097989260004634390797 1775661745972501737896549)
                  ·
                    refine ⟨332936577369844075855603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1775661745972501737896549 332936577369844075855603)
                    ·
                      rfl

theorem cell23_1945175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_1945175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945175 prefixEnd_1945175 := by exact prefixLift 1945175
  have htrace : WordTrace (prefixWord ++ tailWord_1945175) baseStart_1945175 baseEnd_1945175 := by
    simpa [prefixWord, tailWord_1945175, baseEnd_1945175] using wordTrace_append hprefix tailTrace_1945175
  have hstable : (prefixWord ++ tailWord_1945175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945175).length < 2 ^ (prefixWord ++ tailWord_1945175).sum := by decide
  have hdescent : baseEnd_1945175 < baseStart_1945175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945205 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 8]
def baseStart_1945205 : Nat := 118140960795 + 1945205 * 2 ^ 59
def prefixEnd_1945205 : Nat := 4983230072969 + 3 ^ 40 * 1945205 * 2
def baseEnd_1945205 : Nat := 110980570725463012243519

theorem tailTrace_1945205 : CollatzResearch.WordTrace tailWord_1945205 prefixEnd_1945205 110980570725463012243519 := by
  unfold tailWord_1945205
  simp only [CollatzResearch.WordTrace]
  refine ⟨70947454917861974410157069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47298303278574649606771379 70947454917861974410157069)
  ·
    refine ⟨26605295594198240403808901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70947454917861974410157069 26605295594198240403808901)
    ·
      refine ⟨4988492923912170075714169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26605295594198240403808901 4988492923912170075714169)
      ·
        refine ⟨3741369692934127556785627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988492923912170075714169 3741369692934127556785627)
        ·
          refine ⟨5612054539401191335178441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741369692934127556785627 5612054539401191335178441)
          ·
            refine ⟨4209040904550893501383831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612054539401191335178441 4209040904550893501383831)
            ·
              refine ⟨6313561356826340252075747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209040904550893501383831 6313561356826340252075747)
              ·
                refine ⟨9470342035239510378113621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313561356826340252075747 9470342035239510378113621)
                ·
                  refine ⟨110980570725463012243519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9470342035239510378113621 110980570725463012243519)
                  ·
                    rfl

theorem cell23_1945205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_1945205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945205 prefixEnd_1945205 := by exact prefixLift 1945205
  have htrace : WordTrace (prefixWord ++ tailWord_1945205) baseStart_1945205 baseEnd_1945205 := by
    simpa [prefixWord, tailWord_1945205, baseEnd_1945205] using wordTrace_append hprefix tailTrace_1945205
  have hstable : (prefixWord ++ tailWord_1945205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945205).length < 2 ^ (prefixWord ++ tailWord_1945205).sum := by decide
  have hdescent : baseEnd_1945205 < baseStart_1945205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945225 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 5, 2]
def baseStart_1945225 : Nat := 118140960795 + 1945225 * 2 ^ 59
def prefixEnd_1945225 : Nat := 4983230072969 + 3 ^ 40 * 1945225 * 2
def baseEnd_1945225 : Nat := 998835406142257031941579

theorem tailTrace_1945225 : CollatzResearch.WordTrace tailWord_1945225 prefixEnd_1945225 998835406142257031941579 := by
  unfold tailWord_1945225
  simp only [CollatzResearch.WordTrace]
  refine ⟨70948184377789517825885129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47298789585193011883923419 70948184377789517825885129)
  ·
    refine ⟨53211138283342138369413847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70948184377789517825885129 53211138283342138369413847)
    ·
      refine ⟨79816707425013207554120771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53211138283342138369413847 79816707425013207554120771)
      ·
        refine ⟨119725061137519811331181157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79816707425013207554120771 119725061137519811331181157)
        ·
          refine ⟨22448448963284964624596467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119725061137519811331181157 22448448963284964624596467)
          ·
            refine ⟨33672673444927446936894701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22448448963284964624596467 33672673444927446936894701)
            ·
              refine ⟨12627252541847792601335513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33672673444927446936894701 12627252541847792601335513)
              ·
                refine ⟨9470439406385844451001635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12627252541847792601335513 9470439406385844451001635)
                ·
                  refine ⟨14205659109578766676502453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470439406385844451001635 14205659109578766676502453)
                  ·
                    refine ⟨1331780541523009375922105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14205659109578766676502453 1331780541523009375922105)
                    ·
                      refine ⟨998835406142257031941579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331780541523009375922105 998835406142257031941579)
                      ·
                        rfl

theorem cell23_1945225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5, 2].length) (baseStart_1945225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945225 prefixEnd_1945225 := by exact prefixLift 1945225
  have htrace : WordTrace (prefixWord ++ tailWord_1945225) baseStart_1945225 baseEnd_1945225 := by
    simpa [prefixWord, tailWord_1945225, baseEnd_1945225] using wordTrace_append hprefix tailTrace_1945225
  have hstable : (prefixWord ++ tailWord_1945225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945225).length < 2 ^ (prefixWord ++ tailWord_1945225).sum := by decide
  have hdescent : baseEnd_1945225 < baseStart_1945225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945286 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1945286 : Nat := 118140960795 + 1945286 * 2 ^ 59
def prefixEnd_1945286 : Nat := 4983230072969 + 3 ^ 40 * 1945286 * 2
def baseEnd_1945286 : Nat := 332955576154060431092933

theorem tailTrace_1945286 : CollatzResearch.WordTrace tailWord_1945286 prefixEnd_1945286 332955576154060431092933 := by
  unfold tailWord_1945286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217200288455266413870491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47300272820379016829237141 2217200288455266413870491)
  ·
    refine ⟨3325800432682899620805737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217200288455266413870491 3325800432682899620805737)
    ·
      refine ⟨2494350324512174715604303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325800432682899620805737 2494350324512174715604303)
      ·
        refine ⟨3741525486768262073406455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494350324512174715604303 3741525486768262073406455)
        ·
          refine ⟨5612288230152393110109683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741525486768262073406455 5612288230152393110109683)
          ·
            refine ⟨8418432345228589665164525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612288230152393110109683 8418432345228589665164525)
            ·
              refine ⟨3156912129460721124436697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8418432345228589665164525 3156912129460721124436697)
              ·
                refine ⟨2367684097095540843327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156912129460721124436697 2367684097095540843327523)
                ·
                  refine ⟨3551526145643311264991285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367684097095540843327523 3551526145643311264991285)
                  ·
                    refine ⟨332955576154060431092933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3551526145643311264991285 332955576154060431092933)
                    ·
                      rfl

theorem cell23_1945286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1945286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945286 prefixEnd_1945286 := by exact prefixLift 1945286
  have htrace : WordTrace (prefixWord ++ tailWord_1945286) baseStart_1945286 baseEnd_1945286 := by
    simpa [prefixWord, tailWord_1945286, baseEnd_1945286] using wordTrace_append hprefix tailTrace_1945286
  have hstable : (prefixWord ++ tailWord_1945286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945286).length < 2 ^ (prefixWord ++ tailWord_1945286).sum := by decide
  have hdescent : baseEnd_1945286 < baseStart_1945286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945305 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1945305 : Nat := 118140960795 + 1945305 * 2 ^ 59
def prefixEnd_1945305 : Nat := 4983230072969 + 3 ^ 40 * 1945305 * 2
def baseEnd_1945305 : Nat := 998876484594616718941211

theorem tailTrace_1945305 : CollatzResearch.WordTrace tailWord_1945305 prefixEnd_1945305 998876484594616718941211 := by
  unfold tailWord_1945305
  simp only [CollatzResearch.WordTrace]
  refine ⟨70951102217499691488797369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47300734811666460992531579 70951102217499691488797369)
  ·
    refine ⟨53213326663124768616598027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70951102217499691488797369 53213326663124768616598027)
    ·
      refine ⟨79819989994687152924897041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53213326663124768616598027 79819989994687152924897041)
      ·
        refine ⟨59864992496015364693672781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79819989994687152924897041 59864992496015364693672781)
        ·
          refine ⟨22449372186005761760127293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59864992496015364693672781 22449372186005761760127293)
          ·
            refine ⟨8418514569752160660047735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22449372186005761760127293 8418514569752160660047735)
            ·
              refine ⟨12627771854628240990071603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418514569752160660047735 12627771854628240990071603)
              ·
                refine ⟨18941657781942361485107405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627771854628240990071603 18941657781942361485107405)
                ·
                  refine ⟨7103121668228385556915277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18941657781942361485107405 7103121668228385556915277)
                  ·
                    refine ⟨2663670625585644583843229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7103121668228385556915277 2663670625585644583843229)
                    ·
                      refine ⟨998876484594616718941211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663670625585644583843229 998876484594616718941211)
                      ·
                        rfl

theorem cell23_1945305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1945305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945305 prefixEnd_1945305 := by exact prefixLift 1945305
  have htrace : WordTrace (prefixWord ++ tailWord_1945305) baseStart_1945305 baseEnd_1945305 := by
    simpa [prefixWord, tailWord_1945305, baseEnd_1945305] using wordTrace_append hprefix tailTrace_1945305
  have hstable : (prefixWord ++ tailWord_1945305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945305).length < 2 ^ (prefixWord ++ tailWord_1945305).sum := by decide
  have hdescent : baseEnd_1945305 < baseStart_1945305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945322 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1945322 : Nat := 118140960795 + 1945322 * 2 ^ 59
def prefixEnd_1945322 : Nat := 4983230072969 + 3 ^ 40 * 1945322 * 2
def baseEnd_1945322 : Nat := 998885213765743152428633

theorem tailTrace_1945322 : CollatzResearch.WordTrace tailWord_1945322 prefixEnd_1945322 998885213765743152428633 := by
  unfold tailWord_1945322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17737930564609525848041555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47301148172292068928110813 17737930564609525848041555)
  ·
    refine ⟨26606895846914288772062333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17737930564609525848041555 26606895846914288772062333)
    ·
      refine ⟨9977585942592858289523375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26606895846914288772062333 9977585942592858289523375)
      ·
        refine ⟨14966378913889287434285063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977585942592858289523375 14966378913889287434285063)
        ·
          refine ⟨22449568370833931151427595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966378913889287434285063 22449568370833931151427595)
          ·
            refine ⟨33674352556250896727141393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449568370833931151427595 33674352556250896727141393)
            ·
              refine ⟨25255764417188172545356045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33674352556250896727141393 25255764417188172545356045)
              ·
                refine ⟨9470911656445564704508517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255764417188172545356045 9470911656445564704508517)
                ·
                  refine ⟨1775795935583543382095347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9470911656445564704508517 1775795935583543382095347)
                  ·
                    refine ⟨2663693903375315073143021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775795935583543382095347 2663693903375315073143021)
                    ·
                      refine ⟨998885213765743152428633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663693903375315073143021 998885213765743152428633)
                      ·
                        rfl

theorem cell23_1945322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1945322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945322 prefixEnd_1945322 := by exact prefixLift 1945322
  have htrace : WordTrace (prefixWord ++ tailWord_1945322) baseStart_1945322 baseEnd_1945322 := by
    simpa [prefixWord, tailWord_1945322, baseEnd_1945322] using wordTrace_append hprefix tailTrace_1945322
  have hstable : (prefixWord ++ tailWord_1945322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945322).length < 2 ^ (prefixWord ++ tailWord_1945322).sum := by decide
  have hdescent : baseEnd_1945322 < baseStart_1945322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945325 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1945325 : Nat := 118140960795 + 1945325 * 2 ^ 59
def prefixEnd_1945325 : Nat := 4983230072969 + 3 ^ 40 * 1945325 * 2
def baseEnd_1945325 : Nat := 332962251402568880230373

theorem tailTrace_1945325 : CollatzResearch.WordTrace tailWord_1945325 prefixEnd_1945325 332962251402568880230373 := by
  unfold tailWord_1945325
  simp only [CollatzResearch.WordTrace]
  refine ⟨70951831677427234904525429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47301221118284823269683619 70951831677427234904525429)
  ·
    refine ⟨6651734219758803272299259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70951831677427234904525429 6651734219758803272299259)
    ·
      refine ⟨9977601329638204908448889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651734219758803272299259 9977601329638204908448889)
      ·
        refine ⟨7483200997228653681336667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9977601329638204908448889 7483200997228653681336667)
        ·
          refine ⟨11224801495842980522005001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483200997228653681336667 11224801495842980522005001)
          ·
            refine ⟨8418601121882235391503751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11224801495842980522005001 8418601121882235391503751)
            ·
              refine ⟨12627901682823353087255627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418601121882235391503751 12627901682823353087255627)
              ·
                refine ⟨18941852524235029630883441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627901682823353087255627 18941852524235029630883441)
                ·
                  refine ⟨14206389393176272223162581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18941852524235029630883441 14206389393176272223162581)
                  ·
                    refine ⟨332962251402568880230373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14206389393176272223162581 332962251402568880230373)
                    ·
                      rfl

theorem cell23_1945325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1945325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945325 prefixEnd_1945325 := by exact prefixLift 1945325
  have htrace : WordTrace (prefixWord ++ tailWord_1945325) baseStart_1945325 baseEnd_1945325 := by
    simpa [prefixWord, tailWord_1945325, baseEnd_1945325] using wordTrace_append hprefix tailTrace_1945325
  have hstable : (prefixWord ++ tailWord_1945325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945325).length < 2 ^ (prefixWord ++ tailWord_1945325).sum := by decide
  have hdescent : baseEnd_1945325 < baseStart_1945325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945357 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1945357 : Nat := 118140960795 + 1945357 * 2 ^ 59
def prefixEnd_1945357 : Nat := 4983230072969 + 3 ^ 40 * 1945357 * 2
def baseEnd_1945357 : Nat := 998903185588650515490973

theorem tailTrace_1945357 : CollatzResearch.WordTrace tailWord_1945357 prefixEnd_1945357 998903185588650515490973 := by
  unfold tailWord_1945357
  simp only [CollatzResearch.WordTrace]
  refine ⟨70952998813311304369690325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47301999208874202913126883 70952998813311304369690325)
  ·
    refine ⟨1662960909686983696164617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70952998813311304369690325 1662960909686983696164617)
    ·
      refine ⟨1247220682265237772123463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662960909686983696164617 1247220682265237772123463)
      ·
        refine ⟨1870831023397856658185195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247220682265237772123463 1870831023397856658185195)
        ·
          refine ⟨2806246535096784987277793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870831023397856658185195 2806246535096784987277793)
          ·
            refine ⟨2104684901322588740458345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806246535096784987277793 2104684901322588740458345)
            ·
              refine ⟨1578513675991941555343759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104684901322588740458345 1578513675991941555343759)
              ·
                refine ⟨2367770513987912333015639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578513675991941555343759 2367770513987912333015639)
                ·
                  refine ⟨3551655770981868499523459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367770513987912333015639 3551655770981868499523459)
                  ·
                    refine ⟨5327483656472802749285189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3551655770981868499523459 5327483656472802749285189)
                    ·
                      refine ⟨998903185588650515490973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5327483656472802749285189 998903185588650515490973)
                      ·
                        rfl

theorem cell23_1945357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1945357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945357 prefixEnd_1945357 := by exact prefixLift 1945357
  have htrace : WordTrace (prefixWord ++ tailWord_1945357) baseStart_1945357 baseEnd_1945357 := by
    simpa [prefixWord, tailWord_1945357, baseEnd_1945357] using wordTrace_append hprefix tailTrace_1945357
  have hstable : (prefixWord ++ tailWord_1945357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945357).length < 2 ^ (prefixWord ++ tailWord_1945357).sum := by decide
  have hdescent : baseEnd_1945357 < baseStart_1945357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945375 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1945375 : Nat := 118140960795 + 1945375 * 2 ^ 59
def prefixEnd_1945375 : Nat := 4983230072969 + 3 ^ 40 * 1945375 * 2
def baseEnd_1945375 : Nat := 998912428240431445065889

theorem tailTrace_1945375 : CollatzResearch.WordTrace tailWord_1945375 prefixEnd_1945375 998912428240431445065889 := by
  unfold tailWord_1945375
  simp only [CollatzResearch.WordTrace]
  refine ⟨70953655327246093443845579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47302436884830728962563719 70953655327246093443845579)
  ·
    refine ⟨106430482990869140165768369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70953655327246093443845579 106430482990869140165768369)
    ·
      refine ⟨79822862243151855124326277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106430482990869140165768369 79822862243151855124326277)
      ·
        refine ⟨14966786670590972835811177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79822862243151855124326277 14966786670590972835811177)
        ·
          refine ⟨11225090002943229626858383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14966786670590972835811177 11225090002943229626858383)
          ·
            refine ⟨16837635004414844440287575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225090002943229626858383 16837635004414844440287575)
            ·
              refine ⟨25256452506622266660431363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837635004414844440287575 25256452506622266660431363)
              ·
                refine ⟨37884678759933399990647045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25256452506622266660431363 37884678759933399990647045)
                ·
                  refine ⟨7103377267487512498246321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37884678759933399990647045 7103377267487512498246321)
                  ·
                    refine ⟨5327532950615634373684741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103377267487512498246321 5327532950615634373684741)
                    ·
                      refine ⟨998912428240431445065889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5327532950615634373684741 998912428240431445065889)
                      ·
                        rfl

theorem cell23_1945375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1945375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945375 prefixEnd_1945375 := by exact prefixLift 1945375
  have htrace : WordTrace (prefixWord ++ tailWord_1945375) baseStart_1945375 baseEnd_1945375 := by
    simpa [prefixWord, tailWord_1945375, baseEnd_1945375] using wordTrace_append hprefix tailTrace_1945375
  have hstable : (prefixWord ++ tailWord_1945375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945375).length < 2 ^ (prefixWord ++ tailWord_1945375).sum := by decide
  have hdescent : baseEnd_1945375 < baseStart_1945375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945396 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_1945396 : Nat := 118140960795 + 1945396 * 2 ^ 59
def prefixEnd_1945396 : Nat := 4983230072969 + 3 ^ 40 * 1945396 * 2
def baseEnd_1945396 : Nat := 998923211334175862903293

theorem tailTrace_1945396 : CollatzResearch.WordTrace tailWord_1945396 prefixEnd_1945396 998923211334175862903293 := by
  unfold tailWord_1945396
  simp only [CollatzResearch.WordTrace]
  refine ⟨35477210630085007015180021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47302947506780009353573361 35477210630085007015180021)
  ·
    refine ⟨3325988496570469407673127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35477210630085007015180021 3325988496570469407673127)
    ·
      refine ⟨4988982744855704111509691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325988496570469407673127 4988982744855704111509691)
      ·
        refine ⟨7483474117283556167264537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988982744855704111509691 7483474117283556167264537)
        ·
          refine ⟨5612605587962667125448403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7483474117283556167264537 5612605587962667125448403)
          ·
            refine ⟨8418908381944000688172605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612605587962667125448403 8418908381944000688172605)
            ·
              refine ⟨3157090643229000258064727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8418908381944000688172605 3157090643229000258064727)
              ·
                refine ⟨4735635964843500387097091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157090643229000258064727 4735635964843500387097091)
                ·
                  refine ⟨7103453947265250580645637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735635964843500387097091 7103453947265250580645637)
                  ·
                    refine ⟨1331897615112234483871057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103453947265250580645637 1331897615112234483871057)
                    ·
                      refine ⟨998923211334175862903293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331897615112234483871057 998923211334175862903293)
                      ·
                        rfl

theorem cell23_1945396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_1945396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945396 prefixEnd_1945396 := by exact prefixLift 1945396
  have htrace : WordTrace (prefixWord ++ tailWord_1945396) baseStart_1945396 baseEnd_1945396 := by
    simpa [prefixWord, tailWord_1945396, baseEnd_1945396] using wordTrace_append hprefix tailTrace_1945396
  have hstable : (prefixWord ++ tailWord_1945396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945396).length < 2 ^ (prefixWord ++ tailWord_1945396).sum := by decide
  have hdescent : baseEnd_1945396 < baseStart_1945396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945415 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1945415 : Nat := 118140960795 + 1945415 * 2 ^ 59
def prefixEnd_1945415 : Nat := 4983230072969 + 3 ^ 40 * 1945415 * 2
def baseEnd_1945415 : Nat := 332977655822203762855235

theorem tailTrace_1945415 : CollatzResearch.WordTrace tailWord_1945415 prefixEnd_1945415 332977655822203762855235 := by
  unfold tailWord_1945415
  simp only [CollatzResearch.WordTrace]
  refine ⟨70955114247101180275301699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47303409498067453516867799 70955114247101180275301699)
  ·
    refine ⟨106432671370651770412952549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70955114247101180275301699 106432671370651770412952549)
    ·
      refine ⟨19956125881997206952428603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106432671370651770412952549 19956125881997206952428603)
      ·
        refine ⟨29934188822995810428642905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19956125881997206952428603 29934188822995810428642905)
        ·
          refine ⟨22450641617246857821482179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29934188822995810428642905 22450641617246857821482179)
          ·
            refine ⟨33675962425870286732223269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22450641617246857821482179 33675962425870286732223269)
            ·
              refine ⟨6314242954850678762291863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33675962425870286732223269 6314242954850678762291863)
              ·
                refine ⟨9471364432276018143437795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314242954850678762291863 9471364432276018143437795)
                ·
                  refine ⟨14207046648414027215156693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471364432276018143437795 14207046648414027215156693)
                  ·
                    refine ⟨332977655822203762855235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14207046648414027215156693 332977655822203762855235)
                    ·
                      rfl

theorem cell23_1945415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1945415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945415 prefixEnd_1945415 := by exact prefixLift 1945415
  have htrace : WordTrace (prefixWord ++ tailWord_1945415) baseStart_1945415 baseEnd_1945415 := by
    simpa [prefixWord, tailWord_1945415, baseEnd_1945415] using wordTrace_append hprefix tailTrace_1945415
  have hstable : (prefixWord ++ tailWord_1945415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945415).length < 2 ^ (prefixWord ++ tailWord_1945415).sum := by decide
  have hdescent : baseEnd_1945415 < baseStart_1945415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945422 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_1945422 : Nat := 118140960795 + 1945422 * 2 ^ 59
def prefixEnd_1945422 : Nat := 4983230072969 + 3 ^ 40 * 1945422 * 2
def baseEnd_1945422 : Nat := 998936561831192761178173

theorem tailTrace_1945422 : CollatzResearch.WordTrace tailWord_1945422 prefixEnd_1945422 998936561831192761178173 := by
  unfold tailWord_1945422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869421194759477558850815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47303579705383880313871013 8869421194759477558850815)
  ·
    refine ⟨13304131792139216338276223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8869421194759477558850815 13304131792139216338276223)
    ·
      refine ⟨19956197688208824507414335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304131792139216338276223 19956197688208824507414335)
      ·
        refine ⟨29934296532313236761121503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19956197688208824507414335 29934296532313236761121503)
        ·
          refine ⟨44901444798469855141682255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29934296532313236761121503 44901444798469855141682255)
          ·
            refine ⟨67352167197704782712523383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44901444798469855141682255 67352167197704782712523383)
            ·
              refine ⟨101028250796557174068785075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67352167197704782712523383 101028250796557174068785075)
              ·
                refine ⟨151542376194835761103177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101028250796557174068785075 151542376194835761103177613)
                ·
                  refine ⟨56828391073063410413691605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151542376194835761103177613 56828391073063410413691605)
                  ·
                    refine ⟨1331915415774923681570897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56828391073063410413691605 1331915415774923681570897)
                    ·
                      refine ⟨998936561831192761178173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331915415774923681570897 998936561831192761178173)
                      ·
                        rfl

theorem cell23_1945422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_1945422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945422 prefixEnd_1945422 := by exact prefixLift 1945422
  have htrace : WordTrace (prefixWord ++ tailWord_1945422) baseStart_1945422 baseEnd_1945422 := by
    simpa [prefixWord, tailWord_1945422, baseEnd_1945422] using wordTrace_append hprefix tailTrace_1945422
  have hstable : (prefixWord ++ tailWord_1945422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945422).length < 2 ^ (prefixWord ++ tailWord_1945422).sum := by decide
  have hdescent : baseEnd_1945422 < baseStart_1945422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945436 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 7]
def baseStart_1945436 : Nat := 118140960795 + 1945436 * 2 ^ 59
def prefixEnd_1945436 : Nat := 4983230072969 + 3 ^ 40 * 1945436 * 2
def baseEnd_1945436 : Nat := 110993750062261745155901

theorem tailTrace_1945436 : CollatzResearch.WordTrace tailWord_1945436 prefixEnd_1945436 110993750062261745155901 := by
  unfold tailWord_1945436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35477940090012550430908081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47303920120016733907877441 35477940090012550430908081)
  ·
    refine ⟨26608455067509412823181061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35477940090012550430908081 26608455067509412823181061)
    ·
      refine ⟨4989085325158014904346449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26608455067509412823181061 4989085325158014904346449)
      ·
        refine ⟨3741813993868511178259837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989085325158014904346449 3741813993868511178259837)
        ·
          refine ⟨1403180247700691691847439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3741813993868511178259837 1403180247700691691847439)
          ·
            refine ⟨2104770371551037537771159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403180247700691691847439 2104770371551037537771159)
            ·
              refine ⟨3157155557326556306656739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104770371551037537771159 3157155557326556306656739)
              ·
                refine ⟨4735733335989834459985109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157155557326556306656739 4735733335989834459985109)
                ·
                  refine ⟨110993750062261745155901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4735733335989834459985109 110993750062261745155901)
                  ·
                    rfl

theorem cell23_1945436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_1945436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945436 prefixEnd_1945436 := by exact prefixLift 1945436
  have htrace : WordTrace (prefixWord ++ tailWord_1945436) baseStart_1945436 baseEnd_1945436 := by
    simpa [prefixWord, tailWord_1945436, baseEnd_1945436] using wordTrace_append hprefix tailTrace_1945436
  have hstable : (prefixWord ++ tailWord_1945436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945436).length < 2 ^ (prefixWord ++ tailWord_1945436).sum := by decide
  have hdescent : baseEnd_1945436 < baseStart_1945436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945442 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1945442 : Nat := 118140960795 + 1945442 * 2 ^ 59
def prefixEnd_1945442 : Nat := 4983230072969 + 3 ^ 40 * 1945442 * 2
def baseEnd_1945442 : Nat := 998946831444282682928081

theorem tailTrace_1945442 : CollatzResearch.WordTrace tailWord_1945442 prefixEnd_1945442 998946831444282682928081 := by
  unfold tailWord_1945442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739024754500840971633645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47304066012002242591023053 17739024754500840971633645)
  ·
    refine ⟨6652134282937815364362617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17739024754500840971633645 6652134282937815364362617)
    ·
      refine ⟨4989100712203361523271963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6652134282937815364362617 4989100712203361523271963)
      ·
        refine ⟨7483651068305042284907945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989100712203361523271963 7483651068305042284907945)
        ·
          refine ⟨5612738301228781713680959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7483651068305042284907945 5612738301228781713680959)
          ·
            refine ⟨8419107451843172570521439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612738301228781713680959 8419107451843172570521439)
            ·
              refine ⟨12628661177764758855782159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419107451843172570521439 12628661177764758855782159)
              ·
                refine ⟨18942991766647138283673239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12628661177764758855782159 18942991766647138283673239)
                ·
                  refine ⟨28414487649970707425509859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18942991766647138283673239 28414487649970707425509859)
                  ·
                    refine ⟨42621731474956061138264789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28414487649970707425509859 42621731474956061138264789)
                    ·
                      refine ⟨998946831444282682928081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42621731474956061138264789 998946831444282682928081)
                      ·
                        rfl

theorem cell23_1945442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1945442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945442 prefixEnd_1945442 := by exact prefixLift 1945442
  have htrace : WordTrace (prefixWord ++ tailWord_1945442) baseStart_1945442 baseEnd_1945442 := by
    simpa [prefixWord, tailWord_1945442, baseEnd_1945442] using wordTrace_append hprefix tailTrace_1945442
  have hstable : (prefixWord ++ tailWord_1945442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945442).length < 2 ^ (prefixWord ++ tailWord_1945442).sum := by decide
  have hdescent : baseEnd_1945442 < baseStart_1945442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945519 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_1945519 : Nat := 118140960795 + 1945519 * 2 ^ 59
def prefixEnd_1945519 : Nat := 4983230072969 + 3 ^ 40 * 1945519 * 2
def baseEnd_1945519 : Nat := 998986369454678881665227

theorem tailTrace_1945519 : CollatzResearch.WordTrace tailWord_1945519 prefixEnd_1945519 998986369454678881665227 := by
  unfold tailWord_1945519
  simp only [CollatzResearch.WordTrace]
  refine ⟨70958907438724406037087611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47305938292482937358058407 70958907438724406037087611)
  ·
    refine ⟨106438361158086609055631417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70958907438724406037087611 106438361158086609055631417)
    ·
      refine ⟨79828770868564956791723563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106438361158086609055631417 79828770868564956791723563)
      ·
        refine ⟨119743156302847435187585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79828770868564956791723563 119743156302847435187585345)
        ·
          refine ⟨89807367227135576390689009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119743156302847435187585345 89807367227135576390689009)
          ·
            refine ⟨67355525420351682293016757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89807367227135576390689009 67355525420351682293016757)
            ·
              refine ⟨6314580508157970214970321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67355525420351682293016757 6314580508157970214970321)
              ·
                refine ⟨4735935381118477661227741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314580508157970214970321 4735935381118477661227741)
                ·
                  refine ⟨1775975767919429122960403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4735935381118477661227741 1775975767919429122960403)
                  ·
                    refine ⟨2663963651879143684440605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1775975767919429122960403 2663963651879143684440605)
                    ·
                      refine ⟨998986369454678881665227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2663963651879143684440605 998986369454678881665227)
                      ·
                        rfl

theorem cell23_1945519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_1945519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945519 prefixEnd_1945519 := by exact prefixLift 1945519
  have htrace : WordTrace (prefixWord ++ tailWord_1945519) baseStart_1945519 baseEnd_1945519 := by
    simpa [prefixWord, tailWord_1945519, baseEnd_1945519] using wordTrace_append hprefix tailTrace_1945519
  have hstable : (prefixWord ++ tailWord_1945519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945519).length < 2 ^ (prefixWord ++ tailWord_1945519).sum := by decide
  have hdescent : baseEnd_1945519 < baseStart_1945519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945529 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 5, 2]
def baseStart_1945529 : Nat := 118140960795 + 1945529 * 2 ^ 59
def prefixEnd_1945529 : Nat := 4983230072969 + 3 ^ 40 * 1945529 * 2
def baseEnd_1945529 : Nat := 998991504261223842540181

theorem tailTrace_1945529 : CollatzResearch.WordTrace tailWord_1945529 prefixEnd_1945529 998991504261223842540181 := by
  unfold tailWord_1945529
  simp only [CollatzResearch.WordTrace]
  refine ⟨70959272168688177744951641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47306181445792118496634427 70959272168688177744951641)
  ·
    refine ⟨53219454126516133308713731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70959272168688177744951641 53219454126516133308713731)
    ·
      refine ⟨79829181189774199963070597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53219454126516133308713731 79829181189774199963070597)
      ·
        refine ⟨14967971473082662493075737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79829181189774199963070597 14967971473082662493075737)
        ·
          refine ⟨11225978604811996869806803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967971473082662493075737 11225978604811996869806803)
          ·
            refine ⟨16838967907217995304710205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225978604811996869806803 16838967907217995304710205)
            ·
              refine ⟨6314612965206748239266327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16838967907217995304710205 6314612965206748239266327)
              ·
                refine ⟨9471919447810122358899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314612965206748239266327 9471919447810122358899491)
                ·
                  refine ⟨14207879171715183538349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471919447810122358899491 14207879171715183538349237)
                  ·
                    refine ⟨1331988672348298456720241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14207879171715183538349237 1331988672348298456720241)
                    ·
                      refine ⟨998991504261223842540181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331988672348298456720241 998991504261223842540181)
                      ·
                        rfl

theorem cell23_1945529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_1945529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945529 prefixEnd_1945529 := by exact prefixLift 1945529
  have htrace : WordTrace (prefixWord ++ tailWord_1945529) baseStart_1945529 baseEnd_1945529 := by
    simpa [prefixWord, tailWord_1945529, baseEnd_1945529] using wordTrace_append hprefix tailTrace_1945529
  have hstable : (prefixWord ++ tailWord_1945529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945529).length < 2 ^ (prefixWord ++ tailWord_1945529).sum := by decide
  have hdescent : baseEnd_1945529 < baseStart_1945529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945569 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1945569 : Nat := 118140960795 + 1945569 * 2 ^ 59
def prefixEnd_1945569 : Nat := 4983230072969 + 3 ^ 40 * 1945569 * 2
def baseEnd_1945569 : Nat := 333004014495801228679999

theorem tailTrace_1945569 : CollatzResearch.WordTrace tailWord_1945569 prefixEnd_1945569 333004014495801228679999 := by
  unfold tailWord_1945569
  simp only [CollatzResearch.WordTrace]
  refine ⟨70960731088543264576407761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47307154059028843050938507 70960731088543264576407761)
  ·
    refine ⟨53220548316407448432305821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70960731088543264576407761 53220548316407448432305821)
    ·
      refine ⟨19957705618652793162114683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53220548316407448432305821 19957705618652793162114683)
      ·
        refine ⟨29936558427979189743172025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19957705618652793162114683 29936558427979189743172025)
        ·
          refine ⟨22452418820984392307379019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29936558427979189743172025 22452418820984392307379019)
          ·
            refine ⟨33678628231476588461068529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22452418820984392307379019 33678628231476588461068529)
            ·
              refine ⟨25258971173607441345801397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33678628231476588461068529 25258971173607441345801397)
              ·
                refine ⟨2368028547525697626168881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25258971173607441345801397 2368028547525697626168881)
                ·
                  refine ⟨1776021410644273219626661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368028547525697626168881 1776021410644273219626661)
                  ·
                    refine ⟨333004014495801228679999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776021410644273219626661 333004014495801228679999)
                    ·
                      rfl

theorem cell23_1945569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1945569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945569 prefixEnd_1945569 := by exact prefixLift 1945569
  have htrace : WordTrace (prefixWord ++ tailWord_1945569) baseStart_1945569 baseEnd_1945569 := by
    simpa [prefixWord, tailWord_1945569, baseEnd_1945569] using wordTrace_append hprefix tailTrace_1945569
  have hstable : (prefixWord ++ tailWord_1945569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945569).length < 2 ^ (prefixWord ++ tailWord_1945569).sum := by decide
  have hdescent : baseEnd_1945569 < baseStart_1945569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945572 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1945572 : Nat := 118140960795 + 1945572 * 2 ^ 59
def prefixEnd_1945572 : Nat := 4983230072969 + 3 ^ 40 * 1945572 * 2
def baseEnd_1945572 : Nat := 999013583929367174302483

theorem tailTrace_1945572 : CollatzResearch.WordTrace tailWord_1945572 prefixEnd_1945572 999013583929367174302483 := by
  unfold tailWord_1945572
  simp only [CollatzResearch.WordTrace]
  refine ⟨35480420253766198044383485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47307227005021597392511313 35480420253766198044383485)
  ·
    refine ⟨13305157595162324266643807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35480420253766198044383485 13305157595162324266643807)
    ·
      refine ⟨19957736392743486399965711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13305157595162324266643807 19957736392743486399965711)
      ·
        refine ⟨29936604589115229599948567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19957736392743486399965711 29936604589115229599948567)
        ·
          refine ⟨44904906883672844399922851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29936604589115229599948567 44904906883672844399922851)
          ·
            refine ⟨67357360325509266599884277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44904906883672844399922851 67357360325509266599884277)
            ·
              refine ⟨6314752530516493743739151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67357360325509266599884277 6314752530516493743739151)
              ·
                refine ⟨9472128795774740615608727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314752530516493743739151 9472128795774740615608727)
                ·
                  refine ⟨14208193193662110923413091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9472128795774740615608727 14208193193662110923413091)
                  ·
                    refine ⟨21312289790493166385119637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14208193193662110923413091 21312289790493166385119637)
                    ·
                      refine ⟨999013583929367174302483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21312289790493166385119637 999013583929367174302483)
                      ·
                        rfl

theorem cell23_1945572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1945572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945572 prefixEnd_1945572 := by exact prefixLift 1945572
  have htrace : WordTrace (prefixWord ++ tailWord_1945572) baseStart_1945572 baseEnd_1945572 := by
    simpa [prefixWord, tailWord_1945572, baseEnd_1945572] using wordTrace_append hprefix tailTrace_1945572
  have hstable : (prefixWord ++ tailWord_1945572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945572).length < 2 ^ (prefixWord ++ tailWord_1945572).sum := by decide
  have hdescent : baseEnd_1945572 < baseStart_1945572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945610 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1945610 : Nat := 118140960795 + 1945610 * 2 ^ 59
def prefixEnd_1945610 : Nat := 4983230072969 + 3 ^ 40 * 1945610 * 2
def baseEnd_1945610 : Nat := 999033096194238025627309

theorem tailTrace_1945610 : CollatzResearch.WordTrace tailWord_1945610 prefixEnd_1945610 999033096194238025627309 := by
  unfold tailWord_1945610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740556620348682144662571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47308150987596485719100189 17740556620348682144662571)
  ·
    refine ⟨26610834930523023216993857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17740556620348682144662571 26610834930523023216993857)
    ·
      refine ⟨19958126197892267412745393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26610834930523023216993857 19958126197892267412745393)
      ·
        refine ⟨14968594648419200559559045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19958126197892267412745393 14968594648419200559559045)
        ·
          refine ⟨2806611496578600104917321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14968594648419200559559045 2806611496578600104917321)
          ·
            refine ⟨2104958622433950078687991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806611496578600104917321 2104958622433950078687991)
            ·
              refine ⟨3157437933650925118031987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104958622433950078687991 3157437933650925118031987)
              ·
                refine ⟨4736156900476387677047981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157437933650925118031987 4736156900476387677047981)
                ·
                  refine ⟨1776058837678645378892993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4736156900476387677047981 1776058837678645378892993)
                  ·
                    refine ⟨1332044128258984034169745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776058837678645378892993 1332044128258984034169745)
                    ·
                      refine ⟨999033096194238025627309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332044128258984034169745 999033096194238025627309)
                      ·
                        rfl

theorem cell23_1945610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1945610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945610 prefixEnd_1945610 := by exact prefixLift 1945610
  have htrace : WordTrace (prefixWord ++ tailWord_1945610) baseStart_1945610 baseEnd_1945610 := by
    simpa [prefixWord, tailWord_1945610, baseEnd_1945610] using wordTrace_append hprefix tailTrace_1945610
  have hstable : (prefixWord ++ tailWord_1945610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945610).length < 2 ^ (prefixWord ++ tailWord_1945610).sum := by decide
  have hdescent : baseEnd_1945610 < baseStart_1945610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945612 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1945612 : Nat := 118140960795 + 1945612 * 2 ^ 59
def prefixEnd_1945612 : Nat := 4983230072969 + 3 ^ 40 * 1945612 * 2
def baseEnd_1945612 : Nat := 333011374385182339267433

theorem tailTrace_1945612 : CollatzResearch.WordTrace tailWord_1945612 prefixEnd_1945612 333011374385182339267433 := by
  unfold tailWord_1945612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35481149713693741460111545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47308199618258321946815393 35481149713693741460111545)
  ·
    refine ⟨26610862285270306095083659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35481149713693741460111545 26610862285270306095083659)
    ·
      refine ⟨39916293427905459142625489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26610862285270306095083659 39916293427905459142625489)
      ·
        refine ⟨29937220070929094356969117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39916293427905459142625489 29937220070929094356969117)
        ·
          refine ⟨11226457526598410383863419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29937220070929094356969117 11226457526598410383863419)
          ·
            refine ⟨16839686289897615575795129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11226457526598410383863419 16839686289897615575795129)
            ·
              refine ⟨12629764717423211681846347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16839686289897615575795129 12629764717423211681846347)
              ·
                refine ⟨18944647076134817522769521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12629764717423211681846347 18944647076134817522769521)
                ·
                  refine ⟨14208485307101113142077141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18944647076134817522769521 14208485307101113142077141)
                  ·
                    refine ⟨333011374385182339267433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14208485307101113142077141 333011374385182339267433)
                    ·
                      rfl

theorem cell23_1945612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1945612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945612 prefixEnd_1945612 := by exact prefixLift 1945612
  have htrace : WordTrace (prefixWord ++ tailWord_1945612) baseStart_1945612 baseEnd_1945612 := by
    simpa [prefixWord, tailWord_1945612, baseEnd_1945612] using wordTrace_append hprefix tailTrace_1945612
  have hstable : (prefixWord ++ tailWord_1945612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945612).length < 2 ^ (prefixWord ++ tailWord_1945612).sum := by decide
  have hdescent : baseEnd_1945612 < baseStart_1945612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945620 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1945620 : Nat := 118140960795 + 1945620 * 2 ^ 59
def prefixEnd_1945620 : Nat := 4983230072969 + 3 ^ 40 * 1945620 * 2
def baseEnd_1945620 : Nat := 333012743666927662167421

theorem tailTrace_1945620 : CollatzResearch.WordTrace tailWord_1945620 prefixEnd_1945620 333012743666927662167421 := by
  unfold tailWord_1945620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35481295605679250143257157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47308394140905666857676209 35481295605679250143257157)
  ·
    refine ⟨6652742926064859401860717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35481295605679250143257157 6652742926064859401860717)
    ·
      refine ⟨2494778597274322275697769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6652742926064859401860717 2494778597274322275697769)
      ·
        refine ⟨1871083947955741706773327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2494778597274322275697769 1871083947955741706773327)
        ·
          refine ⟨2806625921933612560159991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871083947955741706773327 2806625921933612560159991)
          ·
            refine ⟨4209938882900418840239987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806625921933612560159991 4209938882900418840239987)
            ·
              refine ⟨6314908324350628260359981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209938882900418840239987 6314908324350628260359981)
              ·
                refine ⟨2368090621631485597634993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314908324350628260359981 2368090621631485597634993)
                ·
                  refine ⟨1776067966223614198226245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368090621631485597634993 1776067966223614198226245)
                  ·
                    refine ⟨333012743666927662167421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776067966223614198226245 333012743666927662167421)
                    ·
                      rfl

theorem cell23_1945620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1945620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945620 prefixEnd_1945620 := by exact prefixLift 1945620
  have htrace : WordTrace (prefixWord ++ tailWord_1945620) baseStart_1945620 baseEnd_1945620 := by
    simpa [prefixWord, tailWord_1945620, baseEnd_1945620] using wordTrace_append hprefix tailTrace_1945620
  have hstable : (prefixWord ++ tailWord_1945620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945620).length < 2 ^ (prefixWord ++ tailWord_1945620).sum := by decide
  have hdescent : baseEnd_1945620 < baseStart_1945620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945756 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1945756 : Nat := 118140960795 + 1945756 * 2 ^ 59
def prefixEnd_1945756 : Nat := 4983230072969 + 3 ^ 40 * 1945756 * 2
def baseEnd_1945756 : Nat := 999108064369794454401637

theorem tailTrace_1945756 : CollatzResearch.WordTrace tailWord_1945756 prefixEnd_1945756 999108064369794454401637 := by
  unfold tailWord_1945756
  simp only [CollatzResearch.WordTrace]
  refine ⟨35483775769432897756732561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47311701025910530342310081 35483775769432897756732561)
  ·
    refine ⟨26612831827074673317549421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35483775769432897756732561 26612831827074673317549421)
    ·
      refine ⟨9979811935153002494081033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26612831827074673317549421 9979811935153002494081033)
      ·
        refine ⟨7484858951364751870560775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9979811935153002494081033 7484858951364751870560775)
        ·
          refine ⟨11227288427047127805841163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484858951364751870560775 11227288427047127805841163)
          ·
            refine ⟨16840932640570691708761745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227288427047127805841163 16840932640570691708761745)
            ·
              refine ⟨12630699480428018781571309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840932640570691708761745 12630699480428018781571309)
              ·
                refine ⟨4736512305160507043089241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12630699480428018781571309 4736512305160507043089241)
                ·
                  refine ⟨3552384228870380282316931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736512305160507043089241 3552384228870380282316931)
                  ·
                    refine ⟨5328576343305570423475397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3552384228870380282316931 5328576343305570423475397)
                    ·
                      refine ⟨999108064369794454401637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5328576343305570423475397 999108064369794454401637)
                      ·
                        rfl

theorem cell23_1945756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1945756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945756 prefixEnd_1945756 := by exact prefixLift 1945756
  have htrace : WordTrace (prefixWord ++ tailWord_1945756) baseStart_1945756 baseEnd_1945756 := by
    simpa [prefixWord, tailWord_1945756, baseEnd_1945756] using wordTrace_append hprefix tailTrace_1945756
  have hstable : (prefixWord ++ tailWord_1945756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945756).length < 2 ^ (prefixWord ++ tailWord_1945756).sum := by decide
  have hdescent : baseEnd_1945756 < baseStart_1945756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945773 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1945773 : Nat := 118140960795 + 1945773 * 2 ^ 59
def prefixEnd_1945773 : Nat := 4983230072969 + 3 ^ 40 * 1945773 * 2
def baseEnd_1945773 : Nat := 999116793540920887889059

theorem tailTrace_1945773 : CollatzResearch.WordTrace tailWord_1945773 prefixEnd_1945773 999116793540920887889059 := by
  unfold tailWord_1945773
  simp only [CollatzResearch.WordTrace]
  refine ⟨70968171579804207416833973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47312114386536138277889315 70968171579804207416833973)
  ·
    refine ⟨6653266085606644445328185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70968171579804207416833973 6653266085606644445328185)
    ·
      refine ⟨4989949564204983333996139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6653266085606644445328185 4989949564204983333996139)
      ·
        refine ⟨7484924346307475000994209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989949564204983333996139 7484924346307475000994209)
        ·
          refine ⟨5613693259730606250745657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7484924346307475000994209 5613693259730606250745657)
          ·
            refine ⟨4210269944797954688059243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613693259730606250745657 4210269944797954688059243)
            ·
              refine ⟨6315404917196932032088865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210269944797954688059243 6315404917196932032088865)
              ·
                refine ⟨4736553687897699024066649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315404917196932032088865 4736553687897699024066649)
                ·
                  refine ⟨3552415265923274268049987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736553687897699024066649 3552415265923274268049987)
                  ·
                    refine ⟨5328622898884911402074981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3552415265923274268049987 5328622898884911402074981)
                    ·
                      refine ⟨999116793540920887889059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5328622898884911402074981 999116793540920887889059)
                      ·
                        rfl

theorem cell23_1945773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1945773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945773 prefixEnd_1945773 := by exact prefixLift 1945773
  have htrace : WordTrace (prefixWord ++ tailWord_1945773) baseStart_1945773 baseEnd_1945773 := by
    simpa [prefixWord, tailWord_1945773, baseEnd_1945773] using wordTrace_append hprefix tailTrace_1945773
  have hstable : (prefixWord ++ tailWord_1945773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945773).length < 2 ^ (prefixWord ++ tailWord_1945773).sum := by decide
  have hdescent : baseEnd_1945773 < baseStart_1945773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945779 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 6]
def baseStart_1945779 : Nat := 118140960795 + 1945779 * 2 ^ 59
def prefixEnd_1945779 : Nat := 4983230072969 + 3 ^ 40 * 1945779 * 2
def baseEnd_1945779 : Nat := 111013319380538651601559

theorem tailTrace_1945779 : CollatzResearch.WordTrace tailWord_1945779 prefixEnd_1945779 111013319380538651601559 := by
  unfold tailWord_1945779
  simp only [CollatzResearch.WordTrace]
  refine ⟨70968390417782470441552391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47312260278521646961034927 70968390417782470441552391)
  ·
    refine ⟨106452585626673705662328587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70968390417782470441552391 106452585626673705662328587)
    ·
      refine ⟨159678878440010558493492881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106452585626673705662328587 159678878440010558493492881)
      ·
        refine ⟨119759158830007918870119661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159678878440010558493492881 119759158830007918870119661)
        ·
          refine ⟨44909684561252969576294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119759158830007918870119661 44909684561252969576294873)
          ·
            refine ⟨33682263420939727182221155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44909684561252969576294873 33682263420939727182221155)
            ·
              refine ⟨50523395131409590773331733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33682263420939727182221155 50523395131409590773331733)
              ·
                refine ⟨2368284146784824567499925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50523395131409590773331733 2368284146784824567499925)
                ·
                  refine ⟨111013319380538651601559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2368284146784824567499925 111013319380538651601559)
                  ·
                    rfl

theorem cell23_1945779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 6].length) (baseStart_1945779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945779 prefixEnd_1945779 := by exact prefixLift 1945779
  have htrace : WordTrace (prefixWord ++ tailWord_1945779) baseStart_1945779 baseEnd_1945779 := by
    simpa [prefixWord, tailWord_1945779, baseEnd_1945779] using wordTrace_append hprefix tailTrace_1945779
  have hstable : (prefixWord ++ tailWord_1945779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945779).length < 2 ^ (prefixWord ++ tailWord_1945779).sum := by decide
  have hdescent : baseEnd_1945779 < baseStart_1945779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945783 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1945783 : Nat := 118140960795 + 1945783 * 2 ^ 59
def prefixEnd_1945783 : Nat := 4983230072969 + 3 ^ 40 * 1945783 * 2
def baseEnd_1945783 : Nat := 333040642782488616254671

theorem tailTrace_1945783 : CollatzResearch.WordTrace tailWord_1945783 prefixEnd_1945783 333040642782488616254671 := by
  unfold tailWord_1945783
  simp only [CollatzResearch.WordTrace]
  refine ⟨70968536309767979124698003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47312357539845319416465335 70968536309767979124698003)
  ·
    refine ⟨106452804464651968687047005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70968536309767979124698003 106452804464651968687047005)
    ·
      refine ⟨39919801674244488257642627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106452804464651968687047005 39919801674244488257642627)
      ·
        refine ⟨59879702511366732386463941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39919801674244488257642627 59879702511366732386463941)
        ·
          refine ⟨11227444220881262322461989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59879702511366732386463941 11227444220881262322461989)
          ·
            refine ⟨2105145791415236685461623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11227444220881262322461989 2105145791415236685461623)
            ·
              refine ⟨3157718687122855028192435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105145791415236685461623 3157718687122855028192435)
              ·
                refine ⟨4736578030684282542288653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157718687122855028192435 4736578030684282542288653)
                ·
                  refine ⟨1776216761506605953358245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4736578030684282542288653 1776216761506605953358245)
                  ·
                    refine ⟨333040642782488616254671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776216761506605953358245 333040642782488616254671)
                    ·
                      rfl

theorem cell23_1945783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1945783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945783 prefixEnd_1945783 := by exact prefixLift 1945783
  have htrace : WordTrace (prefixWord ++ tailWord_1945783) baseStart_1945783 baseEnd_1945783 := by
    simpa [prefixWord, tailWord_1945783, baseEnd_1945783] using wordTrace_append hprefix tailTrace_1945783
  have hstable : (prefixWord ++ tailWord_1945783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945783).length < 2 ^ (prefixWord ++ tailWord_1945783).sum := by decide
  have hdescent : baseEnd_1945783 < baseStart_1945783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945890 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1945890 : Nat := 118140960795 + 1945890 * 2 ^ 59
def prefixEnd_1945890 : Nat := 4983230072969 + 3 ^ 40 * 1945890 * 2
def baseEnd_1945890 : Nat := 333058956925832310042007

theorem tailTrace_1945890 : CollatzResearch.WordTrace tailWord_1945890 prefixEnd_1945890 333058956925832310042007 := by
  unfold tailWord_1945890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743109730095084099710781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47314959280253557599228749 17743109730095084099710781)
  ·
    refine ⟨6653666148785656537391543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17743109730095084099710781 6653666148785656537391543)
    ·
      refine ⟨9980499223178484806087315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653666148785656537391543 9980499223178484806087315)
      ·
        refine ⟨14970748834767727209130973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980499223178484806087315 14970748834767727209130973)
        ·
          refine ⟨5614030813037897703424115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14970748834767727209130973 5614030813037897703424115)
          ·
            refine ⟨8421046219556846555136173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614030813037897703424115 8421046219556846555136173)
            ·
              refine ⟨3157892332333817458176065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8421046219556846555136173 3157892332333817458176065)
              ·
                refine ⟨2368419249250363093632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157892332333817458176065 2368419249250363093632049)
                ·
                  refine ⟨1776314436937772320224037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368419249250363093632049 1776314436937772320224037)
                  ·
                    refine ⟨333058956925832310042007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776314436937772320224037 333058956925832310042007)
                    ·
                      rfl

theorem cell23_1945890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1945890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945890 prefixEnd_1945890 := by exact prefixLift 1945890
  have htrace : WordTrace (prefixWord ++ tailWord_1945890) baseStart_1945890 baseEnd_1945890 := by
    simpa [prefixWord, tailWord_1945890, baseEnd_1945890] using wordTrace_append hprefix tailTrace_1945890
  have hstable : (prefixWord ++ tailWord_1945890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945890).length < 2 ^ (prefixWord ++ tailWord_1945890).sum := by decide
  have hdescent : baseEnd_1945890 < baseStart_1945890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945923 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 3, 3, 2]
def baseStart_1945923 : Nat := 118140960795 + 1945923 * 2 ^ 59
def prefixEnd_1945923 : Nat := 4983230072969 + 3 ^ 40 * 1945923 * 2
def baseEnd_1945923 : Nat := 999193815639095301013369

theorem tailTrace_1945923 : CollatzResearch.WordTrace tailWord_1945923 prefixEnd_1945923 999193815639095301013369 := by
  unfold tailWord_1945923
  simp only [CollatzResearch.WordTrace]
  refine ⟨70973642529260783034794423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47315761686173855356529615 70973642529260783034794423)
  ·
    refine ⟨106460463793891174552191635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70973642529260783034794423 106460463793891174552191635)
    ·
      refine ⟨159690695690836761828287453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106460463793891174552191635 159690695690836761828287453)
      ·
        refine ⟨59884010884063785685607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159690695690836761828287453 59884010884063785685607795)
        ·
          refine ⟨89826016326095678528411693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59884010884063785685607795 89826016326095678528411693)
          ·
            refine ⟨33684756122285879448154385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89826016326095678528411693 33684756122285879448154385)
            ·
              refine ⟨25263567091714409586115789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33684756122285879448154385 25263567091714409586115789)
              ·
                refine ⟨9473837659392903594793421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25263567091714409586115789 9473837659392903594793421)
                ·
                  refine ⟨3552689122272338848047533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9473837659392903594793421 3552689122272338848047533)
                  ·
                    refine ⟨1332258420852127068017825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552689122272338848047533 1332258420852127068017825)
                    ·
                      refine ⟨999193815639095301013369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332258420852127068017825 999193815639095301013369)
                      ·
                        rfl

theorem cell23_1945923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_1945923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945923 prefixEnd_1945923 := by exact prefixLift 1945923
  have htrace : WordTrace (prefixWord ++ tailWord_1945923) baseStart_1945923 baseEnd_1945923 := by
    simpa [prefixWord, tailWord_1945923, baseEnd_1945923] using wordTrace_append hprefix tailTrace_1945923
  have hstable : (prefixWord ++ tailWord_1945923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945923).length < 2 ^ (prefixWord ++ tailWord_1945923).sum := by decide
  have hdescent : baseEnd_1945923 < baseStart_1945923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945948 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1945948 : Nat := 118140960795 + 1945948 * 2 ^ 59
def prefixEnd_1945948 : Nat := 4983230072969 + 3 ^ 40 * 1945948 * 2
def baseEnd_1945948 : Nat := 999206652655457703200755

theorem tailTrace_1945948 : CollatzResearch.WordTrace tailWord_1945948 prefixEnd_1945948 999206652655457703200755 := by
  unfold tailWord_1945948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35487277177085106152227249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47316369569446808202969665 35487277177085106152227249)
  ·
    refine ⟨26615457882813829614170437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35487277177085106152227249 26615457882813829614170437)
    ·
      refine ⟨4990398353027593052656957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26615457882813829614170437 4990398353027593052656957)
      ·
        refine ⟨1871399382385347394746359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4990398353027593052656957 1871399382385347394746359)
        ·
          refine ⟨2807099073578021092119539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871399382385347394746359 2807099073578021092119539)
          ·
            refine ⟨4210648610367031638179309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807099073578021092119539 4210648610367031638179309)
            ·
              refine ⟨1578993228887636864317241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4210648610367031638179309 1578993228887636864317241)
              ·
                refine ⟨1184244921665727648237931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578993228887636864317241 1184244921665727648237931)
                ·
                  refine ⟨1776367382498591472356897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184244921665727648237931 1776367382498591472356897)
                  ·
                    refine ⟨1332275536873943604267673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776367382498591472356897 1332275536873943604267673)
                    ·
                      refine ⟨999206652655457703200755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332275536873943604267673 999206652655457703200755)
                      ·
                        rfl

theorem cell23_1945948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1945948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945948 prefixEnd_1945948 := by exact prefixLift 1945948
  have htrace : WordTrace (prefixWord ++ tailWord_1945948) baseStart_1945948 baseEnd_1945948 := by
    simpa [prefixWord, tailWord_1945948, baseEnd_1945948] using wordTrace_append hprefix tailTrace_1945948
  have hstable : (prefixWord ++ tailWord_1945948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945948).length < 2 ^ (prefixWord ++ tailWord_1945948).sum := by decide
  have hdescent : baseEnd_1945948 < baseStart_1945948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945956 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1945956 : Nat := 118140960795 + 1945956 * 2 ^ 59
def prefixEnd_1945956 : Nat := 4983230072969 + 3 ^ 40 * 1945956 * 2
def baseEnd_1945956 : Nat := 999210760500693671900717

theorem tailTrace_1945956 : CollatzResearch.WordTrace tailWord_1945956 prefixEnd_1945956 999210760500693671900717 := by
  unfold tailWord_1945956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35487423069070614835372861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47316564092094153113830481 35487423069070614835372861)
  ·
    refine ⟨13307783650901480563264823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35487423069070614835372861 13307783650901480563264823)
    ·
      refine ⟨19961675476352220844897235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13307783650901480563264823 19961675476352220844897235)
      ·
        refine ⟨29942513214528331267345853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19961675476352220844897235 29942513214528331267345853)
        ·
          refine ⟨11228442455448124225254695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29942513214528331267345853 11228442455448124225254695)
          ·
            refine ⟨16842663683172186337882043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228442455448124225254695 16842663683172186337882043)
            ·
              refine ⟨25263995524758279506823065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16842663683172186337882043 25263995524758279506823065)
              ·
                refine ⟨18947996643568709630117299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25263995524758279506823065 18947996643568709630117299)
                ·
                  refine ⟨28421994965353064445175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947996643568709630117299 28421994965353064445175949)
                  ·
                    refine ⟨10658248112007399166940981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28421994965353064445175949 10658248112007399166940981)
                    ·
                      refine ⟨999210760500693671900717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10658248112007399166940981 999210760500693671900717)
                      ·
                        rfl

theorem cell23_1945956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1945956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945956 prefixEnd_1945956 := by exact prefixLift 1945956
  have htrace : WordTrace (prefixWord ++ tailWord_1945956) baseStart_1945956 baseEnd_1945956 := by
    simpa [prefixWord, tailWord_1945956, baseEnd_1945956] using wordTrace_append hprefix tailTrace_1945956
  have hstable : (prefixWord ++ tailWord_1945956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945956).length < 2 ^ (prefixWord ++ tailWord_1945956).sum := by decide
  have hdescent : baseEnd_1945956 < baseStart_1945956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945964 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_1945964 : Nat := 118140960795 + 1945964 * 2 ^ 59
def prefixEnd_1945964 : Nat := 4983230072969 + 3 ^ 40 * 1945964 * 2
def baseEnd_1945964 : Nat := 999214868345929640600681

theorem tailTrace_1945964 : CollatzResearch.WordTrace tailWord_1945964 prefixEnd_1945964 999214868345929640600681 := by
  unfold tailWord_1945964
  simp only [CollatzResearch.WordTrace]
  refine ⟨35487568961056123518518473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47316758614741498024691297 35487568961056123518518473)
  ·
    refine ⟨26615676720792092638888855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35487568961056123518518473 26615676720792092638888855)
    ·
      refine ⟨39923515081188138958333283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26615676720792092638888855 39923515081188138958333283)
      ·
        refine ⟨59885272621782208437499925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39923515081188138958333283 59885272621782208437499925)
        ·
          refine ⟨2807122154146041020507809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59885272621782208437499925 2807122154146041020507809)
          ·
            refine ⟨2105341615609530765380857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2807122154146041020507809 2105341615609530765380857)
            ·
              refine ⟨1579006211707148074035643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105341615609530765380857 1579006211707148074035643)
              ·
                refine ⟨2368509317560722111053465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579006211707148074035643 2368509317560722111053465)
                ·
                  refine ⟨1776381988170541583290099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368509317560722111053465 1776381988170541583290099)
                  ·
                    refine ⟨2664572982255812374935149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1776381988170541583290099 2664572982255812374935149)
                    ·
                      refine ⟨999214868345929640600681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2664572982255812374935149 999214868345929640600681)
                      ·
                        rfl

theorem cell23_1945964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_1945964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945964 prefixEnd_1945964 := by exact prefixLift 1945964
  have htrace : WordTrace (prefixWord ++ tailWord_1945964) baseStart_1945964 baseEnd_1945964 := by
    simpa [prefixWord, tailWord_1945964, baseEnd_1945964] using wordTrace_append hprefix tailTrace_1945964
  have hstable : (prefixWord ++ tailWord_1945964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945964).length < 2 ^ (prefixWord ++ tailWord_1945964).sum := by decide
  have hdescent : baseEnd_1945964 < baseStart_1945964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945973 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1945973 : Nat := 118140960795 + 1945973 * 2 ^ 59
def prefixEnd_1945973 : Nat := 4983230072969 + 3 ^ 40 * 1945973 * 2
def baseEnd_1945973 : Nat := 999219489671820105388139

theorem tailTrace_1945973 : CollatzResearch.WordTrace tailWord_1945973 prefixEnd_1945973 999219489671820105388139 := by
  unfold tailWord_1945973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70975466179079641574114573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47316977452719761049409715 70975466179079641574114573)
  ·
    refine ⟨26615799817154865590292965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70975466179079641574114573 26615799817154865590292965)
    ·
      refine ⟨4990462465716537298179931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26615799817154865590292965 4990462465716537298179931)
      ·
        refine ⟨7485693698574805947269897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990462465716537298179931 7485693698574805947269897)
        ·
          refine ⟨5614270273931104460452423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7485693698574805947269897 5614270273931104460452423)
          ·
            refine ⟨8421405410896656690678635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614270273931104460452423 8421405410896656690678635)
            ·
              refine ⟨12632108116344985036017953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8421405410896656690678635 12632108116344985036017953)
              ·
                refine ⟨9474081087258738777013465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12632108116344985036017953 9474081087258738777013465)
                ·
                  refine ⟨7105560815444054082760099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9474081087258738777013465 7105560815444054082760099)
                  ·
                    refine ⟨10658341223166081124140149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105560815444054082760099 10658341223166081124140149)
                    ·
                      refine ⟨999219489671820105388139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10658341223166081124140149 999219489671820105388139)
                      ·
                        rfl

theorem cell23_1945973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1945973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945973 prefixEnd_1945973 := by exact prefixLift 1945973
  have htrace : WordTrace (prefixWord ++ tailWord_1945973) baseStart_1945973 baseEnd_1945973 := by
    simpa [prefixWord, tailWord_1945973, baseEnd_1945973] using wordTrace_append hprefix tailTrace_1945973
  have hstable : (prefixWord ++ tailWord_1945973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945973).length < 2 ^ (prefixWord ++ tailWord_1945973).sum := by decide
  have hdescent : baseEnd_1945973 < baseStart_1945973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945974 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1945974 : Nat := 118140960795 + 1945974 * 2 ^ 59
def prefixEnd_1945974 : Nat := 4983230072969 + 3 ^ 40 * 1945974 * 2
def baseEnd_1945974 : Nat := 999220003152474601475635

theorem tailTrace_1945974 : CollatzResearch.WordTrace tailWord_1945974 prefixEnd_1945974 999220003152474601475635 := by
  unfold tailWord_1945974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435968915754751171556311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47317001768050679163267317 4435968915754751171556311)
  ·
    refine ⟨6653953373632126757334467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435968915754751171556311 6653953373632126757334467)
    ·
      refine ⟨9980930060448190136001701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653953373632126757334467 9980930060448190136001701)
      ·
        refine ⟨1871424386334035650500319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9980930060448190136001701 1871424386334035650500319)
        ·
          refine ⟨2807136579501053475750479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871424386334035650500319 2807136579501053475750479)
          ·
            refine ⟨4210704869251580213625719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807136579501053475750479 4210704869251580213625719)
            ·
              refine ⟨6316057303877370320438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210704869251580213625719 6316057303877370320438579)
              ·
                refine ⟨9474085955816055480657869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316057303877370320438579 9474085955816055480657869)
                ·
                  refine ⟨3552782233431020805246701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9474085955816055480657869 3552782233431020805246701)
                  ·
                    refine ⟨1332293337536632801967513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552782233431020805246701 1332293337536632801967513)
                    ·
                      refine ⟨999220003152474601475635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332293337536632801967513 999220003152474601475635)
                      ·
                        rfl

theorem cell23_1945974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1945974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1945974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1945974 prefixEnd_1945974 := by exact prefixLift 1945974
  have htrace : WordTrace (prefixWord ++ tailWord_1945974) baseStart_1945974 baseEnd_1945974 := by
    simpa [prefixWord, tailWord_1945974, baseEnd_1945974] using wordTrace_append hprefix tailTrace_1945974
  have hstable : (prefixWord ++ tailWord_1945974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945974).length < 2 ^ (prefixWord ++ tailWord_1945974).sum := by decide
  have hdescent : baseEnd_1945974 < baseStart_1945974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946010 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_1946010 : Nat := 118140960795 + 1946010 * 2 ^ 59
def prefixEnd_1946010 : Nat := 4983230072969 + 3 ^ 40 * 1946010 * 2
def baseEnd_1946010 : Nat := 111026498717337384513941

theorem tailTrace_1946010 : CollatzResearch.WordTrace tailWord_1946010 prefixEnd_1946010 111026498717337384513941 := by
  unfold tailWord_1946010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744203919986399223302871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47317877119963731262140989 17744203919986399223302871)
  ·
    refine ⟨26616305879979598834954307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17744203919986399223302871 26616305879979598834954307)
    ·
      refine ⟨39924458819969398252431461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26616305879979598834954307 39924458819969398252431461)
      ·
        refine ⟨7485836028744262172330899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39924458819969398252431461 7485836028744262172330899)
        ·
          refine ⟨11228754043116393258496349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485836028744262172330899 11228754043116393258496349)
          ·
            refine ⟨4210782766168647471936131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11228754043116393258496349 4210782766168647471936131)
            ·
              refine ⟨6316174149252971207904197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210782766168647471936131 6316174149252971207904197)
              ·
                refine ⟨1184282652984932101482037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6316174149252971207904197 1184282652984932101482037)
                ·
                  refine ⟨111026498717337384513941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1184282652984932101482037 111026498717337384513941)
                  ·
                    rfl

theorem cell23_1946010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_1946010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946010 prefixEnd_1946010 := by exact prefixLift 1946010
  have htrace : WordTrace (prefixWord ++ tailWord_1946010) baseStart_1946010 baseEnd_1946010 := by
    simpa [prefixWord, tailWord_1946010, baseEnd_1946010] using wordTrace_append hprefix tailTrace_1946010
  have hstable : (prefixWord ++ tailWord_1946010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946010).length < 2 ^ (prefixWord ++ tailWord_1946010).sum := by decide
  have hdescent : baseEnd_1946010 < baseStart_1946010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946063 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_1946063 : Nat := 118140960795 + 1946063 * 2 ^ 59
def prefixEnd_1946063 : Nat := 4983230072969 + 3 ^ 40 * 1946063 * 2
def baseEnd_1946063 : Nat := 999265702930724753262725

theorem tailTrace_1946063 : CollatzResearch.WordTrace tailWord_1946063 prefixEnd_1946063 999265702930724753262725 := by
  unfold tailWord_1946063
  simp only [CollatzResearch.WordTrace]
  refine ⟨70978748748753586944890843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47319165832502391296593895 70978748748753586944890843)
  ·
    refine ⟨106468123123130380417336265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70978748748753586944890843 106468123123130380417336265)
    ·
      refine ⟨79851092342347785313002199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106468123123130380417336265 79851092342347785313002199)
      ·
        refine ⟨119776638513521677969503299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79851092342347785313002199 119776638513521677969503299)
        ·
          refine ⟨179664957770282516954254949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119776638513521677969503299 179664957770282516954254949)
          ·
            refine ⟨33687179581927971928922803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179664957770282516954254949 33687179581927971928922803)
            ·
              refine ⟨50530769372891957893384205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687179581927971928922803 50530769372891957893384205)
              ·
                refine ⟨18949038514834484210019077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50530769372891957893384205 18949038514834484210019077)
                ·
                  refine ⟨3552944721531465789378577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18949038514834484210019077 3552944721531465789378577)
                  ·
                    refine ⟨2664708541148599342033933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3552944721531465789378577 2664708541148599342033933)
                    ·
                      refine ⟨999265702930724753262725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2664708541148599342033933 999265702930724753262725)
                      ·
                        rfl

theorem cell23_1946063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_1946063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946063 prefixEnd_1946063 := by exact prefixLift 1946063
  have htrace : WordTrace (prefixWord ++ tailWord_1946063) baseStart_1946063 baseEnd_1946063 := by
    simpa [prefixWord, tailWord_1946063, baseEnd_1946063] using wordTrace_append hprefix tailTrace_1946063
  have hstable : (prefixWord ++ tailWord_1946063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946063).length < 2 ^ (prefixWord ++ tailWord_1946063).sum := by decide
  have hdescent : baseEnd_1946063 < baseStart_1946063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946114 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1946114 : Nat := 118140960795 + 1946114 * 2 ^ 59
def prefixEnd_1946114 : Nat := 4983230072969 + 3 ^ 40 * 1946114 * 2
def baseEnd_1946114 : Nat := 999291890444104053724991

theorem tailTrace_1946114 : CollatzResearch.WordTrace tailWord_1946114 prefixEnd_1946114 999291890444104053724991 := by
  unfold tailWord_1946114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745152217892205663749349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47320405914379215103331597 17745152217892205663749349)
  ·
    refine ⟨3327216040854788561953003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17745152217892205663749349 3327216040854788561953003)
    ·
      refine ⟨4990824061282182842929505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327216040854788561953003 4990824061282182842929505)
      ·
        refine ⟨3743118045961637132197129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990824061282182842929505 3743118045961637132197129)
        ·
          refine ⟨2807338534471227849147847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743118045961637132197129 2807338534471227849147847)
          ·
            refine ⟨4211007801706841773721771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807338534471227849147847 4211007801706841773721771)
            ·
              refine ⟨6316511702560262660582657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211007801706841773721771 6316511702560262660582657)
              ·
                refine ⟨4737383776920196995436993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316511702560262660582657 4737383776920196995436993)
                ·
                  refine ⟨3553037832690147746577745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737383776920196995436993 3553037832690147746577745)
                  ·
                    refine ⟨2664778374517610809933309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553037832690147746577745 2664778374517610809933309)
                    ·
                      refine ⟨999291890444104053724991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2664778374517610809933309 999291890444104053724991)
                      ·
                        rfl

theorem cell23_1946114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1946114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946114 prefixEnd_1946114 := by exact prefixLift 1946114
  have htrace : WordTrace (prefixWord ++ tailWord_1946114) baseStart_1946114 baseEnd_1946114 := by
    simpa [prefixWord, tailWord_1946114, baseEnd_1946114] using wordTrace_append hprefix tailTrace_1946114
  have hstable : (prefixWord ++ tailWord_1946114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946114).length < 2 ^ (prefixWord ++ tailWord_1946114).sum := by decide
  have hdescent : baseEnd_1946114 < baseStart_1946114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946143 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 6]
def baseStart_1946143 : Nat := 118140960795 + 1946143 * 2 ^ 59
def prefixEnd_1946143 : Nat := 4983230072969 + 3 ^ 40 * 1946143 * 2
def baseEnd_1946143 : Nat := 333102260461028146754119

theorem tailTrace_1946143 : CollatzResearch.WordTrace tailWord_1946143 prefixEnd_1946143 333102260461028146754119 := by
  unfold tailWord_1946143
  simp only [CollatzResearch.WordTrace]
  refine ⟨70981666588463760607803083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47321111058975840405202055 70981666588463760607803083)
  ·
    refine ⟨106472499882695640911704625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70981666588463760607803083 106472499882695640911704625)
    ·
      refine ⟨79854374912021730683778469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106472499882695640911704625 79854374912021730683778469)
      ·
        refine ⟨14972695296004074503208463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79854374912021730683778469 14972695296004074503208463)
        ·
          refine ⟨22459042944006111754812695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14972695296004074503208463 22459042944006111754812695)
          ·
            refine ⟨33688564416009167632219043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22459042944006111754812695 33688564416009167632219043)
            ·
              refine ⟨50532846624013751448328565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33688564416009167632219043 50532846624013751448328565)
              ·
                refine ⟨4737454371001289198280803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50532846624013751448328565 4737454371001289198280803)
                ·
                  refine ⟨7106181556501933797421205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737454371001289198280803 7106181556501933797421205)
                  ·
                    refine ⟨333102260461028146754119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7106181556501933797421205 333102260461028146754119)
                    ·
                      rfl

theorem cell23_1946143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_1946143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946143 prefixEnd_1946143 := by exact prefixLift 1946143
  have htrace : WordTrace (prefixWord ++ tailWord_1946143) baseStart_1946143 baseEnd_1946143 := by
    simpa [prefixWord, tailWord_1946143, baseEnd_1946143] using wordTrace_append hprefix tailTrace_1946143
  have hstable : (prefixWord ++ tailWord_1946143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946143).length < 2 ^ (prefixWord ++ tailWord_1946143).sum := by decide
  have hdescent : baseEnd_1946143 < baseStart_1946143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946147 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 1, 5]
def baseStart_1946147 : Nat := 118140960795 + 1946147 * 2 ^ 59
def prefixEnd_1946147 : Nat := 4983230072969 + 3 ^ 40 * 1946147 * 2
def baseEnd_1946147 : Nat := 333102945101900808204113

theorem tailTrace_1946147 : CollatzResearch.WordTrace tailWord_1946147 prefixEnd_1946147 333102945101900808204113 := by
  unfold tailWord_1946147
  simp only [CollatzResearch.WordTrace]
  refine ⟨70981812480449269290948695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47321208320299512860632463 70981812480449269290948695)
  ·
    refine ⟨106472718720673903936423043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70981812480449269290948695 106472718720673903936423043)
    ·
      refine ⟨159709078081010855904634565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106472718720673903936423043 159709078081010855904634565)
      ·
        refine ⟨29945452140189535482118981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159709078081010855904634565 29945452140189535482118981)
        ·
          refine ⟨5614772276285537902897309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29945452140189535482118981 5614772276285537902897309)
          ·
            refine ⟨2105539603607076713586491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5614772276285537902897309 2105539603607076713586491)
            ·
              refine ⟨3158309405410615070379737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105539603607076713586491 3158309405410615070379737)
              ·
                refine ⟨2368732054057961302784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158309405410615070379737 2368732054057961302784803)
                ·
                  refine ⟨3553098081086941954177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368732054057961302784803 3553098081086941954177205)
                  ·
                    refine ⟨333102945101900808204113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3553098081086941954177205 333102945101900808204113)
                    ·
                      rfl

theorem cell23_1946147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 5].length) (baseStart_1946147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946147 prefixEnd_1946147 := by exact prefixLift 1946147
  have htrace : WordTrace (prefixWord ++ tailWord_1946147) baseStart_1946147 baseEnd_1946147 := by
    simpa [prefixWord, tailWord_1946147, baseEnd_1946147] using wordTrace_append hprefix tailTrace_1946147
  have hstable : (prefixWord ++ tailWord_1946147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946147).length < 2 ^ (prefixWord ++ tailWord_1946147).sum := by decide
  have hdescent : baseEnd_1946147 < baseStart_1946147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946154 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1946154 : Nat := 118140960795 + 1946154 * 2 ^ 59
def prefixEnd_1946154 : Nat := 4983230072969 + 3 ^ 40 * 1946154 * 2
def baseEnd_1946154 : Nat := 999312429670283897224807

theorem tailTrace_1946154 : CollatzResearch.WordTrace tailWord_1946154 prefixEnd_1946154 999312429670283897224807 := by
  unfold tailWord_1946154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745516947855977371613379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47321378527615939657635677 17745516947855977371613379)
  ·
    refine ⟨26618275421783966057420069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17745516947855977371613379 26618275421783966057420069)
    ·
      refine ⟨4990926641584493635766263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26618275421783966057420069 4990926641584493635766263)
      ·
        refine ⟨7486389962376740453649395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990926641584493635766263 7486389962376740453649395)
        ·
          refine ⟨11229584943565110680474093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486389962376740453649395 11229584943565110680474093)
          ·
            refine ⟨4211094353836916505177785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11229584943565110680474093 4211094353836916505177785)
            ·
              refine ⟨3158320765377687378883339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211094353836916505177785 3158320765377687378883339)
              ·
                refine ⟨4737481148066531068325009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158320765377687378883339 4737481148066531068325009)
                ·
                  refine ⟨3553110861049898301243757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737481148066531068325009 3553110861049898301243757)
                  ·
                    refine ⟨1332416572893711862966409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553110861049898301243757 1332416572893711862966409)
                    ·
                      refine ⟨999312429670283897224807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332416572893711862966409 999312429670283897224807)
                      ·
                        rfl

theorem cell23_1946154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1946154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946154 prefixEnd_1946154 := by exact prefixLift 1946154
  have htrace : WordTrace (prefixWord ++ tailWord_1946154) baseStart_1946154 baseEnd_1946154 := by
    simpa [prefixWord, tailWord_1946154, baseEnd_1946154] using wordTrace_append hprefix tailTrace_1946154
  have hstable : (prefixWord ++ tailWord_1946154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946154).length < 2 ^ (prefixWord ++ tailWord_1946154).sum := by decide
  have hdescent : baseEnd_1946154 < baseStart_1946154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946167 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_1946167 : Nat := 118140960795 + 1946167 * 2 ^ 59
def prefixEnd_1946167 : Nat := 4983230072969 + 3 ^ 40 * 1946167 * 2
def baseEnd_1946167 : Nat := 999319104918792346362247

theorem tailTrace_1946167 : CollatzResearch.WordTrace tailWord_1946167 prefixEnd_1946167 999319104918792346362247 := by
  unfold tailWord_1946167
  simp only [CollatzResearch.WordTrace]
  refine ⟨70982541940376812706676755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47321694626917875137784503 70982541940376812706676755)
  ·
    refine ⟨106473812910565219060015133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70982541940376812706676755 106473812910565219060015133)
    ·
      refine ⟨39927679841461957147505675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106473812910565219060015133 39927679841461957147505675)
      ·
        refine ⟨59891519762192935721258513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39927679841461957147505675 59891519762192935721258513)
        ·
          refine ⟨44918639821644701790943885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59891519762192935721258513 44918639821644701790943885)
          ·
            refine ⟨16844489933116763171603957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44918639821644701790943885 16844489933116763171603957)
            ·
              refine ⟨1579170931229696547337871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16844489933116763171603957 1579170931229696547337871)
              ·
                refine ⟨2368756396844544821006807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579170931229696547337871 2368756396844544821006807)
                ·
                  refine ⟨3553134595266817231510211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368756396844544821006807 3553134595266817231510211)
                  ·
                    refine ⟨5329701892900225847265317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3553134595266817231510211 5329701892900225847265317)
                    ·
                      refine ⟨999319104918792346362247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5329701892900225847265317 999319104918792346362247)
                      ·
                        rfl

theorem cell23_1946167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_1946167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946167 prefixEnd_1946167 := by exact prefixLift 1946167
  have htrace : WordTrace (prefixWord ++ tailWord_1946167) baseStart_1946167 baseEnd_1946167 := by
    simpa [prefixWord, tailWord_1946167, baseEnd_1946167] using wordTrace_append hprefix tailTrace_1946167
  have hstable : (prefixWord ++ tailWord_1946167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946167).length < 2 ^ (prefixWord ++ tailWord_1946167).sum := by decide
  have hdescent : baseEnd_1946167 < baseStart_1946167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946170 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1946170 : Nat := 118140960795 + 1946170 * 2 ^ 59
def prefixEnd_1946170 : Nat := 4983230072969 + 3 ^ 40 * 1946170 * 2
def baseEnd_1946170 : Nat := 999320645360755834624733

theorem tailTrace_1946170 : CollatzResearch.WordTrace tailWord_1946170 prefixEnd_1946170 999320645360755834624733 := by
  unfold tailWord_1946170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745662839841486054758991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47321767572910629479357309 17745662839841486054758991)
  ·
    refine ⟨26618494259762229082138487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17745662839841486054758991 26618494259762229082138487)
    ·
      refine ⟨39927741389643343623207731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26618494259762229082138487 39927741389643343623207731)
      ·
        refine ⟨59891612084465015434811597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39927741389643343623207731 59891612084465015434811597)
        ·
          refine ⟨22459354531674380788054349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59891612084465015434811597 22459354531674380788054349)
          ·
            refine ⟨8422257949377892795520381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22459354531674380788054349 8422257949377892795520381)
            ·
              refine ⟨3158346731016709798320143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8422257949377892795520381 3158346731016709798320143)
              ·
                refine ⟨4737520096525064697480215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158346731016709798320143 4737520096525064697480215)
                ·
                  refine ⟨7106280144787597046220323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737520096525064697480215 7106280144787597046220323)
                  ·
                    refine ⟨10659420217181395569330485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7106280144787597046220323 10659420217181395569330485)
                    ·
                      refine ⟨999320645360755834624733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10659420217181395569330485 999320645360755834624733)
                      ·
                        rfl

theorem cell23_1946170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1946170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946170 prefixEnd_1946170 := by exact prefixLift 1946170
  have htrace : WordTrace (prefixWord ++ tailWord_1946170) baseStart_1946170 baseEnd_1946170 := by
    simpa [prefixWord, tailWord_1946170, baseEnd_1946170] using wordTrace_append hprefix tailTrace_1946170
  have hstable : (prefixWord ++ tailWord_1946170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946170).length < 2 ^ (prefixWord ++ tailWord_1946170).sum := by decide
  have hdescent : baseEnd_1946170 < baseStart_1946170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946173 : List Nat := [1, 4, 1, 3, 2, 12]
def baseStart_1946173 : Nat := 118140960795 + 1946173 * 2 ^ 59
def prefixEnd_1946173 : Nat := 4983230072969 + 3 ^ 40 * 1946173 * 2
def baseEnd_1946173 : Nat := 4112436978612013674433

theorem tailTrace_1946173 : CollatzResearch.WordTrace tailWord_1946173 prefixEnd_1946173 4112436978612013674433 := by
  unfold tailWord_1946173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70982760778355075731395173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47321840518903383820930115 70982760778355075731395173)
  ·
    refine ⟨13309267645941576699636595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70982760778355075731395173 13309267645941576699636595)
    ·
      refine ⟨19963901468912365049454893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13309267645941576699636595 19963901468912365049454893)
      ·
        refine ⟨7486463050842136893545585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19963901468912365049454893 7486463050842136893545585)
        ·
          refine ⟨5614847288131602670159189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7486463050842136893545585 5614847288131602670159189)
          ·
            refine ⟨4112436978612013674433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5614847288131602670159189 4112436978612013674433)
            ·
              rfl

theorem cell23_1946173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 12].length) (baseStart_1946173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946173 prefixEnd_1946173 := by exact prefixLift 1946173
  have htrace : WordTrace (prefixWord ++ tailWord_1946173) baseStart_1946173 baseEnd_1946173 := by
    simpa [prefixWord, tailWord_1946173, baseEnd_1946173] using wordTrace_append hprefix tailTrace_1946173
  have hstable : (prefixWord ++ tailWord_1946173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946173).length < 2 ^ (prefixWord ++ tailWord_1946173).sum := by decide
  have hdescent : baseEnd_1946173 < baseStart_1946173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946177 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1946177 : Nat := 118140960795 + 1946177 * 2 ^ 59
def prefixEnd_1946177 : Nat := 4983230072969 + 3 ^ 40 * 1946177 * 2
def baseEnd_1946177 : Nat := 333108079908445769079067

theorem tailTrace_1946177 : CollatzResearch.WordTrace tailWord_1946177 prefixEnd_1946177 333108079908445769079067 := by
  unfold tailWord_1946177
  simp only [CollatzResearch.WordTrace]
  refine ⟨70982906670340584414540785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47321937780227056276360523 70982906670340584414540785)
  ·
    refine ⟨53237180002755438310905589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70982906670340584414540785 53237180002755438310905589)
    ·
      refine ⟨4990985625258322341647399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53237180002755438310905589 4990985625258322341647399)
      ·
        refine ⟨7486478437887483512471099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990985625258322341647399 7486478437887483512471099)
        ·
          refine ⟨11229717656831225268706649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486478437887483512471099 11229717656831225268706649)
          ·
            refine ⟨8422288242623418951529987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11229717656831225268706649 8422288242623418951529987)
            ·
              refine ⟨12633432363935128427294981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422288242623418951529987 12633432363935128427294981)
              ·
                refine ⟨2368768568237836580117809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12633432363935128427294981 2368768568237836580117809)
                ·
                  refine ⟨1776576426178377435088357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368768568237836580117809 1776576426178377435088357)
                  ·
                    refine ⟨333108079908445769079067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776576426178377435088357 333108079908445769079067)
                    ·
                      rfl

theorem cell23_1946177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1946177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946177 prefixEnd_1946177 := by exact prefixLift 1946177
  have htrace : WordTrace (prefixWord ++ tailWord_1946177) baseStart_1946177 baseEnd_1946177 := by
    simpa [prefixWord, tailWord_1946177, baseEnd_1946177] using wordTrace_append hprefix tailTrace_1946177
  have hstable : (prefixWord ++ tailWord_1946177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946177).length < 2 ^ (prefixWord ++ tailWord_1946177).sum := by decide
  have hdescent : baseEnd_1946177 < baseStart_1946177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946200 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1946200 : Nat := 118140960795 + 1946200 * 2 ^ 59
def prefixEnd_1946200 : Nat := 4983230072969 + 3 ^ 40 * 1946200 * 2
def baseEnd_1946200 : Nat := 999336049780390717249595

theorem tailTrace_1946200 : CollatzResearch.WordTrace tailWord_1946200 prefixEnd_1946200 999336049780390717249595 := by
  unfold tailWord_1946200
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491872774628629671314027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47322497032838172895085369 35491872774628629671314027)
  ·
    refine ⟨53237809161942944506971041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35491872774628629671314027 53237809161942944506971041)
    ·
      refine ⟨39928356871457208380228281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53237809161942944506971041 39928356871457208380228281)
      ·
        refine ⟨29946267653592906285171211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39928356871457208380228281 29946267653592906285171211)
        ·
          refine ⟨44919401480389359427756817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29946267653592906285171211 44919401480389359427756817)
          ·
            refine ⟨33689551110292019570817613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44919401480389359427756817 33689551110292019570817613)
            ·
              refine ⟨12633581666359507339056605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33689551110292019570817613 12633581666359507339056605)
              ·
                refine ⟨4737593124884815252146227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633581666359507339056605 4737593124884815252146227)
                ·
                  refine ⟨7106389687327222878219341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737593124884815252146227 7106389687327222878219341)
                  ·
                    refine ⟨2664896132747708579332253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7106389687327222878219341 2664896132747708579332253)
                    ·
                      refine ⟨999336049780390717249595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2664896132747708579332253 999336049780390717249595)
                      ·
                        rfl

theorem cell23_1946200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1946200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946200 prefixEnd_1946200 := by exact prefixLift 1946200
  have htrace : WordTrace (prefixWord ++ tailWord_1946200) baseStart_1946200 baseEnd_1946200 := by
    simpa [prefixWord, tailWord_1946200, baseEnd_1946200] using wordTrace_append hprefix tailTrace_1946200
  have hstable : (prefixWord ++ tailWord_1946200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946200).length < 2 ^ (prefixWord ++ tailWord_1946200).sum := by decide
  have hdescent : baseEnd_1946200 < baseStart_1946200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946221 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_1946221 : Nat := 118140960795 + 1946221 * 2 ^ 59
def prefixEnd_1946221 : Nat := 4983230072969 + 3 ^ 40 * 1946221 * 2
def baseEnd_1946221 : Nat := 999346832874135135086999

theorem tailTrace_1946221 : CollatzResearch.WordTrace tailWord_1946221 prefixEnd_1946221 999346832874135135086999 := by
  unfold tailWord_1946221
  simp only [CollatzResearch.WordTrace]
  refine ⟨70984511482181179929142517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47323007654787453286095011 70984511482181179929142517)
  ·
    refine ⟨6654797951454485618357111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70984511482181179929142517 6654797951454485618357111)
    ·
      refine ⟨9982196927181728427535667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654797951454485618357111 9982196927181728427535667)
      ·
        refine ⟨14973295390772592641303501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9982196927181728427535667 14973295390772592641303501)
        ·
          refine ⟨5614985771539722240488813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14973295390772592641303501 5614985771539722240488813)
          ·
            refine ⟨2105619664327395840183305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5614985771539722240488813 2105619664327395840183305)
            ·
              refine ⟨1579214748245546880137479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105619664327395840183305 1579214748245546880137479)
              ·
                refine ⟨2368822122368320320206219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579214748245546880137479 2368822122368320320206219)
                ·
                  refine ⟨3553233183552480480309329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368822122368320320206219 3553233183552480480309329)
                  ·
                    refine ⟨2664924887664360360231997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3553233183552480480309329 2664924887664360360231997)
                    ·
                      refine ⟨999346832874135135086999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2664924887664360360231997 999346832874135135086999)
                      ·
                        rfl

theorem cell23_1946221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_1946221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946221 prefixEnd_1946221 := by exact prefixLift 1946221
  have htrace : WordTrace (prefixWord ++ tailWord_1946221) baseStart_1946221 baseEnd_1946221 := by
    simpa [prefixWord, tailWord_1946221, baseEnd_1946221] using wordTrace_append hprefix tailTrace_1946221
  have hstable : (prefixWord ++ tailWord_1946221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946221).length < 2 ^ (prefixWord ++ tailWord_1946221).sum := by decide
  have hdescent : baseEnd_1946221 < baseStart_1946221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946308 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1946308 : Nat := 118140960795 + 1946308 * 2 ^ 59
def prefixEnd_1946308 : Nat := 4983230072969 + 3 ^ 40 * 1946308 * 2
def baseEnd_1946308 : Nat := 999391505691076294699099

theorem tailTrace_1946308 : CollatzResearch.WordTrace tailWord_1946308 prefixEnd_1946308 999391505691076294699099 := by
  unfold tailWord_1946308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493842316432996893779789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47325123088577329191706385 35493842316432996893779789)
  ·
    refine ⟨13310190868662373835167421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35493842316432996893779789 13310190868662373835167421)
    ·
      refine ⟨4991321575748390188187783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13310190868662373835167421 4991321575748390188187783)
      ·
        refine ⟨7486982363622585282281675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991321575748390188187783 7486982363622585282281675)
        ·
          refine ⟨11230473545433877923422513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486982363622585282281675 11230473545433877923422513)
          ·
            refine ⟨8422855159075408442566885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11230473545433877923422513 8422855159075408442566885)
            ·
              refine ⟨1579285342326639082981291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8422855159075408442566885 1579285342326639082981291)
              ·
                refine ⟨2368928013489958624471937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579285342326639082981291 2368928013489958624471937)
                ·
                  refine ⟨1776696010117468968353953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368928013489958624471937 1776696010117468968353953)
                  ·
                    refine ⟨1332522007588101726265465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776696010117468968353953 1332522007588101726265465)
                    ·
                      refine ⟨999391505691076294699099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332522007588101726265465 999391505691076294699099)
                      ·
                        rfl

theorem cell23_1946308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1946308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946308 prefixEnd_1946308 := by exact prefixLift 1946308
  have htrace : WordTrace (prefixWord ++ tailWord_1946308) baseStart_1946308 baseEnd_1946308 := by
    simpa [prefixWord, tailWord_1946308, baseEnd_1946308] using wordTrace_append hprefix tailTrace_1946308
  have hstable : (prefixWord ++ tailWord_1946308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946308).length < 2 ^ (prefixWord ++ tailWord_1946308).sum := by decide
  have hdescent : baseEnd_1946308 < baseStart_1946308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946327 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1946327 : Nat := 118140960795 + 1946327 * 2 ^ 59
def prefixEnd_1946327 : Nat := 4983230072969 + 3 ^ 40 * 1946327 * 2
def baseEnd_1946327 : Nat := 333133753941170573453837

theorem tailTrace_1946327 : CollatzResearch.WordTrace tailWord_1946327 prefixEnd_1946327 333133753941170573453837 := by
  unfold tailWord_1946327
  simp only [CollatzResearch.WordTrace]
  refine ⟨70988377619797160032501235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47325585079864773355000823 70988377619797160032501235)
  ·
    refine ⟨106482566429695740048751853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70988377619797160032501235 106482566429695740048751853)
    ·
      refine ⟨39930962411135902518281945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106482566429695740048751853 39930962411135902518281945)
      ·
        refine ⟨29948221808351926888711459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39930962411135902518281945 29948221808351926888711459)
        ·
          refine ⟨44922332712527890333067189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29948221808351926888711459 44922332712527890333067189)
          ·
            refine ⟨4211468691799489718725049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44922332712527890333067189 4211468691799489718725049)
            ·
              refine ⟨3158601518849617289043787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211468691799489718725049 3158601518849617289043787)
              ·
                refine ⟨4737902278274425933565681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158601518849617289043787 4737902278274425933565681)
                ·
                  refine ⟨3553426708705819450174261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737902278274425933565681 3553426708705819450174261)
                  ·
                    refine ⟨333133753941170573453837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3553426708705819450174261 333133753941170573453837)
                    ·
                      rfl

theorem cell23_1946327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1946327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946327 prefixEnd_1946327 := by exact prefixLift 1946327
  have htrace : WordTrace (prefixWord ++ tailWord_1946327) baseStart_1946327 baseEnd_1946327 := by
    simpa [prefixWord, tailWord_1946327, baseEnd_1946327] using wordTrace_append hprefix tailTrace_1946327
  have hstable : (prefixWord ++ tailWord_1946327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946327).length < 2 ^ (prefixWord ++ tailWord_1946327).sum := by decide
  have hdescent : baseEnd_1946327 < baseStart_1946327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946347 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 4, 2]
def baseStart_1946347 : Nat := 118140960795 + 1946347 * 2 ^ 59
def prefixEnd_1946347 : Nat := 4983230072969 + 3 ^ 40 * 1946347 * 2
def baseEnd_1946347 : Nat := 999411531436601642111419

theorem tailTrace_1946347 : CollatzResearch.WordTrace tailWord_1946347 prefixEnd_1946347 999411531436601642111419 := by
  unfold tailWord_1946347
  simp only [CollatzResearch.WordTrace]
  refine ⟨70989107079724703448229295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47326071386483135632152863 70989107079724703448229295)
  ·
    refine ⟨106483660619587055172343943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70989107079724703448229295 106483660619587055172343943)
    ·
      refine ⟨159725490929380582758515915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106483660619587055172343943 159725490929380582758515915)
      ·
        refine ⟨239588236394070874137773873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159725490929380582758515915 239588236394070874137773873)
        ·
          refine ⟨179691177295553155603330405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239588236394070874137773873 179691177295553155603330405)
          ·
            refine ⟨33692095742916216675624451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179691177295553155603330405 33692095742916216675624451)
            ·
              refine ⟨50538143614374325013436677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33692095742916216675624451 50538143614374325013436677)
              ·
                refine ⟨9475901927695185940019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50538143614374325013436677 9475901927695185940019377)
                ·
                  refine ⟨7106926445771389455014533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475901927695185940019377 7106926445771389455014533)
                  ·
                    refine ⟨1332548708582135522815225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106926445771389455014533 1332548708582135522815225)
                    ·
                      refine ⟨999411531436601642111419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332548708582135522815225 999411531436601642111419)
                      ·
                        rfl

theorem cell23_1946347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4, 2].length) (baseStart_1946347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946347 prefixEnd_1946347 := by exact prefixLift 1946347
  have htrace : WordTrace (prefixWord ++ tailWord_1946347) baseStart_1946347 baseEnd_1946347 := by
    simpa [prefixWord, tailWord_1946347, baseEnd_1946347] using wordTrace_append hprefix tailTrace_1946347
  have hstable : (prefixWord ++ tailWord_1946347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946347).length < 2 ^ (prefixWord ++ tailWord_1946347).sum := by decide
  have hdescent : baseEnd_1946347 < baseStart_1946347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946364 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_1946364 : Nat := 118140960795 + 1946364 * 2 ^ 59
def prefixEnd_1946364 : Nat := 4983230072969 + 3 ^ 40 * 1946364 * 2
def baseEnd_1946364 : Nat := 999420260607728075598841

theorem tailTrace_1946364 : CollatzResearch.WordTrace tailWord_1946364 prefixEnd_1946364 999420260607728075598841 := by
  unfold tailWord_1946364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494863560331557675799073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47326484747108743567732097 35494863560331557675799073)
  ·
    refine ⟨26621147670248668256849305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35494863560331557675799073 26621147670248668256849305)
    ·
      refine ⟨19965860752686501192636979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26621147670248668256849305 19965860752686501192636979)
      ·
        refine ⟨29948791129029751788955469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965860752686501192636979 29948791129029751788955469)
        ·
          refine ⟨11230796673386156920858301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29948791129029751788955469 11230796673386156920858301)
          ·
            refine ⟨4211548752519808845321863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11230796673386156920858301 4211548752519808845321863)
            ·
              refine ⟨6317323128779713267982795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211548752519808845321863 6317323128779713267982795)
              ·
                refine ⟨9475984693169569901974193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317323128779713267982795 9475984693169569901974193)
                ·
                  refine ⟨7106988519877177426480645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475984693169569901974193 7106988519877177426480645)
                  ·
                    refine ⟨1332560347476970767465121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106988519877177426480645 1332560347476970767465121)
                    ·
                      refine ⟨999420260607728075598841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332560347476970767465121 999420260607728075598841)
                      ·
                        rfl

theorem cell23_1946364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_1946364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946364 prefixEnd_1946364 := by exact prefixLift 1946364
  have htrace : WordTrace (prefixWord ++ tailWord_1946364) baseStart_1946364 baseEnd_1946364 := by
    simpa [prefixWord, tailWord_1946364, baseEnd_1946364] using wordTrace_append hprefix tailTrace_1946364
  have hstable : (prefixWord ++ tailWord_1946364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946364).length < 2 ^ (prefixWord ++ tailWord_1946364).sum := by decide
  have hdescent : baseEnd_1946364 < baseStart_1946364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946457 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1946457 : Nat := 118140960795 + 1946457 * 2 ^ 59
def prefixEnd_1946457 : Nat := 4983230072969 + 3 ^ 40 * 1946457 * 2
def baseEnd_1946457 : Nat := 999468014308596211735913

theorem tailTrace_1946457 : CollatzResearch.WordTrace tailWord_1946457 prefixEnd_1946457 999468014308596211735913 := by
  unfold tailWord_1946457
  simp only [CollatzResearch.WordTrace]
  refine ⟨70993119109326192234733625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47328746072884128156489083 70993119109326192234733625)
  ·
    refine ⟨53244839331994644176050219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70993119109326192234733625 53244839331994644176050219)
    ·
      refine ⟨79867258997991966264075329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53244839331994644176050219 79867258997991966264075329)
      ·
        refine ⟨59900444248493974698056497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79867258997991966264075329 59900444248493974698056497)
        ·
          refine ⟨44925333186370481023542373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59900444248493974698056497 44925333186370481023542373)
          ·
            refine ⟨8423499972444465191914195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44925333186370481023542373 8423499972444465191914195)
            ·
              refine ⟨12635249958666697787871293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423499972444465191914195 12635249958666697787871293)
              ·
                refine ⟨4738218734500011670451735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12635249958666697787871293 4738218734500011670451735)
                ·
                  refine ⟨7107328101750017505677603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738218734500011670451735 7107328101750017505677603)
                  ·
                    refine ⟨10660992152625026258516405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107328101750017505677603 10660992152625026258516405)
                    ·
                      refine ⟨999468014308596211735913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10660992152625026258516405 999468014308596211735913)
                      ·
                        rfl

theorem cell23_1946457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1946457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946457 prefixEnd_1946457 := by exact prefixLift 1946457
  have htrace : WordTrace (prefixWord ++ tailWord_1946457) baseStart_1946457 baseEnd_1946457 := by
    simpa [prefixWord, tailWord_1946457, baseEnd_1946457] using wordTrace_append hprefix tailTrace_1946457
  have hstable : (prefixWord ++ tailWord_1946457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946457).length < 2 ^ (prefixWord ++ tailWord_1946457).sum := by decide
  have hdescent : baseEnd_1946457 < baseStart_1946457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946464 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_1946464 : Nat := 118140960795 + 1946464 * 2 ^ 59
def prefixEnd_1946464 : Nat := 4983230072969 + 3 ^ 40 * 1946464 * 2
def baseEnd_1946464 : Nat := 333157202891059228116127

theorem tailTrace_1946464 : CollatzResearch.WordTrace tailWord_1946464 prefixEnd_1946464 333157202891059228116127 := by
  unfold tailWord_1946464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35496687210150416215119223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47328916280200554953492297 35496687210150416215119223)
  ·
    refine ⟨53245030815225624322678835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35496687210150416215119223 53245030815225624322678835)
    ·
      refine ⟨79867546222838436484018253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53245030815225624322678835 79867546222838436484018253)
      ·
        refine ⟨29950329833564413681506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79867546222838436484018253 29950329833564413681506845)
        ·
          refine ⟨11231373687586655130565067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29950329833564413681506845 11231373687586655130565067)
          ·
            refine ⟨16847060531379982695847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231373687586655130565067 16847060531379982695847601)
            ·
              refine ⟨12635295398534987021885701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16847060531379982695847601 12635295398534987021885701)
              ·
                refine ⟨2369117887225310066603569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12635295398534987021885701 2369117887225310066603569)
                ·
                  refine ⟨1776838415418982549952677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369117887225310066603569 1776838415418982549952677)
                  ·
                    refine ⟨333157202891059228116127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776838415418982549952677 333157202891059228116127)
                    ·
                      rfl

theorem cell23_1946464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_1946464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946464 prefixEnd_1946464 := by exact prefixLift 1946464
  have htrace : WordTrace (prefixWord ++ tailWord_1946464) baseStart_1946464 baseEnd_1946464 := by
    simpa [prefixWord, tailWord_1946464, baseEnd_1946464] using wordTrace_append hprefix tailTrace_1946464
  have hstable : (prefixWord ++ tailWord_1946464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946464).length < 2 ^ (prefixWord ++ tailWord_1946464).sum := by decide
  have hdescent : baseEnd_1946464 < baseStart_1946464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946467 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1946467 : Nat := 118140960795 + 1946467 * 2 ^ 59
def prefixEnd_1946467 : Nat := 4983230072969 + 3 ^ 40 * 1946467 * 2
def baseEnd_1946467 : Nat := 999473149115141172610867

theorem tailTrace_1946467 : CollatzResearch.WordTrace tailWord_1946467 prefixEnd_1946467 999473149115141172610867 := by
  unfold tailWord_1946467
  simp only [CollatzResearch.WordTrace]
  refine ⟨70993483839289963942597655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47328989226193309295065103 70993483839289963942597655)
  ·
    refine ⟨106490225758934945913896483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70993483839289963942597655 106490225758934945913896483)
    ·
      refine ⟨159735338638402418870844725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106490225758934945913896483 159735338638402418870844725)
      ·
        refine ⟨14975187997350226769141693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159735338638402418870844725 14975187997350226769141693)
        ·
          refine ⟨5615695499006335038428135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14975187997350226769141693 5615695499006335038428135)
          ·
            refine ⟨8423543248509502557642203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615695499006335038428135 8423543248509502557642203)
            ·
              refine ⟨12635314872764253836463305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423543248509502557642203 12635314872764253836463305)
              ·
                refine ⟨9476486154573190377347479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12635314872764253836463305 9476486154573190377347479)
                ·
                  refine ⟨14214729231859785566021219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476486154573190377347479 14214729231859785566021219)
                  ·
                    refine ⟨21322093847789678349031829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14214729231859785566021219 21322093847789678349031829)
                    ·
                      refine ⟨999473149115141172610867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21322093847789678349031829 999473149115141172610867)
                      ·
                        rfl

theorem cell23_1946467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1946467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946467 prefixEnd_1946467 := by exact prefixLift 1946467
  have htrace : WordTrace (prefixWord ++ tailWord_1946467) baseStart_1946467 baseEnd_1946467 := by
    simpa [prefixWord, tailWord_1946467, baseEnd_1946467] using wordTrace_append hprefix tailTrace_1946467
  have hstable : (prefixWord ++ tailWord_1946467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946467).length < 2 ^ (prefixWord ++ tailWord_1946467).sum := by decide
  have hdescent : baseEnd_1946467 < baseStart_1946467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946481 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_1946481 : Nat := 118140960795 + 1946481 * 2 ^ 59
def prefixEnd_1946481 : Nat := 4983230072969 + 3 ^ 40 * 1946481 * 2
def baseEnd_1946481 : Nat := 333160112614768039278601

theorem tailTrace_1946481 : CollatzResearch.WordTrace tailWord_1946481 prefixEnd_1946481 333160112614768039278601 := by
  unfold tailWord_1946481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70993994461239244333607297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47329329640826162889071531 70993994461239244333607297)
  ·
    refine ⟨53245495845929433250205473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70993994461239244333607297 53245495845929433250205473)
    ·
      refine ⟨39934121884447074937654105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53245495845929433250205473 39934121884447074937654105)
      ·
        refine ⟨29950591413335306203240579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39934121884447074937654105 29950591413335306203240579)
        ·
          refine ⟨44925887120002959304860869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950591413335306203240579 44925887120002959304860869)
          ·
            refine ⟨8423603835000554869661413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44925887120002959304860869 8423603835000554869661413)
            ·
              refine ⟨1579425719062604038061515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8423603835000554869661413 1579425719062604038061515)
              ·
                refine ⟨2369138578593906057092273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579425719062604038061515 2369138578593906057092273)
                ·
                  refine ⟨1776853933945429542819205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369138578593906057092273 1776853933945429542819205)
                  ·
                    refine ⟨333160112614768039278601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776853933945429542819205 333160112614768039278601)
                    ·
                      rfl

theorem cell23_1946481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_1946481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946481 prefixEnd_1946481 := by exact prefixLift 1946481
  have htrace : WordTrace (prefixWord ++ tailWord_1946481) baseStart_1946481 baseEnd_1946481 := by
    simpa [prefixWord, tailWord_1946481, baseEnd_1946481] using wordTrace_append hprefix tailTrace_1946481
  have hstable : (prefixWord ++ tailWord_1946481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946481).length < 2 ^ (prefixWord ++ tailWord_1946481).sum := by decide
  have hdescent : baseEnd_1946481 < baseStart_1946481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1946487 : Nat := 118140960795 + 1946487 * 2 ^ 59
def prefixEnd_1946487 : Nat := 4983230072969 + 3 ^ 40 * 1946487 * 2
def baseEnd_1946487 : Nat := 999483418728231094360775

theorem tailTrace_1946487 : CollatzResearch.WordTrace tailWord_1946487 prefixEnd_1946487 999483418728231094360775 := by
  unfold tailWord_1946487
  simp only [CollatzResearch.WordTrace]
  refine ⟨70994213299217507358325715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47329475532811671572217143 70994213299217507358325715)
  ·
    refine ⟨106491319948826261037488573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70994213299217507358325715 106491319948826261037488573)
    ·
      refine ⟨39934244980809847889058215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106491319948826261037488573 39934244980809847889058215)
      ·
        refine ⟨59901367471214771833587323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39934244980809847889058215 59901367471214771833587323)
        ·
          refine ⟨89852051206822157750380985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59901367471214771833587323 89852051206822157750380985)
          ·
            refine ⟨67389038405116618312785739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89852051206822157750380985 67389038405116618312785739)
            ·
              refine ⟨101083557607674927469178609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67389038405116618312785739 101083557607674927469178609)
              ·
                refine ⟨75812668205756195601883957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101083557607674927469178609 75812668205756195601883957)
                ·
                  refine ⟨7107437644289643337676621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75812668205756195601883957 7107437644289643337676621)
                  ·
                    refine ⟨2665289116608616251628733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7107437644289643337676621 2665289116608616251628733)
                    ·
                      refine ⟨999483418728231094360775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665289116608616251628733 999483418728231094360775)
                      ·
                        rfl

theorem cell23_1946487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1946487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946487 prefixEnd_1946487 := by exact prefixLift 1946487
  have htrace : WordTrace (prefixWord ++ tailWord_1946487) baseStart_1946487 baseEnd_1946487 := by
    simpa [prefixWord, tailWord_1946487, baseEnd_1946487] using wordTrace_append hprefix tailTrace_1946487
  have hstable : (prefixWord ++ tailWord_1946487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946487).length < 2 ^ (prefixWord ++ tailWord_1946487).sum := by decide
  have hdescent : baseEnd_1946487 < baseStart_1946487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946498 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1946498 : Nat := 118140960795 + 1946498 * 2 ^ 59
def prefixEnd_1946498 : Nat := 4983230072969 + 3 ^ 40 * 1946498 * 2
def baseEnd_1946498 : Nat := 333163022338476850441075

theorem tailTrace_1946498 : CollatzResearch.WordTrace tailWord_1946498 prefixEnd_1946498 333163022338476850441075 := by
  unfold tailWord_1946498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748653625544414059244037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47329743001451770824650765 17748653625544414059244037)
  ·
    refine ⟨3327872554789577636108257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17748653625544414059244037 3327872554789577636108257)
    ·
      refine ⟨2495904416092183227081193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327872554789577636108257 2495904416092183227081193)
      ·
        refine ⟨1871928312069137420310895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2495904416092183227081193 1871928312069137420310895)
        ·
          refine ⟨2807892468103706130466343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871928312069137420310895 2807892468103706130466343)
          ·
            refine ⟨4211838702155559195699515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807892468103706130466343 4211838702155559195699515)
            ·
              refine ⟨6317758053233338793549273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211838702155559195699515 6317758053233338793549273)
              ·
                refine ⟨4738318539925004095161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317758053233338793549273 4738318539925004095161955)
                ·
                  refine ⟨7107477809887506142742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738318539925004095161955 7107477809887506142742933)
                  ·
                    refine ⟨333163022338476850441075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7107477809887506142742933 333163022338476850441075)
                    ·
                      rfl

theorem cell23_1946498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1946498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946498 prefixEnd_1946498 := by exact prefixLift 1946498
  have htrace : WordTrace (prefixWord ++ tailWord_1946498) baseStart_1946498 baseEnd_1946498 := by
    simpa [prefixWord, tailWord_1946498, baseEnd_1946498] using wordTrace_append hprefix tailTrace_1946498
  have hstable : (prefixWord ++ tailWord_1946498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946498).length < 2 ^ (prefixWord ++ tailWord_1946498).sum := by decide
  have hdescent : baseEnd_1946498 < baseStart_1946498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946504 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1946504 : Nat := 118140960795 + 1946504 * 2 ^ 59
def prefixEnd_1946504 : Nat := 4983230072969 + 3 ^ 40 * 1946504 * 2
def baseEnd_1946504 : Nat := 999492147899357527848197

theorem tailTrace_1946504 : CollatzResearch.WordTrace tailWord_1946504 prefixEnd_1946504 999492147899357527848197 := by
  unfold tailWord_1946504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497416670077959630847283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47329888893437279507796377 35497416670077959630847283)
  ·
    refine ⟨53246125005116939446270925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35497416670077959630847283 53246125005116939446270925)
    ·
      refine ⟨19967296876918852292351597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53246125005116939446270925 19967296876918852292351597)
      ·
        refine ⟨7487736328844569609631849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19967296876918852292351597 7487736328844569609631849)
        ·
          refine ⟨5615802246633427207223887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487736328844569609631849 5615802246633427207223887)
          ·
            refine ⟨8423703369950140810835831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615802246633427207223887 8423703369950140810835831)
            ·
              refine ⟨12635555054925211216253747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423703369950140810835831 12635555054925211216253747)
              ·
                refine ⟨18953332582387816824380621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635555054925211216253747 18953332582387816824380621)
                ·
                  refine ⟨7107499718395431309142733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18953332582387816824380621 7107499718395431309142733)
                  ·
                    refine ⟨2665312394398286740928525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7107499718395431309142733 2665312394398286740928525)
                    ·
                      refine ⟨999492147899357527848197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665312394398286740928525 999492147899357527848197)
                      ·
                        rfl

theorem cell23_1946504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1946504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946504 prefixEnd_1946504 := by exact prefixLift 1946504
  have htrace : WordTrace (prefixWord ++ tailWord_1946504) baseStart_1946504 baseEnd_1946504 := by
    simpa [prefixWord, tailWord_1946504, baseEnd_1946504] using wordTrace_append hprefix tailTrace_1946504
  have hstable : (prefixWord ++ tailWord_1946504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946504).length < 2 ^ (prefixWord ++ tailWord_1946504).sum := by decide
  have hdescent : baseEnd_1946504 < baseStart_1946504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946537 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_1946537 : Nat := 118140960795 + 1946537 * 2 ^ 59
def prefixEnd_1946537 : Nat := 4983230072969 + 3 ^ 40 * 1946537 * 2
def baseEnd_1946537 : Nat := 333169697586985299578515

theorem tailTrace_1946537 : CollatzResearch.WordTrace tailWord_1946537 prefixEnd_1946537 333169697586985299578515 := by
  unfold tailWord_1946537
  simp only [CollatzResearch.WordTrace]
  refine ⟨70996036949036365897645865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47330691299357577265097243 70996036949036365897645865)
  ·
    refine ⟨53247027711777274423234399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70996036949036365897645865 53247027711777274423234399)
    ·
      refine ⟨79870541567665911634851599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53247027711777274423234399 79870541567665911634851599)
      ·
        refine ⟨119805812351498867452277399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79870541567665911634851599 119805812351498867452277399)
        ·
          refine ⟨179708718527248301178416099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119805812351498867452277399 179708718527248301178416099)
          ·
            refine ⟨269563077790872451767624149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179708718527248301178416099 269563077790872451767624149)
            ·
              refine ⟨6317884635723573088303691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 269563077790872451767624149 6317884635723573088303691)
              ·
                refine ⟨9476826953585359632455537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317884635723573088303691 9476826953585359632455537)
                ·
                  refine ⟨7107620215189019724341653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476826953585359632455537 7107620215189019724341653)
                  ·
                    refine ⟨333169697586985299578515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7107620215189019724341653 333169697586985299578515)
                    ·
                      rfl

theorem cell23_1946537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_1946537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946537 prefixEnd_1946537 := by exact prefixLift 1946537
  have htrace : WordTrace (prefixWord ++ tailWord_1946537) baseStart_1946537 baseEnd_1946537 := by
    simpa [prefixWord, tailWord_1946537, baseEnd_1946537] using wordTrace_append hprefix tailTrace_1946537
  have hstable : (prefixWord ++ tailWord_1946537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946537).length < 2 ^ (prefixWord ++ tailWord_1946537).sum := by decide
  have hdescent : baseEnd_1946537 < baseStart_1946537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946547 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_1946547 : Nat := 118140960795 + 1946547 * 2 ^ 59
def prefixEnd_1946547 : Nat := 4983230072969 + 3 ^ 40 * 1946547 * 2
def baseEnd_1946547 : Nat := 999514227567500859610499

theorem tailTrace_1946547 : CollatzResearch.WordTrace tailWord_1946547 prefixEnd_1946547 999514227567500859610499 := by
  unfold tailWord_1946547
  simp only [CollatzResearch.WordTrace]
  refine ⟨70996401679000137605509895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47330934452666758403673263 70996401679000137605509895)
  ·
    refine ⟨106494602518500206408264843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70996401679000137605509895 106494602518500206408264843)
    ·
      refine ⟨159741903777750309612397265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106494602518500206408264843 159741903777750309612397265)
      ·
        refine ⟨119806427833312732209297949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159741903777750309612397265 119806427833312732209297949)
        ·
          refine ⟨44927410437492274578486731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119806427833312732209297949 44927410437492274578486731)
          ·
            refine ⟨67391115656238411867730097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44927410437492274578486731 67391115656238411867730097)
            ·
              refine ⟨50543336742178808900797573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67391115656238411867730097 50543336742178808900797573)
              ·
                refine ⟨9476875639158526668899545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50543336742178808900797573 9476875639158526668899545)
                ·
                  refine ⟨7107656729368895001674659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476875639158526668899545 7107656729368895001674659)
                  ·
                    refine ⟨10661485094053342502511989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107656729368895001674659 10661485094053342502511989)
                    ·
                      refine ⟨999514227567500859610499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10661485094053342502511989 999514227567500859610499)
                      ·
                        rfl

theorem cell23_1946547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_1946547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946547 prefixEnd_1946547 := by exact prefixLift 1946547
  have htrace : WordTrace (prefixWord ++ tailWord_1946547) baseStart_1946547 baseEnd_1946547 := by
    simpa [prefixWord, tailWord_1946547, baseEnd_1946547] using wordTrace_append hprefix tailTrace_1946547
  have hstable : (prefixWord ++ tailWord_1946547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946547).length < 2 ^ (prefixWord ++ tailWord_1946547).sum := by decide
  have hdescent : baseEnd_1946547 < baseStart_1946547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946566 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1946566 : Nat := 118140960795 + 1946566 * 2 ^ 59
def prefixEnd_1946566 : Nat := 4983230072969 + 3 ^ 40 * 1946566 * 2
def baseEnd_1946566 : Nat := 333174661233312095090971

theorem tailTrace_1946566 : CollatzResearch.WordTrace tailWord_1946566 prefixEnd_1946566 333174661233312095090971 := by
  unfold tailWord_1946566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218659208310353245326611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47331396443954202566967701 2218659208310353245326611)
  ·
    refine ⟨3327988812465529867989917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218659208310353245326611 3327988812465529867989917)
    ·
      refine ⟨1247995804674573700496219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3327988812465529867989917 1247995804674573700496219)
      ·
        refine ⟨1871993707011860550744329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247995804674573700496219 1871993707011860550744329)
        ·
          refine ⟨1403995280258895413058247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1871993707011860550744329 1403995280258895413058247)
          ·
            refine ⟨2105992920388343119587371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403995280258895413058247 2105992920388343119587371)
            ·
              refine ⟨3158989380582514679381057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105992920388343119587371 3158989380582514679381057)
              ·
                refine ⟨2369242035436886009535793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158989380582514679381057 2369242035436886009535793)
                ·
                  refine ⟨1776931526577664507151845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369242035436886009535793 1776931526577664507151845)
                  ·
                    refine ⟨333174661233312095090971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776931526577664507151845 333174661233312095090971)
                    ·
                      rfl

theorem cell23_1946566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1946566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946566 prefixEnd_1946566 := by exact prefixLift 1946566
  have htrace : WordTrace (prefixWord ++ tailWord_1946566) baseStart_1946566 baseEnd_1946566 := by
    simpa [prefixWord, tailWord_1946566, baseEnd_1946566] using wordTrace_append hprefix tailTrace_1946566
  have hstable : (prefixWord ++ tailWord_1946566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946566).length < 2 ^ (prefixWord ++ tailWord_1946566).sum := by decide
  have hdescent : baseEnd_1946566 < baseStart_1946566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946574 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1946574 : Nat := 118140960795 + 1946574 * 2 ^ 59
def prefixEnd_1946574 : Nat := 4983230072969 + 3 ^ 40 * 1946574 * 2
def baseEnd_1946574 : Nat := 999528091545172253972875

theorem tailTrace_1946574 : CollatzResearch.WordTrace tailWord_1946574 prefixEnd_1946574 999528091545172253972875 := by
  unfold tailWord_1946574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874673306237790152092847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47331590966601547477828517 8874673306237790152092847)
  ·
    refine ⟨13312009959356685228139271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8874673306237790152092847 13312009959356685228139271)
    ·
      refine ⟨19968014939035027842208907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13312009959356685228139271 19968014939035027842208907)
      ·
        refine ⟨29952022408552541763313361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19968014939035027842208907 29952022408552541763313361)
        ·
          refine ⟨22464016806414406322485021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29952022408552541763313361 22464016806414406322485021)
          ·
            refine ⟨8424006302405402370931883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22464016806414406322485021 8424006302405402370931883)
            ·
              refine ⟨12636009453608103556397825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424006302405402370931883 12636009453608103556397825)
              ·
                refine ⟨9477007090206077667298369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12636009453608103556397825 9477007090206077667298369)
                ·
                  refine ⟨7107755317654558250473777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9477007090206077667298369 7107755317654558250473777)
                  ·
                    refine ⟨5330816488240918687855333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107755317654558250473777 5330816488240918687855333)
                    ·
                      refine ⟨999528091545172253972875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5330816488240918687855333 999528091545172253972875)
                      ·
                        rfl

theorem cell23_1946574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1946574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946574 prefixEnd_1946574 := by exact prefixLift 1946574
  have htrace : WordTrace (prefixWord ++ tailWord_1946574) baseStart_1946574 baseEnd_1946574 := by
    simpa [prefixWord, tailWord_1946574, baseEnd_1946574] using wordTrace_append hprefix tailTrace_1946574
  have hstable : (prefixWord ++ tailWord_1946574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946574).length < 2 ^ (prefixWord ++ tailWord_1946574).sum := by decide
  have hdescent : baseEnd_1946574 < baseStart_1946574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946584 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 7]
def baseStart_1946584 : Nat := 118140960795 + 1946584 * 2 ^ 59
def prefixEnd_1946584 : Nat := 4983230072969 + 3 ^ 40 * 1946584 * 2
def baseEnd_1946584 : Nat := 111059247372413023871981

theorem tailTrace_1946584 : CollatzResearch.WordTrace tailWord_1946584 prefixEnd_1946584 111059247372413023871981 := by
  unfold tailWord_1946584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35498875589933046462303403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47331834119910728616404537 35498875589933046462303403)
  ·
    refine ⟨53248313384899569693455105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35498875589933046462303403 53248313384899569693455105)
    ·
      refine ⟨39936235038674677270091329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53248313384899569693455105 39936235038674677270091329)
      ·
        refine ⟨29952176279006007952568497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39936235038674677270091329 29952176279006007952568497)
        ·
          refine ⟨22464132209254505964426373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29952176279006007952568497 22464132209254505964426373)
          ·
            refine ⟨4212024789235219868329945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22464132209254505964426373 4212024789235219868329945)
            ·
              refine ⟨3159018591926414901247459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212024789235219868329945 3159018591926414901247459)
              ·
                refine ⟨4738527887889622351871189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159018591926414901247459 4738527887889622351871189)
                ·
                  refine ⟨111059247372413023871981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4738527887889622351871189 111059247372413023871981)
                  ·
                    rfl

theorem cell23_1946584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_1946584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946584 prefixEnd_1946584 := by exact prefixLift 1946584
  have htrace : WordTrace (prefixWord ++ tailWord_1946584) baseStart_1946584 baseEnd_1946584 := by
    simpa [prefixWord, tailWord_1946584, baseEnd_1946584] using wordTrace_append hprefix tailTrace_1946584
  have hstable : (prefixWord ++ tailWord_1946584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946584).length < 2 ^ (prefixWord ++ tailWord_1946584).sum := by decide
  have hdescent : baseEnd_1946584 < baseStart_1946584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946595 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1946595 : Nat := 118140960795 + 1946595 * 2 ^ 59
def prefixEnd_1946595 : Nat := 4983230072969 + 3 ^ 40 * 1946595 * 2
def baseEnd_1946595 : Nat := 999538874638916671810279

theorem tailTrace_1946595 : CollatzResearch.WordTrace tailWord_1946595 prefixEnd_1946595 999538874638916671810279 := by
  unfold tailWord_1946595
  simp only [CollatzResearch.WordTrace]
  refine ⟨70998152382826241803257239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47332101588550827868838159 70998152382826241803257239)
  ·
    refine ⟨106497228574239362704885859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70998152382826241803257239 106497228574239362704885859)
    ·
      refine ⟨159745842861359044057328789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106497228574239362704885859 159745842861359044057328789)
      ·
        refine ⟨7488086384126205190187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159745842861359044057328789 7488086384126205190187287)
        ·
          refine ⟨11232129576189307785280931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488086384126205190187287 11232129576189307785280931)
          ·
            refine ⟨16848194364283961677921397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232129576189307785280931 16848194364283961677921397)
            ·
              refine ⟨1579518221651621407305131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16848194364283961677921397 1579518221651621407305131)
              ·
                refine ⟨2369277332477432110957697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579518221651621407305131 2369277332477432110957697)
                ·
                  refine ⟨1776957999358074083218273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369277332477432110957697 1776957999358074083218273)
                  ·
                    refine ⟨1332718499518555562413705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1776957999358074083218273 1332718499518555562413705)
                    ·
                      refine ⟨999538874638916671810279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332718499518555562413705 999538874638916671810279)
                      ·
                        rfl

theorem cell23_1946595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1946595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946595 prefixEnd_1946595 := by exact prefixLift 1946595
  have htrace : WordTrace (prefixWord ++ tailWord_1946595) baseStart_1946595 baseEnd_1946595 := by
    simpa [prefixWord, tailWord_1946595, baseEnd_1946595] using wordTrace_append hprefix tailTrace_1946595
  have hstable : (prefixWord ++ tailWord_1946595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946595).length < 2 ^ (prefixWord ++ tailWord_1946595).sum := by decide
  have hdescent : baseEnd_1946595 < baseStart_1946595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946695 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 1, 4]
def baseStart_1946695 : Nat := 118140960795 + 1946695 * 2 ^ 59
def prefixEnd_1946695 : Nat := 4983230072969 + 3 ^ 40 * 1946695 * 2
def baseEnd_1946695 : Nat := 333196740901455426853273

theorem tailTrace_1946695 : CollatzResearch.WordTrace tailWord_1946695 prefixEnd_1946695 333196740901455426853273 := by
  unfold tailWord_1946695
  simp only [CollatzResearch.WordTrace]
  refine ⟨71001799682463958881897539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47334533121642639254598359 71001799682463958881897539)
  ·
    refine ⟨106502699523695938322846309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71001799682463958881897539 106502699523695938322846309)
    ·
      refine ⟨19969256160692988435533683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106502699523695938322846309 19969256160692988435533683)
      ·
        refine ⟨29953884241039482653300525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19969256160692988435533683 29953884241039482653300525)
        ·
          refine ⟨11232706590389805994987697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29953884241039482653300525 11232706590389805994987697)
          ·
            refine ⟨8424529942792354496240773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232706590389805994987697 8424529942792354496240773)
            ·
              refine ⟨1579599364273566468045145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8424529942792354496240773 1579599364273566468045145)
              ·
                refine ⟨1184699523205174851033859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579599364273566468045145 1184699523205174851033859)
                ·
                  refine ⟨1777049284807762276550789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184699523205174851033859 1777049284807762276550789)
                  ·
                    refine ⟨333196740901455426853273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1777049284807762276550789 333196740901455426853273)
                    ·
                      rfl

theorem cell23_1946695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_1946695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946695 prefixEnd_1946695 := by exact prefixLift 1946695
  have htrace : WordTrace (prefixWord ++ tailWord_1946695) baseStart_1946695 baseEnd_1946695 := by
    simpa [prefixWord, tailWord_1946695, baseEnd_1946695] using wordTrace_append hprefix tailTrace_1946695
  have hstable : (prefixWord ++ tailWord_1946695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946695).length < 2 ^ (prefixWord ++ tailWord_1946695).sum := by decide
  have hdescent : baseEnd_1946695 < baseStart_1946695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946711 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_1946711 : Nat := 118140960795 + 1946711 * 2 ^ 59
def prefixEnd_1946711 : Nat := 4983230072969 + 3 ^ 40 * 1946711 * 2
def baseEnd_1946711 : Nat := 999598438394838217959745

theorem tailTrace_1946711 : CollatzResearch.WordTrace tailWord_1946711 prefixEnd_1946711 999598438394838217959745 := by
  unfold tailWord_1946711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71002383250405993614479987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47334922166937329076319991 71002383250405993614479987)
  ·
    refine ⟨106503574875608990421719981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71002383250405993614479987 106503574875608990421719981)
    ·
      refine ⟨39938840578353371408144993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106503574875608990421719981 39938840578353371408144993)
      ·
        refine ⟨29954130433765028556108745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39938840578353371408144993 29954130433765028556108745)
        ·
          refine ⟨22465597825323771417081559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29954130433765028556108745 22465597825323771417081559)
          ·
            refine ⟨33698396737985657125622339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22465597825323771417081559 33698396737985657125622339)
            ·
              refine ⟨50547595106978485688433509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33698396737985657125622339 50547595106978485688433509)
              ·
                refine ⟨9477674082558466066581283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50547595106978485688433509 9477674082558466066581283)
                ·
                  refine ⟨14216511123837699099871925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477674082558466066581283 14216511123837699099871925)
                  ·
                    refine ⟨1332797917859784290612993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14216511123837699099871925 1332797917859784290612993)
                    ·
                      refine ⟨999598438394838217959745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332797917859784290612993 999598438394838217959745)
                      ·
                        rfl

theorem cell23_1946711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_1946711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946711 prefixEnd_1946711 := by exact prefixLift 1946711
  have htrace : WordTrace (prefixWord ++ tailWord_1946711) baseStart_1946711 baseEnd_1946711 := by
    simpa [prefixWord, tailWord_1946711, baseEnd_1946711] using wordTrace_append hprefix tailTrace_1946711
  have hstable : (prefixWord ++ tailWord_1946711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946711).length < 2 ^ (prefixWord ++ tailWord_1946711).sum := by decide
  have hdescent : baseEnd_1946711 < baseStart_1946711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946735 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 1, 1, 3]
def baseStart_1946735 : Nat := 118140960795 + 1946735 * 2 ^ 59
def prefixEnd_1946735 : Nat := 4983230072969 + 3 ^ 40 * 1946735 * 2
def baseEnd_1946735 : Nat := 999610761930546124059635

theorem tailTrace_1946735 : CollatzResearch.WordTrace tailWord_1946735 prefixEnd_1946735 999610761930546124059635 := by
  unfold tailWord_1946735
  simp only [CollatzResearch.WordTrace]
  refine ⟨71003258602319045713353659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47335505734879363808902439 71003258602319045713353659)
  ·
    refine ⟨106504887903478568570030489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71003258602319045713353659 106504887903478568570030489)
    ·
      refine ⟨79878665927608926427522867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106504887903478568570030489 79878665927608926427522867)
      ·
        refine ⟨119817998891413389641284301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79878665927608926427522867 119817998891413389641284301)
        ·
          refine ⟨44931749584280021115481613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119817998891413389641284301 44931749584280021115481613)
          ·
            refine ⟨16849406094105007918305605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44931749584280021115481613 16849406094105007918305605)
            ·
              refine ⟨3159263642644688984682301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16849406094105007918305605 3159263642644688984682301)
              ·
                refine ⟨1184723865991758369255863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159263642644688984682301 1184723865991758369255863)
                ·
                  refine ⟨1777085798987637553883795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184723865991758369255863 1777085798987637553883795)
                  ·
                    refine ⟨2665628698481456330825693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777085798987637553883795 2665628698481456330825693)
                    ·
                      refine ⟨999610761930546124059635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665628698481456330825693 999610761930546124059635)
                      ·
                        rfl

theorem cell23_1946735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 1, 3].length) (baseStart_1946735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946735 prefixEnd_1946735 := by exact prefixLift 1946735
  have htrace : WordTrace (prefixWord ++ tailWord_1946735) baseStart_1946735 baseEnd_1946735 := by
    simpa [prefixWord, tailWord_1946735, baseEnd_1946735] using wordTrace_append hprefix tailTrace_1946735
  have hstable : (prefixWord ++ tailWord_1946735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946735).length < 2 ^ (prefixWord ++ tailWord_1946735).sum := by decide
  have hdescent : baseEnd_1946735 < baseStart_1946735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946761 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_1946761 : Nat := 118140960795 + 1946761 * 2 ^ 59
def prefixEnd_1946761 : Nat := 4983230072969 + 3 ^ 40 * 1946761 * 2
def baseEnd_1946761 : Nat := 999624112427563022334515

theorem tailTrace_1946761 : CollatzResearch.WordTrace tailWord_1946761 prefixEnd_1946761 999624112427563022334515 := by
  unfold tailWord_1946761
  simp only [CollatzResearch.WordTrace]
  refine ⟨71004206900224852153800137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47336137933483234769200091 71004206900224852153800137)
  ·
    refine ⟨53253155175168639115350103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71004206900224852153800137 53253155175168639115350103)
    ·
      refine ⟨79879732762752958673025155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53253155175168639115350103 79879732762752958673025155)
      ·
        refine ⟨119819599144129438009537733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79879732762752958673025155 119819599144129438009537733)
        ·
          refine ⟨22466174839524269626788325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119819599144129438009537733 22466174839524269626788325)
          ·
            refine ⟨4212407782410800555022811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22466174839524269626788325 4212407782410800555022811)
            ·
              refine ⟨6318611673616200832534217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212407782410800555022811 6318611673616200832534217)
              ·
                refine ⟨4738958755212150624400663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318611673616200832534217 4738958755212150624400663)
                ·
                  refine ⟨7108438132818225936600995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738958755212150624400663 7108438132818225936600995)
                  ·
                    refine ⟨10662657199227338904901493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108438132818225936600995 10662657199227338904901493)
                    ·
                      refine ⟨999624112427563022334515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10662657199227338904901493 999624112427563022334515)
                      ·
                        rfl

theorem cell23_1946761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_1946761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946761 prefixEnd_1946761 := by exact prefixLift 1946761
  have htrace : WordTrace (prefixWord ++ tailWord_1946761) baseStart_1946761 baseEnd_1946761 := by
    simpa [prefixWord, tailWord_1946761, baseEnd_1946761] using wordTrace_append hprefix tailTrace_1946761
  have hstable : (prefixWord ++ tailWord_1946761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946761).length < 2 ^ (prefixWord ++ tailWord_1946761).sum := by decide
  have hdescent : baseEnd_1946761 < baseStart_1946761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946771 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4]
def baseStart_1946771 : Nat := 118140960795 + 1946771 * 2 ^ 59
def prefixEnd_1946771 : Nat := 4983230072969 + 3 ^ 40 * 1946771 * 2
def baseEnd_1946771 : Nat := 999629247234107983209469

theorem tailTrace_1946771 : CollatzResearch.WordTrace tailWord_1946771 prefixEnd_1946771 999629247234107983209469 := by
  unfold tailWord_1946771
  simp only [CollatzResearch.WordTrace]
  refine ⟨71004571630188623861664167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47336381086792415907776111 71004571630188623861664167)
  ·
    refine ⟨106506857445282935792496251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71004571630188623861664167 106506857445282935792496251)
    ·
      refine ⟨159760286167924403688744377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106506857445282935792496251 159760286167924403688744377)
      ·
        refine ⟨119820214625943302766558283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159760286167924403688744377 119820214625943302766558283)
        ·
          refine ⟨179730321938914954149837425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119820214625943302766558283 179730321938914954149837425)
          ·
            refine ⟨134797741454186215612378069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179730321938914954149837425 134797741454186215612378069)
            ·
              refine ⟨3159322065332489428415111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134797741454186215612378069 3159322065332489428415111)
              ·
                refine ⟨4738983097998734142622667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159322065332489428415111 4738983097998734142622667)
                ·
                  refine ⟨7108474646998101213934001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738983097998734142622667 7108474646998101213934001)
                  ·
                    refine ⟨5331355985248575910450501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108474646998101213934001 5331355985248575910450501)
                    ·
                      refine ⟨999629247234107983209469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5331355985248575910450501 999629247234107983209469)
                      ·
                        rfl

theorem cell23_1946771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_1946771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946771 prefixEnd_1946771 := by exact prefixLift 1946771
  have htrace : WordTrace (prefixWord ++ tailWord_1946771) baseStart_1946771 baseEnd_1946771 := by
    simpa [prefixWord, tailWord_1946771, baseEnd_1946771] using wordTrace_append hprefix tailTrace_1946771
  have hstable : (prefixWord ++ tailWord_1946771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946771).length < 2 ^ (prefixWord ++ tailWord_1946771).sum := by decide
  have hdescent : baseEnd_1946771 < baseStart_1946771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946775 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1946775 : Nat := 118140960795 + 1946775 * 2 ^ 59
def prefixEnd_1946775 : Nat := 4983230072969 + 3 ^ 40 * 1946775 * 2
def baseEnd_1946775 : Nat := 999631301156725967559451

theorem tailTrace_1946775 : CollatzResearch.WordTrace tailWord_1946775 prefixEnd_1946775 999631301156725967559451 := by
  unfold tailWord_1946775
  simp only [CollatzResearch.WordTrace]
  refine ⟨71004717522174132544809779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47336478348116088363206519 71004717522174132544809779)
  ·
    refine ⟨106507076283261198817214669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71004717522174132544809779 106507076283261198817214669)
    ·
      refine ⟨39940153606222949556455501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106507076283261198817214669 39940153606222949556455501)
      ·
        refine ⟨14977557602333606083670813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39940153606222949556455501 14977557602333606083670813)
        ·
          refine ⟨5616584100875102281376555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14977557602333606083670813 5616584100875102281376555)
          ·
            refine ⟨8424876151312653422064833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616584100875102281376555 8424876151312653422064833)
            ·
              refine ⟨6318657113484490066548625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8424876151312653422064833 6318657113484490066548625)
              ·
                refine ⟨4738992835113367549911469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318657113484490066548625 4738992835113367549911469)
                ·
                  refine ⟨1777122313167512831216801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4738992835113367549911469 1777122313167512831216801)
                  ·
                    refine ⟨1332841734875634623412601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1777122313167512831216801 1332841734875634623412601)
                    ·
                      refine ⟨999631301156725967559451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332841734875634623412601 999631301156725967559451)
                      ·
                        rfl

theorem cell23_1946775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1946775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946775 prefixEnd_1946775 := by exact prefixLift 1946775
  have htrace : WordTrace (prefixWord ++ tailWord_1946775) baseStart_1946775 baseEnd_1946775 := by
    simpa [prefixWord, tailWord_1946775, baseEnd_1946775] using wordTrace_append hprefix tailTrace_1946775
  have hstable : (prefixWord ++ tailWord_1946775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946775).length < 2 ^ (prefixWord ++ tailWord_1946775).sum := by decide
  have hdescent : baseEnd_1946775 < baseStart_1946775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946786 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1946786 : Nat := 118140960795 + 1946786 * 2 ^ 59
def prefixEnd_1946786 : Nat := 4983230072969 + 3 ^ 40 * 1946786 * 2
def baseEnd_1946786 : Nat := 999636949443925424521901

theorem tailTrace_1946786 : CollatzResearch.WordTrace tailWord_1946786 prefixEnd_1946786 999636949443925424521901 := by
  unfold tailWord_1946786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751279681283570355865053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47336745816756187615640141 17751279681283570355865053)
  ·
    refine ⟨6656729880481338883449395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17751279681283570355865053 6656729880481338883449395)
    ·
      refine ⟨9985094820722008325174093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656729880481338883449395 9985094820722008325174093)
      ·
        refine ⟨3744410557770753121940285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9985094820722008325174093 3744410557770753121940285)
        ·
          refine ⟨1404153959164032420727607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3744410557770753121940285 1404153959164032420727607)
          ·
            refine ⟨2106230938746048631091411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404153959164032420727607 2106230938746048631091411)
            ·
              refine ⟨3159346408119072946637117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106230938746048631091411 3159346408119072946637117)
              ·
                refine ⟨1184754903044652354988919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159346408119072946637117 1184754903044652354988919)
                ·
                  refine ⟨1777132354566978532483379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184754903044652354988919 1777132354566978532483379)
                  ·
                    refine ⟨2665698531850467798725069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777132354566978532483379 2665698531850467798725069)
                    ·
                      refine ⟨999636949443925424521901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665698531850467798725069 999636949443925424521901)
                      ·
                        rfl

theorem cell23_1946786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1946786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946786 prefixEnd_1946786 := by exact prefixLift 1946786
  have htrace : WordTrace (prefixWord ++ tailWord_1946786) baseStart_1946786 baseEnd_1946786 := by
    simpa [prefixWord, tailWord_1946786, baseEnd_1946786] using wordTrace_append hprefix tailTrace_1946786
  have hstable : (prefixWord ++ tailWord_1946786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946786).length < 2 ^ (prefixWord ++ tailWord_1946786).sum := by decide
  have hdescent : baseEnd_1946786 < baseStart_1946786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946809 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 1, 2, 2]
def baseStart_1946809 : Nat := 118140960795 + 1946809 * 2 ^ 59
def prefixEnd_1946809 : Nat := 4983230072969 + 3 ^ 40 * 1946809 * 2
def baseEnd_1946809 : Nat := 999648759498978834534295

theorem tailTrace_1946809 : CollatzResearch.WordTrace tailWord_1946809 prefixEnd_1946809 999648759498978834534295 := by
  unfold tailWord_1946809
  simp only [CollatzResearch.WordTrace]
  refine ⟨71005957604050956351547481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47337305069367304234364987 71005957604050956351547481)
  ·
    refine ⟨53254468203038217263660611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71005957604050956351547481 53254468203038217263660611)
    ·
      refine ⟨79881702304557325895490917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53254468203038217263660611 79881702304557325895490917)
      ·
        refine ⟨14977819182104498605404547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79881702304557325895490917 14977819182104498605404547)
        ·
          refine ⟨22466728773156747908106821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977819182104498605404547 22466728773156747908106821)
          ·
            refine ⟨4212511644966890232770029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22466728773156747908106821 4212511644966890232770029)
            ·
              refine ⟨1579691866862583837288761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4212511644966890232770029 1579691866862583837288761)
              ·
                refine ⟨1184768900146937877966571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579691866862583837288761 1184768900146937877966571)
                ·
                  refine ⟨1777153350220406816949857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184768900146937877966571 1777153350220406816949857)
                  ·
                    refine ⟨1332865012665305112712393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1777153350220406816949857 1332865012665305112712393)
                    ·
                      refine ⟨999648759498978834534295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332865012665305112712393 999648759498978834534295)
                      ·
                        rfl

theorem cell23_1946809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_1946809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946809 prefixEnd_1946809 := by exact prefixLift 1946809
  have htrace : WordTrace (prefixWord ++ tailWord_1946809) baseStart_1946809 baseEnd_1946809 := by
    simpa [prefixWord, tailWord_1946809, baseEnd_1946809] using wordTrace_append hprefix tailTrace_1946809
  have hstable : (prefixWord ++ tailWord_1946809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946809).length < 2 ^ (prefixWord ++ tailWord_1946809).sum := by decide
  have hdescent : baseEnd_1946809 < baseStart_1946809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946848 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2]
def baseStart_1946848 : Nat := 118140960795 + 1946848 * 2 ^ 59
def prefixEnd_1946848 : Nat := 4983230072969 + 3 ^ 40 * 1946848 * 2
def baseEnd_1946848 : Nat := 999668785244504181946615

theorem tailTrace_1946848 : CollatzResearch.WordTrace tailWord_1946848 prefixEnd_1946848 999668785244504181946615 := by
  unfold tailWord_1946848
  simp only [CollatzResearch.WordTrace]
  refine ⟨35503690025454833006108599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47338253367273110674811465 35503690025454833006108599)
  ·
    refine ⟨53255535038182249509162899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35503690025454833006108599 53255535038182249509162899)
    ·
      refine ⟨79883302557273374263744349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53255535038182249509162899 79883302557273374263744349)
      ·
        refine ⟨29956238458977515348904131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79883302557273374263744349 29956238458977515348904131)
        ·
          refine ⟨44934357688466273023356197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29956238458977515348904131 44934357688466273023356197)
          ·
            refine ⟨8425192066587426191879287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44934357688466273023356197 8425192066587426191879287)
            ·
              refine ⟨12637788099881139287818931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425192066587426191879287 12637788099881139287818931)
              ·
                refine ⟨18956682149821708931728397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637788099881139287818931 18956682149821708931728397)
                ·
                  refine ⟨7108755806183140849398149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18956682149821708931728397 7108755806183140849398149)
                  ·
                    refine ⟨1332891713659338909262153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7108755806183140849398149 1332891713659338909262153)
                    ·
                      refine ⟨999668785244504181946615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1332891713659338909262153 999668785244504181946615)
                      ·
                        rfl

theorem cell23_1946848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_1946848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946848 prefixEnd_1946848 := by exact prefixLift 1946848
  have htrace : WordTrace (prefixWord ++ tailWord_1946848) baseStart_1946848 baseEnd_1946848 := by
    simpa [prefixWord, tailWord_1946848, baseEnd_1946848] using wordTrace_append hprefix tailTrace_1946848
  have hstable : (prefixWord ++ tailWord_1946848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946848).length < 2 ^ (prefixWord ++ tailWord_1946848).sum := by decide
  have hdescent : baseEnd_1946848 < baseStart_1946848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946878 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1946878 : Nat := 118140960795 + 1946878 * 2 ^ 59
def prefixEnd_1946878 : Nat := 4983230072969 + 3 ^ 40 * 1946878 * 2
def baseEnd_1946878 : Nat := 999684189664139064571477

theorem tailTrace_1946878 : CollatzResearch.WordTrace tailWord_1946878 prefixEnd_1946878 999684189664139064571477 := by
  unfold tailWord_1946878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876059280100122641976161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47338982827200654090539525 8876059280100122641976161)
  ·
    refine ⟨6657044460075091981482121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8876059280100122641976161 6657044460075091981482121)
    ·
      refine ⟨4992783345056318986111591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657044460075091981482121 4992783345056318986111591)
      ·
        refine ⟨7489175017584478479167387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992783345056318986111591 7489175017584478479167387)
        ·
          refine ⟨11233762526376717718751081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489175017584478479167387 11233762526376717718751081)
          ·
            refine ⟨8425321894782538289063311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11233762526376717718751081 8425321894782538289063311)
            ·
              refine ⟨12637982842173807433594967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425321894782538289063311 12637982842173807433594967)
              ·
                refine ⟨18956974263260711150392451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637982842173807433594967 18956974263260711150392451)
                ·
                  refine ⟨28435461394891066725588677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18956974263260711150392451 28435461394891066725588677)
                  ·
                    refine ⟨5331649011542075011047877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28435461394891066725588677 5331649011542075011047877)
                    ·
                      refine ⟨999684189664139064571477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5331649011542075011047877 999684189664139064571477)
                      ·
                        rfl

theorem cell23_1946878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1946878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946878 prefixEnd_1946878 := by exact prefixLift 1946878
  have htrace : WordTrace (prefixWord ++ tailWord_1946878) baseStart_1946878 baseEnd_1946878 := by
    simpa [prefixWord, tailWord_1946878, baseEnd_1946878] using wordTrace_append hprefix tailTrace_1946878
  have hstable : (prefixWord ++ tailWord_1946878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946878).length < 2 ^ (prefixWord ++ tailWord_1946878).sum := by decide
  have hdescent : baseEnd_1946878 < baseStart_1946878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946888 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 7]
def baseStart_1946888 : Nat := 118140960795 + 1946888 * 2 ^ 59
def prefixEnd_1946888 : Nat := 4983230072969 + 3 ^ 40 * 1946888 * 2
def baseEnd_1946888 : Nat := 111076591607853780605159

theorem tailTrace_1946888 : CollatzResearch.WordTrace tailWord_1946888 prefixEnd_1946888 111076591607853780605159 := by
  unfold tailWord_1946888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35504419485382376421836659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47339225980509835229115545 35504419485382376421836659)
  ·
    refine ⟨53256629228073564632754989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35504419485382376421836659 53256629228073564632754989)
    ·
      refine ⟨19971235960527586737283121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53256629228073564632754989 19971235960527586737283121)
      ·
        refine ⟨14978426970395690052962341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19971235960527586737283121 14978426970395690052962341)
        ·
          refine ⟨2808455056949191884930439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14978426970395690052962341 2808455056949191884930439)
          ·
            refine ⟨4212682585423787827395659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808455056949191884930439 4212682585423787827395659)
            ·
              refine ⟨6319023878135681741093489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212682585423787827395659 6319023878135681741093489)
              ·
                refine ⟨4739267908601761305820117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319023878135681741093489 4739267908601761305820117)
                ·
                  refine ⟨111076591607853780605159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4739267908601761305820117 111076591607853780605159)
                  ·
                    rfl

theorem cell23_1946888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_1946888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946888 prefixEnd_1946888 := by exact prefixLift 1946888
  have htrace : WordTrace (prefixWord ++ tailWord_1946888) baseStart_1946888 baseEnd_1946888 := by
    simpa [prefixWord, tailWord_1946888, baseEnd_1946888] using wordTrace_append hprefix tailTrace_1946888
  have hstable : (prefixWord ++ tailWord_1946888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946888).length < 2 ^ (prefixWord ++ tailWord_1946888).sum := by decide
  have hdescent : baseEnd_1946888 < baseStart_1946888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946958 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1946958 : Nat := 118140960795 + 1946958 * 2 ^ 59
def prefixEnd_1946958 : Nat := 4983230072969 + 3 ^ 40 * 1946958 * 2
def baseEnd_1946958 : Nat := 999725268116498751571109

theorem tailTrace_1946958 : CollatzResearch.WordTrace tailWord_1946958 prefixEnd_1946958 999725268116498751571109 := by
  unfold tailWord_1946958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876424010063894349840191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47340928053674103199147685 8876424010063894349840191)
  ·
    refine ⟨13314636015095841524760287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8876424010063894349840191 13314636015095841524760287)
    ·
      refine ⟨19971954022643762287140431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314636015095841524760287 19971954022643762287140431)
      ·
        refine ⟨29957931033965643430710647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19971954022643762287140431 29957931033965643430710647)
        ·
          refine ⟨44936896550948465146065971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29957931033965643430710647 44936896550948465146065971)
          ·
            refine ⟨67405344826422697719098957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44936896550948465146065971 67405344826422697719098957)
            ·
              refine ⟨25277004309908511644662109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67405344826422697719098957 25277004309908511644662109)
              ·
                refine ⟨9478876616215691866748291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25277004309908511644662109 9478876616215691866748291)
                ·
                  refine ⟨14218314924323537800122437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478876616215691866748291 14218314924323537800122437)
                  ·
                    refine ⟨2665934048310663337522957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14218314924323537800122437 2665934048310663337522957)
                    ·
                      refine ⟨999725268116498751571109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665934048310663337522957 999725268116498751571109)
                      ·
                        rfl

theorem cell23_1946958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1946958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946958 prefixEnd_1946958 := by exact prefixLift 1946958
  have htrace : WordTrace (prefixWord ++ tailWord_1946958) baseStart_1946958 baseEnd_1946958 := by
    simpa [prefixWord, tailWord_1946958, baseEnd_1946958] using wordTrace_append hprefix tailTrace_1946958
  have hstable : (prefixWord ++ tailWord_1946958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946958).length < 2 ^ (prefixWord ++ tailWord_1946958).sum := by decide
  have hdescent : baseEnd_1946958 < baseStart_1946958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946961 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 10]
def baseStart_1946961 : Nat := 118140960795 + 1946961 * 2 ^ 59
def prefixEnd_1946961 : Nat := 4983230072969 + 3 ^ 40 * 1946961 * 2
def baseEnd_1946961 : Nat := 111080756506495804425955

theorem tailTrace_1946961 : CollatzResearch.WordTrace tailWord_1946961 prefixEnd_1946961 111080756506495804425955 := by
  unfold tailWord_1946961
  simp only [CollatzResearch.WordTrace]
  refine ⟨71011501499500286311080737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47341000999666857540720491 71011501499500286311080737)
  ·
    refine ⟨53258626124625214733310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71011501499500286311080737 53258626124625214733310553)
    ·
      refine ⟨39943969593468911049982915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53258626124625214733310553 39943969593468911049982915)
      ·
        refine ⟨59915954390203366574974373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39943969593468911049982915 59915954390203366574974373)
        ·
          refine ⟨11234241448163131232807695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59915954390203366574974373 11234241448163131232807695)
          ·
            refine ⟨16851362172244696849211543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234241448163131232807695 16851362172244696849211543)
            ·
              refine ⟨25277043258367045273817315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851362172244696849211543 25277043258367045273817315)
              ·
                refine ⟨37915564887550567910725973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25277043258367045273817315 37915564887550567910725973)
                ·
                  refine ⟨111080756506495804425955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37915564887550567910725973 111080756506495804425955)
                  ·
                    rfl

theorem cell23_1946961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_1946961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946961 prefixEnd_1946961 := by exact prefixLift 1946961
  have htrace : WordTrace (prefixWord ++ tailWord_1946961) baseStart_1946961 baseEnd_1946961 := by
    simpa [prefixWord, tailWord_1946961, baseEnd_1946961] using wordTrace_append hprefix tailTrace_1946961
  have hstable : (prefixWord ++ tailWord_1946961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946961).length < 2 ^ (prefixWord ++ tailWord_1946961).sum := by decide
  have hdescent : baseEnd_1946961 < baseStart_1946961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946978 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1946978 : Nat := 118140960795 + 1946978 * 2 ^ 59
def prefixEnd_1946978 : Nat := 4983230072969 + 3 ^ 40 * 1946978 * 2
def baseEnd_1946978 : Nat := 111081726414398741480113

theorem tailTrace_1946978 : CollatzResearch.WordTrace tailWord_1946978 prefixEnd_1946978 111081726414398741480113 := by
  unfold tailWord_1946978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753030385109674553612397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47341414360292465476299725 17753030385109674553612397)
  ·
    refine ⟨6657386394416127957604649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17753030385109674553612397 6657386394416127957604649)
    ·
      refine ⟨4993039795812095968203487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657386394416127957604649 4993039795812095968203487)
      ·
        refine ⟨7489559693718143952305231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993039795812095968203487 7489559693718143952305231)
        ·
          refine ⟨11234339540577215928457847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489559693718143952305231 11234339540577215928457847)
          ·
            refine ⟨16851509310865823892686771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234339540577215928457847 16851509310865823892686771)
            ·
              refine ⟨25277263966298735839030157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851509310865823892686771 25277263966298735839030157)
              ·
                refine ⟨9478973987362025939636309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25277263966298735839030157 9478973987362025939636309)
                ·
                  refine ⟨111081726414398741480113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9478973987362025939636309 111081726414398741480113)
                  ·
                    rfl

theorem cell23_1946978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1946978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1946978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1946978 prefixEnd_1946978 := by exact prefixLift 1946978
  have htrace : WordTrace (prefixWord ++ tailWord_1946978) baseStart_1946978 baseEnd_1946978 := by
    simpa [prefixWord, tailWord_1946978, baseEnd_1946978] using wordTrace_append hprefix tailTrace_1946978
  have hstable : (prefixWord ++ tailWord_1946978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946978).length < 2 ^ (prefixWord ++ tailWord_1946978).sum := by decide
  have hdescent : baseEnd_1946978 < baseStart_1946978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947005 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_1947005 : Nat := 118140960795 + 1947005 * 2 ^ 59
def prefixEnd_1947005 : Nat := 4983230072969 + 3 ^ 40 * 1947005 * 2
def baseEnd_1947005 : Nat := 999749401707260067683393

theorem tailTrace_1947005 : CollatzResearch.WordTrace tailWord_1947005 prefixEnd_1947005 999749401707260067683393 := by
  unfold tailWord_1947005
  simp only [CollatzResearch.WordTrace]
  refine ⟨71013106311340881825682469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47342070874227254550454979 71013106311340881825682469)
  ·
    refine ⟨13314957433376415342315463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71013106311340881825682469 13314957433376415342315463)
    ·
      refine ⟨19972436150064623013473195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314957433376415342315463 19972436150064623013473195)
      ·
        refine ⟨29958654225096934520209793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19972436150064623013473195 29958654225096934520209793)
        ·
          refine ⟨22468990668822700890157345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29958654225096934520209793 22468990668822700890157345)
          ·
            refine ⟨16851743001617025667618009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22468990668822700890157345 16851743001617025667618009)
            ·
              refine ⟨12638807251212769250713507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16851743001617025667618009 12638807251212769250713507)
              ·
                refine ⟨18958210876819153876070261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12638807251212769250713507 18958210876819153876070261)
                ·
                  refine ⟨1777332269701795675881587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18958210876819153876070261 1777332269701795675881587)
                  ·
                    refine ⟨2665998404552693513822381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777332269701795675881587 2665998404552693513822381)
                    ·
                      refine ⟨999749401707260067683393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2665998404552693513822381 999749401707260067683393)
                      ·
                        rfl

theorem cell23_1947005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_1947005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947005 prefixEnd_1947005 := by exact prefixLift 1947005
  have htrace : WordTrace (prefixWord ++ tailWord_1947005) baseStart_1947005 baseEnd_1947005 := by
    simpa [prefixWord, tailWord_1947005, baseEnd_1947005] using wordTrace_append hprefix tailTrace_1947005
  have hstable : (prefixWord ++ tailWord_1947005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947005).length < 2 ^ (prefixWord ++ tailWord_1947005).sum := by decide
  have hdescent : baseEnd_1947005 < baseStart_1947005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947039 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 1, 1, 3]
def baseStart_1947039 : Nat := 118140960795 + 1947039 * 2 ^ 59
def prefixEnd_1947039 : Nat := 4983230072969 + 3 ^ 40 * 1947039 * 2
def baseEnd_1947039 : Nat := 999766860049512934658237

theorem tailTrace_1947039 : CollatzResearch.WordTrace tailWord_1947039 prefixEnd_1947039 999766860049512934658237 := by
  unfold tailWord_1947039
  simp only [CollatzResearch.WordTrace]
  refine ⟨71014346393217705632420171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47342897595478470421613447 71014346393217705632420171)
  ·
    refine ⟨106521519589826558448630257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71014346393217705632420171 106521519589826558448630257)
    ·
      refine ⟨79891139692369918836472693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106521519589826558448630257 79891139692369918836472693)
      ·
        refine ⟨7489794346159679890919315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79891139692369918836472693 7489794346159679890919315)
        ·
          refine ⟨11234691519239519836378973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489794346159679890919315 11234691519239519836378973)
          ·
            refine ⟨4213009319714819938642115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11234691519239519836378973 4213009319714819938642115)
            ·
              refine ⟨6319513979572229907963173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213009319714819938642115 6319513979572229907963173)
              ·
                refine ⟨1184908871169793107743095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6319513979572229907963173 1184908871169793107743095)
                ·
                  refine ⟨1777363306754689661614643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184908871169793107743095 1777363306754689661614643)
                  ·
                    refine ⟨2666044960132034492421965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777363306754689661614643 2666044960132034492421965)
                    ·
                      refine ⟨999766860049512934658237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666044960132034492421965 999766860049512934658237)
                      ·
                        rfl

theorem cell23_1947039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_1947039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947039 prefixEnd_1947039 := by exact prefixLift 1947039
  have htrace : WordTrace (prefixWord ++ tailWord_1947039) baseStart_1947039 baseEnd_1947039 := by
    simpa [prefixWord, tailWord_1947039, baseEnd_1947039] using wordTrace_append hprefix tailTrace_1947039
  have hstable : (prefixWord ++ tailWord_1947039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947039).length < 2 ^ (prefixWord ++ tailWord_1947039).sum := by decide
  have hdescent : baseEnd_1947039 < baseStart_1947039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947082 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_1947082 : Nat := 118140960795 + 1947082 * 2 ^ 59
def prefixEnd_1947082 : Nat := 4983230072969 + 3 ^ 40 * 1947082 * 2
def baseEnd_1947082 : Nat := 999788939717656266420539

theorem tailTrace_1947082 : CollatzResearch.WordTrace tailWord_1947082 prefixEnd_1947082 999788939717656266420539 := by
  unfold tailWord_1947082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753978683015480994058875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47343943154707949317490333 17753978683015480994058875)
  ·
    refine ⟨26630968024523221491088313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17753978683015480994058875 26630968024523221491088313)
    ·
      refine ⟨19973226018392416118316235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26630968024523221491088313 19973226018392416118316235)
      ·
        refine ⟨29959839027588624177474353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19973226018392416118316235 29959839027588624177474353)
        ·
          refine ⟨22469879270691468133105765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29959839027588624177474353 22469879270691468133105765)
          ·
            refine ⟨4213102363254650274957331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22469879270691468133105765 4213102363254650274957331)
            ·
              refine ⟨6319653544881975412435997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213102363254650274957331 6319653544881975412435997)
              ·
                refine ⟨2369870079330740779663499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6319653544881975412435997 2369870079330740779663499)
                ·
                  refine ⟨3554805118996111169495249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369870079330740779663499 3554805118996111169495249)
                  ·
                    refine ⟨2666103839247083377121437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3554805118996111169495249 2666103839247083377121437)
                    ·
                      refine ⟨999788939717656266420539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666103839247083377121437 999788939717656266420539)
                      ·
                        rfl

theorem cell23_1947082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_1947082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947082 prefixEnd_1947082 := by exact prefixLift 1947082
  have htrace : WordTrace (prefixWord ++ tailWord_1947082) baseStart_1947082 baseEnd_1947082 := by
    simpa [prefixWord, tailWord_1947082, baseEnd_1947082] using wordTrace_append hprefix tailTrace_1947082
  have hstable : (prefixWord ++ tailWord_1947082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947082).length < 2 ^ (prefixWord ++ tailWord_1947082).sum := by decide
  have hdescent : baseEnd_1947082 < baseStart_1947082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947108 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1947108 : Nat := 118140960795 + 1947108 * 2 ^ 59
def prefixEnd_1947108 : Nat := 4983230072969 + 3 ^ 40 * 1947108 * 2
def baseEnd_1947108 : Nat := 999802290214673164695419

theorem tailTrace_1947108 : CollatzResearch.WordTrace tailWord_1947108 prefixEnd_1947108 999802290214673164695419 := by
  unfold tailWord_1947108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508431514983865208340989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47344575353311820277787985 35508431514983865208340989)
  ·
    refine ⟨13315661818118949453127871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35508431514983865208340989 13315661818118949453127871)
    ·
      refine ⟨19973492727178424179691807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13315661818118949453127871 19973492727178424179691807)
      ·
        refine ⟨29960239090767636269537711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19973492727178424179691807 29960239090767636269537711)
        ·
          refine ⟨44940358636151454404306567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29960239090767636269537711 44940358636151454404306567)
          ·
            refine ⟨67410537954227181606459851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44940358636151454404306567 67410537954227181606459851)
            ·
              refine ⟨101115806931340772409689777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67410537954227181606459851 101115806931340772409689777)
              ·
                refine ⟨75836855198505579307267333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101115806931340772409689777 75836855198505579307267333)
                ·
                  refine ⟨14219410349719796120112625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75836855198505579307267333 14219410349719796120112625)
                  ·
                    refine ⟨10664557762289847090084469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14219410349719796120112625 10664557762289847090084469)
                    ·
                      refine ⟨999802290214673164695419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10664557762289847090084469 999802290214673164695419)
                      ·
                        rfl

theorem cell23_1947108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1947108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947108 prefixEnd_1947108 := by exact prefixLift 1947108
  have htrace : WordTrace (prefixWord ++ tailWord_1947108) baseStart_1947108 baseEnd_1947108 := by
    simpa [prefixWord, tailWord_1947108, baseEnd_1947108] using wordTrace_append hprefix tailTrace_1947108
  have hstable : (prefixWord ++ tailWord_1947108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947108).length < 2 ^ (prefixWord ++ tailWord_1947108).sum := by decide
  have hdescent : baseEnd_1947108 < baseStart_1947108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947165 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1947165 : Nat := 118140960795 + 1947165 * 2 ^ 59
def prefixEnd_1947165 : Nat := 4983230072969 + 3 ^ 40 * 1947165 * 2
def baseEnd_1947165 : Nat := 999831558611979441682657

theorem tailTrace_1947165 : CollatzResearch.WordTrace tailWord_1947165 prefixEnd_1947165 999831558611979441682657 := by
  unfold tailWord_1947165
  simp only [CollatzResearch.WordTrace]
  refine ⟨71018941990761229151506949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47345961327174152767671299 71018941990761229151506949)
  ·
    refine ⟨13316051623267730465907553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71018941990761229151506949 13316051623267730465907553)
    ·
      refine ⟨9987038717450797849430665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13316051623267730465907553 9987038717450797849430665)
      ·
        refine ⟨7490279038088098387072999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9987038717450797849430665 7490279038088098387072999)
        ·
          refine ⟨11235418557132147580609499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490279038088098387072999 11235418557132147580609499)
          ·
            refine ⟨16853127835698221370914249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235418557132147580609499 16853127835698221370914249)
            ·
              refine ⟨12639845876773666028185687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16853127835698221370914249 12639845876773666028185687)
              ·
                refine ⟨18959768815160499042278531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639845876773666028185687 18959768815160499042278531)
                ·
                  refine ⟨28439653222740748563417797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18959768815160499042278531 28439653222740748563417797)
                  ·
                    refine ⟨5332434979263890355640837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28439653222740748563417797 5332434979263890355640837)
                    ·
                      refine ⟨999831558611979441682657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5332434979263890355640837 999831558611979441682657)
                      ·
                        rfl

theorem cell23_1947165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1947165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947165 prefixEnd_1947165 := by exact prefixLift 1947165
  have htrace : WordTrace (prefixWord ++ tailWord_1947165) baseStart_1947165 baseEnd_1947165 := by
    simpa [prefixWord, tailWord_1947165, baseEnd_1947165] using wordTrace_append hprefix tailTrace_1947165
  have hstable : (prefixWord ++ tailWord_1947165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947165).length < 2 ^ (prefixWord ++ tailWord_1947165).sum := by decide
  have hdescent : baseEnd_1947165 < baseStart_1947165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947185 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1947185 : Nat := 118140960795 + 1947185 * 2 ^ 59
def prefixEnd_1947185 : Nat := 4983230072969 + 3 ^ 40 * 1947185 * 2
def baseEnd_1947185 : Nat := 999841828225069363432565

theorem tailTrace_1947185 : CollatzResearch.WordTrace tailWord_1947185 prefixEnd_1947185 999841828225069363432565 := by
  unfold tailWord_1947185
  simp only [CollatzResearch.WordTrace]
  refine ⟨71019671450688772567235009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47346447633792515044823339 71019671450688772567235009)
  ·
    refine ⟨53264753588016579425426257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71019671450688772567235009 53264753588016579425426257)
    ·
      refine ⟨39948565191012434569069693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53264753588016579425426257 39948565191012434569069693)
      ·
        refine ⟨14980711946629662963401135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39948565191012434569069693 14980711946629662963401135)
        ·
          refine ⟨22471067919944494445101703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14980711946629662963401135 22471067919944494445101703)
          ·
            refine ⟨33706601879916741667652555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22471067919944494445101703 33706601879916741667652555)
            ·
              refine ⟨50559902819875112501478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33706601879916741667652555 50559902819875112501478833)
              ·
                refine ⟨37919927114906334376109125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50559902819875112501478833 37919927114906334376109125)
                ·
                  refine ⟨7109986334044937695520461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37919927114906334376109125 7109986334044937695520461)
                  ·
                    refine ⟨2666244875266851635820173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7109986334044937695520461 2666244875266851635820173)
                    ·
                      refine ⟨999841828225069363432565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666244875266851635820173 999841828225069363432565)
                      ·
                        rfl

theorem cell23_1947185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1947185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947185 prefixEnd_1947185 := by exact prefixLift 1947185
  have htrace : WordTrace (prefixWord ++ tailWord_1947185) baseStart_1947185 baseEnd_1947185 := by
    simpa [prefixWord, tailWord_1947185, baseEnd_1947185] using wordTrace_append hprefix tailTrace_1947185
  have hstable : (prefixWord ++ tailWord_1947185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947185).length < 2 ^ (prefixWord ++ tailWord_1947185).sum := by decide
  have hdescent : baseEnd_1947185 < baseStart_1947185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947205 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1947205 : Nat := 118140960795 + 1947205 * 2 ^ 59
def prefixEnd_1947205 : Nat := 4983230072969 + 3 ^ 40 * 1947205 * 2
def baseEnd_1947205 : Nat := 333284032612719761727491

theorem tailTrace_1947205 : CollatzResearch.WordTrace tailWord_1947205 prefixEnd_1947205 333284032612719761727491 := by
  unfold tailWord_1947205
  simp only [CollatzResearch.WordTrace]
  refine ⟨71020400910616315982963069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47346933940410877321975379 71020400910616315982963069)
  ·
    refine ⟨26632650341481118493611151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71020400910616315982963069 26632650341481118493611151)
    ·
      refine ⟨39948975512221677740416727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26632650341481118493611151 39948975512221677740416727)
      ·
        refine ⟨59923463268332516610625091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39948975512221677740416727 59923463268332516610625091)
        ·
          refine ⟨89885194902498774915937637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59923463268332516610625091 89885194902498774915937637)
          ·
            refine ⟨16853474044218520296738307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89885194902498774915937637 16853474044218520296738307)
            ·
              refine ⟨25280211066327780445107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16853474044218520296738307 25280211066327780445107461)
              ·
                refine ⟨4740039574936458833457649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25280211066327780445107461 4740039574936458833457649)
                ·
                  refine ⟨3555029681202344125093237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740039574936458833457649 3555029681202344125093237)
                  ·
                    refine ⟨333284032612719761727491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555029681202344125093237 333284032612719761727491)
                    ·
                      rfl

theorem cell23_1947205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1947205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947205 prefixEnd_1947205 := by exact prefixLift 1947205
  have htrace : WordTrace (prefixWord ++ tailWord_1947205) baseStart_1947205 baseEnd_1947205 := by
    simpa [prefixWord, tailWord_1947205, baseEnd_1947205] using wordTrace_append hprefix tailTrace_1947205
  have hstable : (prefixWord ++ tailWord_1947205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947205).length < 2 ^ (prefixWord ++ tailWord_1947205).sum := by decide
  have hdescent : baseEnd_1947205 < baseStart_1947205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947212 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_1947212 : Nat := 118140960795 + 1947212 * 2 ^ 59
def prefixEnd_1947212 : Nat := 4983230072969 + 3 ^ 40 * 1947212 * 2
def baseEnd_1947212 : Nat := 999855692202740757794941

theorem tailTrace_1947212 : CollatzResearch.WordTrace tailWord_1947212 prefixEnd_1947212 999855692202740757794941 := by
  unfold tailWord_1947212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35510328110795478089233945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47347104147727304118978593 35510328110795478089233945)
  ·
    refine ⟨26632746083096608566925459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35510328110795478089233945 26632746083096608566925459)
    ·
      refine ⟨39949119124644912850388189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26632746083096608566925459 39949119124644912850388189)
      ·
        refine ⟨14980919671741842318895571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39949119124644912850388189 14980919671741842318895571)
        ·
          refine ⟨22471379507612763478343357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14980919671741842318895571 22471379507612763478343357)
          ·
            refine ⟨8426767315354786304378759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22471379507612763478343357 8426767315354786304378759)
            ·
              refine ⟨12640150973032179456568139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426767315354786304378759 12640150973032179456568139)
              ·
                refine ⟨18960226459548269184852209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640150973032179456568139 18960226459548269184852209)
                ·
                  refine ⟨14220169844661201888639157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18960226459548269184852209 14220169844661201888639157)
                  ·
                    refine ⟨1333140922936987677059921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14220169844661201888639157 1333140922936987677059921)
                    ·
                      refine ⟨999855692202740757794941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333140922936987677059921 999855692202740757794941)
                      ·
                        rfl

theorem cell23_1947212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_1947212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947212 prefixEnd_1947212 := by exact prefixLift 1947212
  have htrace : WordTrace (prefixWord ++ tailWord_1947212) baseStart_1947212 baseEnd_1947212 := by
    simpa [prefixWord, tailWord_1947212, baseEnd_1947212] using wordTrace_append hprefix tailTrace_1947212
  have hstable : (prefixWord ++ tailWord_1947212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947212).length < 2 ^ (prefixWord ++ tailWord_1947212).sum := by decide
  have hdescent : baseEnd_1947212 < baseStart_1947212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947225 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1947225 : Nat := 118140960795 + 1947225 * 2 ^ 59
def prefixEnd_1947225 : Nat := 4983230072969 + 3 ^ 40 * 1947225 * 2
def baseEnd_1947225 : Nat := 999862367451249206932381

theorem tailTrace_1947225 : CollatzResearch.WordTrace tailWord_1947225 prefixEnd_1947225 999862367451249206932381 := by
  unfold tailWord_1947225
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021130370543859398691129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47347420247029239599127419 71021130370543859398691129)
  ·
    refine ⟨53265847777907894549018347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71021130370543859398691129 53265847777907894549018347)
    ·
      refine ⟨79898771666861841823527521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53265847777907894549018347 79898771666861841823527521)
      ·
        refine ⟨59924078750146381367645641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79898771666861841823527521 59924078750146381367645641)
        ·
          refine ⟨44943059062609786025734231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59924078750146381367645641 44943059062609786025734231)
          ·
            refine ⟨67414588593914679038601347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44943059062609786025734231 67414588593914679038601347)
            ·
              refine ⟨101121882890872018557902021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67414588593914679038601347 101121882890872018557902021)
              ·
                refine ⟨18960353042038503479606629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101121882890872018557902021 18960353042038503479606629)
                ·
                  refine ⟨3555066195382219402426243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18960353042038503479606629 3555066195382219402426243)
                  ·
                    refine ⟨5332599293073329103639365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555066195382219402426243 5332599293073329103639365)
                    ·
                      refine ⟨999862367451249206932381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5332599293073329103639365 999862367451249206932381)
                      ·
                        rfl

theorem cell23_1947225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1947225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947225 prefixEnd_1947225 := by exact prefixLift 1947225
  have htrace : WordTrace (prefixWord ++ tailWord_1947225) baseStart_1947225 baseEnd_1947225 := by
    simpa [prefixWord, tailWord_1947225, baseEnd_1947225] using wordTrace_append hprefix tailTrace_1947225
  have hstable : (prefixWord ++ tailWord_1947225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947225).length < 2 ^ (prefixWord ++ tailWord_1947225).sum := by decide
  have hdescent : baseEnd_1947225 < baseStart_1947225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947242 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1947242 : Nat := 118140960795 + 1947242 * 2 ^ 59
def prefixEnd_1947242 : Nat := 4983230072969 + 3 ^ 40 * 1947242 * 2
def baseEnd_1947242 : Nat := 999871096622375640419803

theorem tailTrace_1947242 : CollatzResearch.WordTrace tailWord_1947242 prefixEnd_1947242 999871096622375640419803 := by
  unfold tailWord_1947242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755437602870567825514995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47347833607654847534706653 17755437602870567825514995)
  ·
    refine ⟨26633156404305851738272493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17755437602870567825514995 26633156404305851738272493)
    ·
      refine ⟨9987433651614694401852185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26633156404305851738272493 9987433651614694401852185)
      ·
        refine ⟨7490575238711020801389139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9987433651614694401852185 7490575238711020801389139)
        ·
          refine ⟨11235862858066531202083709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490575238711020801389139 11235862858066531202083709)
          ·
            refine ⟨4213448571774949200781391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11235862858066531202083709 4213448571774949200781391)
            ·
              refine ⟨6320172857662423801172087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213448571774949200781391 6320172857662423801172087)
              ·
                refine ⟨9480259286493635701758131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320172857662423801172087 9480259286493635701758131)
                ·
                  refine ⟨14220388929740453552637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9480259286493635701758131 14220388929740453552637197)
                  ·
                    refine ⟨5332645848652670082238949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14220388929740453552637197 5332645848652670082238949)
                    ·
                      refine ⟨999871096622375640419803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5332645848652670082238949 999871096622375640419803)
                      ·
                        rfl

theorem cell23_1947242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1947242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947242 prefixEnd_1947242 := by exact prefixLift 1947242
  have htrace : WordTrace (prefixWord ++ tailWord_1947242) baseStart_1947242 baseEnd_1947242 := by
    simpa [prefixWord, tailWord_1947242, baseEnd_1947242] using wordTrace_append hprefix tailTrace_1947242
  have hstable : (prefixWord ++ tailWord_1947242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947242).length < 2 ^ (prefixWord ++ tailWord_1947242).sum := by decide
  have hdescent : baseEnd_1947242 < baseStart_1947242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947269 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_1947269 : Nat := 118140960795 + 1947269 * 2 ^ 59
def prefixEnd_1947269 : Nat := 4983230072969 + 3 ^ 40 * 1947269 * 2
def baseEnd_1947269 : Nat := 333294986866682344927393

theorem tailTrace_1947269 : CollatzResearch.WordTrace tailWord_1947269 prefixEnd_1947269 333294986866682344927393 := by
  unfold tailWord_1947269
  simp only [CollatzResearch.WordTrace]
  refine ⟨71022735182384454913292861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47348490121589636608861907 71022735182384454913292861)
  ·
    refine ⟨26633525693394170592484823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71022735182384454913292861 26633525693394170592484823)
    ·
      refine ⟨39950288540091255888727235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26633525693394170592484823 39950288540091255888727235)
      ·
        refine ⟨59925432810136883833090853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39950288540091255888727235 59925432810136883833090853)
        ·
          refine ⟨11236018651900665718704535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59925432810136883833090853 11236018651900665718704535)
          ·
            refine ⟨16854027977850998578056803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236018651900665718704535 16854027977850998578056803)
            ·
              refine ⟨25281041966776497867085205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16854027977850998578056803 25281041966776497867085205)
              ·
                refine ⟨1185048842192648337519619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25281041966776497867085205 1185048842192648337519619)
                ·
                  refine ⟨1777573263288972506279429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185048842192648337519619 1777573263288972506279429)
                  ·
                    refine ⟨333294986866682344927393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1777573263288972506279429 333294986866682344927393)
                    ·
                      rfl

theorem cell23_1947269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_1947269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947269 prefixEnd_1947269 := by exact prefixLift 1947269
  have htrace : WordTrace (prefixWord ++ tailWord_1947269) baseStart_1947269 baseEnd_1947269 := by
    simpa [prefixWord, tailWord_1947269, baseEnd_1947269] using wordTrace_append hprefix tailTrace_1947269
  have hstable : (prefixWord ++ tailWord_1947269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947269).length < 2 ^ (prefixWord ++ tailWord_1947269).sum := by decide
  have hdescent : baseEnd_1947269 < baseStart_1947269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947312 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_1947312 : Nat := 118140960795 + 1947312 * 2 ^ 59
def prefixEnd_1947312 : Nat := 4983230072969 + 3 ^ 40 * 1947312 * 2
def baseEnd_1947312 : Nat := 333302346756063455514827

theorem tailTrace_1947312 : CollatzResearch.WordTrace tailWord_1947312 prefixEnd_1947312 333302346756063455514827 := by
  unfold tailWord_1947312
  simp only [CollatzResearch.WordTrace]
  refine ⟨35512151760614336628554095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47349535680819115504738793 35512151760614336628554095)
  ·
    refine ⟨53268227640921504942831143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35512151760614336628554095 53268227640921504942831143)
    ·
      refine ⟨79902341461382257414246715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53268227640921504942831143 79902341461382257414246715)
      ·
        refine ⟨119853512192073386121370073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79902341461382257414246715 119853512192073386121370073)
        ·
          refine ⟨89890134144055039591027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119853512192073386121370073 89890134144055039591027555)
          ·
            refine ⟨134835201216082559386541333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89890134144055039591027555 134835201216082559386541333)
            ·
              refine ⟨6320400057003869971244125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134835201216082559386541333 6320400057003869971244125)
              ·
                refine ⟨2370150021376451239216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320400057003869971244125 2370150021376451239216547)
                ·
                  refine ⟨3555225032064676858824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370150021376451239216547 3555225032064676858824821)
                  ·
                    refine ⟨333302346756063455514827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555225032064676858824821 333302346756063455514827)
                    ·
                      rfl

theorem cell23_1947312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_1947312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947312 prefixEnd_1947312 := by exact prefixLift 1947312
  have htrace : WordTrace (prefixWord ++ tailWord_1947312) baseStart_1947312 baseEnd_1947312 := by
    simpa [prefixWord, tailWord_1947312, baseEnd_1947312] using wordTrace_append hprefix tailTrace_1947312
  have hstable : (prefixWord ++ tailWord_1947312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947312).length < 2 ^ (prefixWord ++ tailWord_1947312).sum := by decide
  have hdescent : baseEnd_1947312 < baseStart_1947312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947319 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_1947319 : Nat := 118140960795 + 1947319 * 2 ^ 59
def prefixEnd_1947319 : Nat := 4983230072969 + 3 ^ 40 * 1947319 * 2
def baseEnd_1947319 : Nat := 999910634632771839156949

theorem tailTrace_1947319 : CollatzResearch.WordTrace tailWord_1947319 prefixEnd_1947319 999910634632771839156949 := by
  unfold tailWord_1947319
  simp only [CollatzResearch.WordTrace]
  refine ⟨71024558832203313452613011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47349705888135542301742007 71024558832203313452613011)
  ·
    refine ⟨106536838248304970178919517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71024558832203313452613011 106536838248304970178919517)
    ·
      refine ⟨39951314343114363817094819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106536838248304970178919517 39951314343114363817094819)
      ·
        refine ⟨59926971514671545725642229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39951314343114363817094819 59926971514671545725642229)
        ·
          refine ⟨5618153579500457411778959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59926971514671545725642229 5618153579500457411778959)
          ·
            refine ⟨8427230369250686117668439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618153579500457411778959 8427230369250686117668439)
            ·
              refine ⟨12640845553876029176502659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427230369250686117668439 12640845553876029176502659)
              ·
                refine ⟨18961268330814043764753989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640845553876029176502659 18961268330814043764753989)
                ·
                  refine ⟨3555237812027633205891373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18961268330814043764753989 3555237812027633205891373)
                  ·
                    refine ⟨1333214179510362452209265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555237812027633205891373 1333214179510362452209265)
                    ·
                      refine ⟨999910634632771839156949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333214179510362452209265 999910634632771839156949)
                      ·
                        rfl

theorem cell23_1947319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_1947319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947319 prefixEnd_1947319 := by exact prefixLift 1947319
  have htrace : WordTrace (prefixWord ++ tailWord_1947319) baseStart_1947319 baseEnd_1947319 := by
    simpa [prefixWord, tailWord_1947319, baseEnd_1947319] using wordTrace_append hprefix tailTrace_1947319
  have hstable : (prefixWord ++ tailWord_1947319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947319).length < 2 ^ (prefixWord ++ tailWord_1947319).sum := by decide
  have hdescent : baseEnd_1947319 < baseStart_1947319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947326 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1947326 : Nat := 118140960795 + 1947326 * 2 ^ 59
def prefixEnd_1947326 : Nat := 4983230072969 + 3 ^ 40 * 1947326 * 2
def baseEnd_1947326 : Nat := 999914228997353311769417

theorem tailTrace_1947326 : CollatzResearch.WordTrace tailWord_1947326 prefixEnd_1947326 999914228997353311769417 := by
  unfold tailWord_1947326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878101767897244206014729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47349876095451969098745221 8878101767897244206014729)
  ·
    refine ⟨6658576325922933154511047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8878101767897244206014729 6658576325922933154511047)
    ·
      refine ⟨9987864488884399731766571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658576325922933154511047 9987864488884399731766571)
      ·
        refine ⟨14981796733326599597649857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987864488884399731766571 14981796733326599597649857)
        ·
          refine ⟨11236347549994949698237393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14981796733326599597649857 11236347549994949698237393)
          ·
            refine ⟨8427260662496212273678045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236347549994949698237393 8427260662496212273678045)
            ·
              refine ⟨3160222748436079602629267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8427260662496212273678045 3160222748436079602629267)
              ·
                refine ⟨4740334122654119403943901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160222748436079602629267 4740334122654119403943901)
                ·
                  refine ⟨1777625295995294776478963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4740334122654119403943901 1777625295995294776478963)
                  ·
                    refine ⟨2666437943992942164718445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1777625295995294776478963 2666437943992942164718445)
                    ·
                      refine ⟨999914228997353311769417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666437943992942164718445 999914228997353311769417)
                      ·
                        rfl

theorem cell23_1947326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1947326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947326 prefixEnd_1947326 := by exact prefixLift 1947326
  have htrace : WordTrace (prefixWord ++ tailWord_1947326) baseStart_1947326 baseEnd_1947326 := by
    simpa [prefixWord, tailWord_1947326, baseEnd_1947326] using wordTrace_append hprefix tailTrace_1947326
  have hstable : (prefixWord ++ tailWord_1947326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947326).length < 2 ^ (prefixWord ++ tailWord_1947326).sum := by decide
  have hdescent : baseEnd_1947326 < baseStart_1947326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947342 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1947342 : Nat := 118140960795 + 1947342 * 2 ^ 59
def prefixEnd_1947342 : Nat := 4983230072969 + 3 ^ 40 * 1947342 * 2
def baseEnd_1947342 : Nat := 333307481562608416389781

theorem tailTrace_1947342 : CollatzResearch.WordTrace tailWord_1947342 prefixEnd_1947342 333307481562608416389781 := by
  unfold tailWord_1947342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878174713889998547587535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47350265140746658920466853 8878174713889998547587535)
  ·
    refine ⟨13317262070834997821381303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878174713889998547587535 13317262070834997821381303)
    ·
      refine ⟨19975893106252496732071955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13317262070834997821381303 19975893106252496732071955)
      ·
        refine ⟨29963839659378745098107933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19975893106252496732071955 29963839659378745098107933)
        ·
          refine ⟨11236439872267029411790475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29963839659378745098107933 11236439872267029411790475)
          ·
            refine ⟨16854659808400544117685713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236439872267029411790475 16854659808400544117685713)
            ·
              refine ⟨12640994856300408088264285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16854659808400544117685713 12640994856300408088264285)
              ·
                refine ⟨4740373071112653033099107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12640994856300408088264285 4740373071112653033099107)
                ·
                  refine ⟨7110559606668979549648661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740373071112653033099107 7110559606668979549648661)
                  ·
                    refine ⟨333307481562608416389781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7110559606668979549648661 333307481562608416389781)
                    ·
                      rfl

theorem cell23_1947342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1947342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947342 prefixEnd_1947342 := by exact prefixLift 1947342
  have htrace : WordTrace (prefixWord ++ tailWord_1947342) baseStart_1947342 baseEnd_1947342 := by
    simpa [prefixWord, tailWord_1947342, baseEnd_1947342] using wordTrace_append hprefix tailTrace_1947342
  have hstable : (prefixWord ++ tailWord_1947342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947342).length < 2 ^ (prefixWord ++ tailWord_1947342).sum := by decide
  have hdescent : baseEnd_1947342 < baseStart_1947342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947346 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1947346 : Nat := 118140960795 + 1947346 * 2 ^ 59
def prefixEnd_1947346 : Nat := 4983230072969 + 3 ^ 40 * 1947346 * 2
def baseEnd_1947346 : Nat := 333308166203481077839775

theorem tailTrace_1947346 : CollatzResearch.WordTrace tailWord_1947346 prefixEnd_1947346 333308166203481077839775 := by
  unfold tailWord_1947346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756385900776374265961473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47350362402070331375897261 17756385900776374265961473)
  ·
    refine ⟨13317289425582280699471105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17756385900776374265961473 13317289425582280699471105)
    ·
      refine ⟨9987967069186710524603329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13317289425582280699471105 9987967069186710524603329)
      ·
        refine ⟨7490975301890032893452497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9987967069186710524603329 7490975301890032893452497)
        ·
          refine ⟨5618231476417524670089373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490975301890032893452497 5618231476417524670089373)
          ·
            refine ⟨2106836803656571751283515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5618231476417524670089373 2106836803656571751283515)
            ·
              refine ⟨3160255205484857626925273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106836803656571751283515 3160255205484857626925273)
              ·
                refine ⟨2370191404113643220193955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160255205484857626925273 2370191404113643220193955)
                ·
                  refine ⟨3555287106170464830290933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370191404113643220193955 3555287106170464830290933)
                  ·
                    refine ⟨333308166203481077839775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555287106170464830290933 333308166203481077839775)
                    ·
                      rfl

theorem cell23_1947346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1947346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947346 prefixEnd_1947346 := by exact prefixLift 1947346
  have htrace : WordTrace (prefixWord ++ tailWord_1947346) baseStart_1947346 baseEnd_1947346 := by
    simpa [prefixWord, tailWord_1947346, baseEnd_1947346] using wordTrace_append hprefix tailTrace_1947346
  have hstable : (prefixWord ++ tailWord_1947346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947346).length < 2 ^ (prefixWord ++ tailWord_1947346).sum := by decide
  have hdescent : baseEnd_1947346 < baseStart_1947346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947499 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 5, 2]
def baseStart_1947499 : Nat := 118140960795 + 1947499 * 2 ^ 59
def prefixEnd_1947499 : Nat := 4983230072969 + 3 ^ 40 * 1947499 * 2
def baseEnd_1947499 : Nat := 1000003061150581134906121

theorem tailTrace_1947499 : CollatzResearch.WordTrace tailWord_1947499 prefixEnd_1947499 1000003061150581134906121 := by
  unfold tailWord_1947499
  simp only [CollatzResearch.WordTrace]
  refine ⟨71031123971551204194165551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47354082647700802796110367 71031123971551204194165551)
  ·
    refine ⟨106546685957326806291248327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71031123971551204194165551 106546685957326806291248327)
    ·
      refine ⟨159820028935990209436872491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106546685957326806291248327 159820028935990209436872491)
      ·
        refine ⟨239730043403985314155308737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159820028935990209436872491 239730043403985314155308737)
        ·
          refine ⟨179797532552988985616481553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239730043403985314155308737 179797532552988985616481553)
          ·
            refine ⟨134848149414741739212361165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179797532552988985616481553 134848149414741739212361165)
            ·
              refine ⟨50568056030528152204635437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134848149414741739212361165 50568056030528152204635437)
              ·
                refine ⟨18963021011448057076738289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50568056030528152204635437 18963021011448057076738289)
                ·
                  refine ⟨14222265758586042807553717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18963021011448057076738289 14222265758586042807553717)
                  ·
                    refine ⟨1333337414867441513208161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14222265758586042807553717 1333337414867441513208161)
                    ·
                      refine ⟨1000003061150581134906121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333337414867441513208161 1000003061150581134906121)
                      ·
                        rfl

theorem cell23_1947499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5, 2].length) (baseStart_1947499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947499 prefixEnd_1947499 := by exact prefixLift 1947499
  have htrace : WordTrace (prefixWord ++ tailWord_1947499) baseStart_1947499 baseEnd_1947499 := by
    simpa [prefixWord, tailWord_1947499, baseEnd_1947499] using wordTrace_append hprefix tailTrace_1947499
  have hstable : (prefixWord ++ tailWord_1947499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947499).length < 2 ^ (prefixWord ++ tailWord_1947499).sum := by decide
  have hdescent : baseEnd_1947499 < baseStart_1947499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947509 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1947509 : Nat := 118140960795 + 1947509 * 2 ^ 59
def prefixEnd_1947509 : Nat := 4983230072969 + 3 ^ 40 * 1947509 * 2
def baseEnd_1947509 : Nat := 333336065319042031927025

theorem tailTrace_1947509 : CollatzResearch.WordTrace tailWord_1947509 prefixEnd_1947509 333336065319042031927025 := by
  unfold tailWord_1947509
  simp only [CollatzResearch.WordTrace]
  refine ⟨71031488701514975902029581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47354325801009983934686387 71031488701514975902029581)
  ·
    refine ⟨26636808263068115963261093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71031488701514975902029581 26636808263068115963261093)
    ·
      refine ⟨4994401549325271743111455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26636808263068115963261093 4994401549325271743111455)
      ·
        refine ⟨7491602323987907614667183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994401549325271743111455 7491602323987907614667183)
        ·
          refine ⟨11237403485981861422000775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491602323987907614667183 11237403485981861422000775)
          ·
            refine ⟨16856105228972792133001163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237403485981861422000775 16856105228972792133001163)
            ·
              refine ⟨25284157843459188199501745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16856105228972792133001163 25284157843459188199501745)
              ·
                refine ⟨18963118382594391149626309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25284157843459188199501745 18963118382594391149626309)
                ·
                  refine ⟨3555584696736448340554933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18963118382594391149626309 3555584696736448340554933)
                  ·
                    refine ⟨333336065319042031927025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555584696736448340554933 333336065319042031927025)
                    ·
                      rfl

theorem cell23_1947509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1947509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947509 prefixEnd_1947509 := by exact prefixLift 1947509
  have htrace : WordTrace (prefixWord ++ tailWord_1947509) baseStart_1947509 baseEnd_1947509 := by
    simpa [prefixWord, tailWord_1947509, baseEnd_1947509] using wordTrace_append hprefix tailTrace_1947509
  have hstable : (prefixWord ++ tailWord_1947509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947509).length < 2 ^ (prefixWord ++ tailWord_1947509).sum := by decide
  have hdescent : baseEnd_1947509 < baseStart_1947509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947546 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1947546 : Nat := 118140960795 + 1947546 * 2 ^ 59
def prefixEnd_1947546 : Nat := 4983230072969 + 3 ^ 40 * 1947546 * 2
def baseEnd_1947546 : Nat := 1000027194741342451018405

theorem tailTrace_1947546 : CollatzResearch.WordTrace tailWord_1947546 prefixEnd_1947546 1000027194741342451018405 := by
  unfold tailWord_1947546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17758209550595232805281623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47355225468253954147417661 17758209550595232805281623)
  ·
    refine ⟨26637314325892849207922435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17758209550595232805281623 26637314325892849207922435)
    ·
      refine ⟨39955971488839273811883653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26637314325892849207922435 39955971488839273811883653)
      ·
        refine ⟨7491744654157363839728185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39955971488839273811883653 7491744654157363839728185)
        ·
          refine ⟨5618808490618022879796139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7491744654157363839728185 5618808490618022879796139)
          ·
            refine ⟨8428212735927034319694209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618808490618022879796139 8428212735927034319694209)
            ·
              refine ⟨6321159551945275739770657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428212735927034319694209 6321159551945275739770657)
              ·
                refine ⟨4740869663958956804827993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321159551945275739770657 4740869663958956804827993)
                ·
                  refine ⟨3555652247969217603620995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740869663958956804827993 3555652247969217603620995)
                  ·
                    refine ⟨5333478371953826405431493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555652247969217603620995 5333478371953826405431493)
                    ·
                      refine ⟨1000027194741342451018405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5333478371953826405431493 1000027194741342451018405)
                      ·
                        rfl

theorem cell23_1947546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1947546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947546 prefixEnd_1947546 := by exact prefixLift 1947546
  have htrace : WordTrace (prefixWord ++ tailWord_1947546) baseStart_1947546 baseEnd_1947546 := by
    simpa [prefixWord, tailWord_1947546, baseEnd_1947546] using wordTrace_append hprefix tailTrace_1947546
  have hstable : (prefixWord ++ tailWord_1947546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947546).length < 2 ^ (prefixWord ++ tailWord_1947546).sum := by decide
  have hdescent : baseEnd_1947546 < baseStart_1947546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947580 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1947580 : Nat := 118140960795 + 1947580 * 2 ^ 59
def prefixEnd_1947580 : Nat := 4983230072969 + 3 ^ 40 * 1947580 * 2
def baseEnd_1947580 : Nat := 1000044653083595317993249

theorem tailTrace_1947580 : CollatzResearch.WordTrace tailWord_1947580 prefixEnd_1947580 1000044653083595317993249 := by
  unfold tailWord_1947580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35517039142128877513932097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47356052189505170018576129 35517039142128877513932097)
  ·
    refine ⟨26637779356596658135449073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35517039142128877513932097 26637779356596658135449073)
    ·
      refine ⟨19978334517447493601586805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26637779356596658135449073 19978334517447493601586805)
      ·
        refine ⟨1872968861010702525148763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19978334517447493601586805 1872968861010702525148763)
        ·
          refine ⟨2809453291516053787723145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872968861010702525148763 2809453291516053787723145)
          ·
            refine ⟨2107089968637040340792359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809453291516053787723145 2107089968637040340792359)
            ·
              refine ⟨3160634952955560511188539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107089968637040340792359 3160634952955560511188539)
              ·
                refine ⟨4740952429433340766782809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160634952955560511188539 4740952429433340766782809)
                ·
                  refine ⟨3555714322075005575087107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740952429433340766782809 3555714322075005575087107)
                  ·
                    refine ⟨5333571483112508362630661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555714322075005575087107 5333571483112508362630661)
                    ·
                      refine ⟨1000044653083595317993249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5333571483112508362630661 1000044653083595317993249)
                      ·
                        rfl

theorem cell23_1947580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1947580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947580 prefixEnd_1947580 := by exact prefixLift 1947580
  have htrace : WordTrace (prefixWord ++ tailWord_1947580) baseStart_1947580 baseEnd_1947580 := by
    simpa [prefixWord, tailWord_1947580, baseEnd_1947580] using wordTrace_append hprefix tailTrace_1947580
  have hstable : (prefixWord ++ tailWord_1947580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947580).length < 2 ^ (prefixWord ++ tailWord_1947580).sum := by decide
  have hdescent : baseEnd_1947580 < baseStart_1947580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947633 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_1947633 : Nat := 118140960795 + 1947633 * 2 ^ 59
def prefixEnd_1947633 : Nat := 4983230072969 + 3 ^ 40 * 1947633 * 2
def baseEnd_1947633 : Nat := 333357289186094536876835

theorem tailTrace_1947633 : CollatzResearch.WordTrace tailWord_1947633 prefixEnd_1947633 333357289186094536876835 := by
  unfold tailWord_1947633
  simp only [CollatzResearch.WordTrace]
  refine ⟨71036011353065745079543553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47357340902043830053029035 71036011353065745079543553)
  ·
    refine ⟨53277008514799308809657665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71036011353065745079543553 53277008514799308809657665)
    ·
      refine ⟨39957756386099481607243249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53277008514799308809657665 39957756386099481607243249)
      ·
        refine ⟨29968317289574611205432437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39957756386099481607243249 29968317289574611205432437)
        ·
          refine ⟨2809529745897619800509291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29968317289574611205432437 2809529745897619800509291)
          ·
            refine ⟨4214294618846429700763937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809529745897619800509291 4214294618846429700763937)
            ·
              refine ⟨3160720964134822275572953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214294618846429700763937 3160720964134822275572953)
              ·
                refine ⟨2370540723101116706679715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160720964134822275572953 2370540723101116706679715)
                ·
                  refine ⟨3555811084651675060019573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370540723101116706679715 3555811084651675060019573)
                  ·
                    refine ⟨333357289186094536876835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555811084651675060019573 333357289186094536876835)
                    ·
                      rfl

theorem cell23_1947633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_1947633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947633 prefixEnd_1947633 := by exact prefixLift 1947633
  have htrace : WordTrace (prefixWord ++ tailWord_1947633) baseStart_1947633 baseEnd_1947633 := by
    simpa [prefixWord, tailWord_1947633, baseEnd_1947633] using wordTrace_append hprefix tailTrace_1947633
  have hstable : (prefixWord ++ tailWord_1947633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947633).length < 2 ^ (prefixWord ++ tailWord_1947633).sum := by decide
  have hdescent : baseEnd_1947633 < baseStart_1947633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1947639 : Nat := 118140960795 + 1947639 * 2 ^ 59
def prefixEnd_1947639 : Nat := 4983230072969 + 3 ^ 40 * 1947639 * 2
def baseEnd_1947639 : Nat := 1000074948442210587155477

theorem tailTrace_1947639 : CollatzResearch.WordTrace tailWord_1947639 prefixEnd_1947639 1000074948442210587155477 := by
  unfold tailWord_1947639
  simp only [CollatzResearch.WordTrace]
  refine ⟨71036230191044008104261971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47357486794029338736174647 71036230191044008104261971)
  ·
    refine ⟨106554345286566012156392957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71036230191044008104261971 106554345286566012156392957)
    ·
      refine ⟨39957879482462254558647359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106554345286566012156392957 39957879482462254558647359)
      ·
        refine ⟨59936819223693381837971039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39957879482462254558647359 59936819223693381837971039)
        ·
          refine ⟨89905228835540072756956559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59936819223693381837971039 89905228835540072756956559)
          ·
            refine ⟨134857843253310109135434839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89905228835540072756956559 134857843253310109135434839)
            ·
              refine ⟨202286764879965163703152259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134857843253310109135434839 202286764879965163703152259)
              ·
                refine ⟨303430147319947745554728389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202286764879965163703152259 303430147319947745554728389)
                ·
                  refine ⟨56893152622490202291511573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303430147319947745554728389 56893152622490202291511573)
                  ·
                    refine ⟨2666866529179228232414605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56893152622490202291511573 2666866529179228232414605)
                    ·
                      refine ⟨1000074948442210587155477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666866529179228232414605 1000074948442210587155477)
                      ·
                        rfl

theorem cell23_1947639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1947639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947639 prefixEnd_1947639 := by exact prefixLift 1947639
  have htrace : WordTrace (prefixWord ++ tailWord_1947639) baseStart_1947639 baseEnd_1947639 := by
    simpa [prefixWord, tailWord_1947639, baseEnd_1947639] using wordTrace_append hprefix tailTrace_1947639
  have hstable : (prefixWord ++ tailWord_1947639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947639).length < 2 ^ (prefixWord ++ tailWord_1947639).sum := by decide
  have hdescent : baseEnd_1947639 < baseStart_1947639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947656 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1947656 : Nat := 118140960795 + 1947656 * 2 ^ 59
def prefixEnd_1947656 : Nat := 4983230072969 + 3 ^ 40 * 1947656 * 2
def baseEnd_1947656 : Nat := 1000083677613337020642899

theorem tailTrace_1947656 : CollatzResearch.WordTrace tailWord_1947656 prefixEnd_1947656 1000083677613337020642899 := by
  unfold tailWord_1947656
  simp only [CollatzResearch.WordTrace]
  refine ⟨35518425115991210003815411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47357900154654946671753881 35518425115991210003815411)
  ·
    refine ⟨53277637673986815005723117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35518425115991210003815411 53277637673986815005723117)
    ·
      refine ⟨19979114127745055627146169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53277637673986815005723117 19979114127745055627146169)
      ·
        refine ⟨14984335595808791720359627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19979114127745055627146169 14984335595808791720359627)
        ·
          refine ⟨22476503393713187580539441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984335595808791720359627 22476503393713187580539441)
          ·
            refine ⟨16857377545284890685404581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22476503393713187580539441 16857377545284890685404581)
            ·
              refine ⟨3160758289740917003513359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16857377545284890685404581 3160758289740917003513359)
              ·
                refine ⟨4741137434611375505270039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160758289740917003513359 4741137434611375505270039)
                ·
                  refine ⟨7111706151917063257905059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741137434611375505270039 7111706151917063257905059)
                  ·
                    refine ⟨10667559227875594886857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7111706151917063257905059 10667559227875594886857589)
                    ·
                      refine ⟨1000083677613337020642899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10667559227875594886857589 1000083677613337020642899)
                      ·
                        rfl

theorem cell23_1947656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1947656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947656 prefixEnd_1947656 := by exact prefixLift 1947656
  have htrace : WordTrace (prefixWord ++ tailWord_1947656) baseStart_1947656 baseEnd_1947656 := by
    simpa [prefixWord, tailWord_1947656, baseEnd_1947656] using wordTrace_append hprefix tailTrace_1947656
  have hstable : (prefixWord ++ tailWord_1947656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947656).length < 2 ^ (prefixWord ++ tailWord_1947656).sum := by decide
  have hdescent : baseEnd_1947656 < baseStart_1947656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947676 : List Nat := [2, 2, 3, 1, 3, 2, 2, 8]
def baseStart_1947676 : Nat := 118140960795 + 1947676 * 2 ^ 59
def prefixEnd_1947676 : Nat := 4983230072969 + 3 ^ 40 * 1947676 * 2
def baseEnd_1947676 : Nat := 37040516563941738607141

theorem tailTrace_1947676 : CollatzResearch.WordTrace tailWord_1947676 prefixEnd_1947676 37040516563941738607141 := by
  unfold tailWord_1947676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35518789845954981711679441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47358386461273308948905921 35518789845954981711679441)
  ·
    refine ⟨26639092384466236283759581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35518789845954981711679441 26639092384466236283759581)
    ·
      refine ⟨9989659644174838606409843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26639092384466236283759581 9989659644174838606409843)
      ·
        refine ⟨14984489466262257909614765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9989659644174838606409843 14984489466262257909614765)
        ·
          refine ⟨5619183549848346716105537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14984489466262257909614765 5619183549848346716105537)
          ·
            refine ⟨4214387662386260037079153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5619183549848346716105537 4214387662386260037079153)
            ·
              refine ⟨3160790746789695027809365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214387662386260037079153 3160790746789695027809365)
              ·
                refine ⟨37040516563941738607141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3160790746789695027809365 37040516563941738607141)
                ·
                  rfl

theorem cell23_1947676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 8].length) (baseStart_1947676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947676 prefixEnd_1947676 := by exact prefixLift 1947676
  have htrace : WordTrace (prefixWord ++ tailWord_1947676) baseStart_1947676 baseEnd_1947676 := by
    simpa [prefixWord, tailWord_1947676, baseEnd_1947676] using wordTrace_append hprefix tailTrace_1947676
  have hstable : (prefixWord ++ tailWord_1947676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947676).length < 2 ^ (prefixWord ++ tailWord_1947676).sum := by decide
  have hdescent : baseEnd_1947676 < baseStart_1947676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947679 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1947679 : Nat := 118140960795 + 1947679 * 2 ^ 59
def prefixEnd_1947679 : Nat := 4983230072969 + 3 ^ 40 * 1947679 * 2
def baseEnd_1947679 : Nat := 1000095487668390430655293

theorem tailTrace_1947679 : CollatzResearch.WordTrace tailWord_1947679 prefixEnd_1947679 1000095487668390430655293 := by
  unfold tailWord_1947679
  simp only [CollatzResearch.WordTrace]
  refine ⟨71037689110899094935718091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358459407266063290478727 71037689110899094935718091)
  ·
    refine ⟨106556533666348642403577137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71037689110899094935718091 106556533666348642403577137)
    ·
      refine ⟨79917400249761481802682853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106556533666348642403577137 79917400249761481802682853)
      ·
        refine ⟨14984512546830277838003035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79917400249761481802682853 14984512546830277838003035)
        ·
          refine ⟨22476768820245416757004553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984512546830277838003035 22476768820245416757004553)
          ·
            refine ⟨16857576615184062567753415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22476768820245416757004553 16857576615184062567753415)
            ·
              refine ⟨25286364922776093851630123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16857576615184062567753415 25286364922776093851630123)
              ·
                refine ⟨37929547384164140777445185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25286364922776093851630123 37929547384164140777445185)
                ·
                  refine ⟨28447160538123105583083889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37929547384164140777445185 28447160538123105583083889)
                  ·
                    refine ⟨21335370403592329187312917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28447160538123105583083889 21335370403592329187312917)
                    ·
                      refine ⟨1000095487668390430655293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21335370403592329187312917 1000095487668390430655293)
                      ·
                        rfl

theorem cell23_1947679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1947679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947679 prefixEnd_1947679 := by exact prefixLift 1947679
  have htrace : WordTrace (prefixWord ++ tailWord_1947679) baseStart_1947679 baseEnd_1947679 := by
    simpa [prefixWord, tailWord_1947679, baseEnd_1947679] using wordTrace_append hprefix tailTrace_1947679
  have hstable : (prefixWord ++ tailWord_1947679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947679).length < 2 ^ (prefixWord ++ tailWord_1947679).sum := by decide
  have hdescent : baseEnd_1947679 < baseStart_1947679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947687 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1947687 : Nat := 118140960795 + 1947687 * 2 ^ 59
def prefixEnd_1947687 : Nat := 4983230072969 + 3 ^ 40 * 1947687 * 2
def baseEnd_1947687 : Nat := 1000099595513626399355257

theorem tailTrace_1947687 : CollatzResearch.WordTrace tailWord_1947687 prefixEnd_1947687 1000099595513626399355257 := by
  unfold tailWord_1947687
  simp only [CollatzResearch.WordTrace]
  refine ⟨71037980894870112302009315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358653929913408201339543 71037980894870112302009315)
  ·
    refine ⟨106556971342305168453013973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71037980894870112302009315 106556971342305168453013973)
    ·
      refine ⟨2497429015835277385617515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106556971342305168453013973 2497429015835277385617515)
      ·
        refine ⟨3746143523752916078426273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497429015835277385617515 3746143523752916078426273)
        ·
          refine ⟨2809607642814687058819705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746143523752916078426273 2809607642814687058819705)
          ·
            refine ⟨2107205732111015294114779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809607642814687058819705 2107205732111015294114779)
            ·
              refine ⟨3160808598166522941172169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107205732111015294114779 3160808598166522941172169)
              ·
                refine ⟨2370606448624892205879127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160808598166522941172169 2370606448624892205879127)
                ·
                  refine ⟨3555909672937338308818691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370606448624892205879127 3555909672937338308818691)
                  ·
                    refine ⟨5333864509406007463228037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3555909672937338308818691 5333864509406007463228037)
                    ·
                      refine ⟨1000099595513626399355257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5333864509406007463228037 1000099595513626399355257)
                      ·
                        rfl

theorem cell23_1947687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1947687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947687 prefixEnd_1947687 := by exact prefixLift 1947687
  have htrace : WordTrace (prefixWord ++ tailWord_1947687) baseStart_1947687 baseEnd_1947687 := by
    simpa [prefixWord, tailWord_1947687, baseEnd_1947687] using wordTrace_append hprefix tailTrace_1947687
  have hstable : (prefixWord ++ tailWord_1947687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947687).length < 2 ^ (prefixWord ++ tailWord_1947687).sum := by decide
  have hdescent : baseEnd_1947687 < baseStart_1947687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947690 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1947690 : Nat := 118140960795 + 1947690 * 2 ^ 59
def prefixEnd_1947690 : Nat := 4983230072969 + 3 ^ 40 * 1947690 * 2
def baseEnd_1947690 : Nat := 1000101135955589887617743

theorem tailTrace_1947690 : CollatzResearch.WordTrace tailWord_1947690 prefixEnd_1947690 1000101135955589887617743 := by
  unfold tailWord_1947690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17759522578464810953592131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47358726875906162542912349 17759522578464810953592131)
  ·
    refine ⟨26639283867697216430388197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17759522578464810953592131 26639283867697216430388197)
    ·
      refine ⟨4994865725193228080697787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26639283867697216430388197 4994865725193228080697787)
      ·
        refine ⟨7492298587789842121046681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994865725193228080697787 7492298587789842121046681)
        ·
          refine ⟨5619223940842381590785011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7492298587789842121046681 5619223940842381590785011)
          ·
            refine ⟨8428835911263572386177517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619223940842381590785011 8428835911263572386177517)
            ·
              refine ⟨3160813466723839644816569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8428835911263572386177517 3160813466723839644816569)
              ·
                refine ⟨2370610100042879733612427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160813466723839644816569 2370610100042879733612427)
                ·
                  refine ⟨3555915150064319600418641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370610100042879733612427 3555915150064319600418641)
                  ·
                    refine ⟨2666936362548239700313981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3555915150064319600418641 2666936362548239700313981)
                    ·
                      refine ⟨1000101135955589887617743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2666936362548239700313981 1000101135955589887617743)
                      ·
                        rfl

theorem cell23_1947690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1947690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947690 prefixEnd_1947690 := by exact prefixLift 1947690
  have htrace : WordTrace (prefixWord ++ tailWord_1947690) baseStart_1947690 baseEnd_1947690 := by
    simpa [prefixWord, tailWord_1947690, baseEnd_1947690] using wordTrace_append hprefix tailTrace_1947690
  have hstable : (prefixWord ++ tailWord_1947690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947690).length < 2 ^ (prefixWord ++ tailWord_1947690).sum := by decide
  have hdescent : baseEnd_1947690 < baseStart_1947690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947699 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1947699 : Nat := 118140960795 + 1947699 * 2 ^ 59
def prefixEnd_1947699 : Nat := 4983230072969 + 3 ^ 40 * 1947699 * 2
def baseEnd_1947699 : Nat := 1000105757281480352405201

theorem tailTrace_1947699 : CollatzResearch.WordTrace tailWord_1947699 prefixEnd_1947699 1000105757281480352405201 := by
  unfold tailWord_1947699
  simp only [CollatzResearch.WordTrace]
  refine ⟨71038418570826638351446151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358945713884425567630767 71038418570826638351446151)
  ·
    refine ⟨106557627856239957527169227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71038418570826638351446151 106557627856239957527169227)
    ·
      refine ⟨159836441784359936290753841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106557627856239957527169227 159836441784359936290753841)
      ·
        refine ⟨119877331338269952218065381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159836441784359936290753841 119877331338269952218065381)
        ·
          refine ⟨22476999625925616040887259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119877331338269952218065381 22476999625925616040887259)
          ·
            refine ⟨33715499438888424061330889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22476999625925616040887259 33715499438888424061330889)
            ·
              refine ⟨25286624579166318045998167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33715499438888424061330889 25286624579166318045998167)
              ·
                refine ⟨37929936868749477068997251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25286624579166318045998167 37929936868749477068997251)
                ·
                  refine ⟨56894905303124215603495877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37929936868749477068997251 56894905303124215603495877)
                  ·
                    refine ⟨10667794744335790425655477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56894905303124215603495877 10667794744335790425655477)
                    ·
                      refine ⟨1000105757281480352405201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10667794744335790425655477 1000105757281480352405201)
                      ·
                        rfl

theorem cell23_1947699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1947699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947699 prefixEnd_1947699 := by exact prefixLift 1947699
  have htrace : WordTrace (prefixWord ++ tailWord_1947699) baseStart_1947699 baseEnd_1947699 := by
    simpa [prefixWord, tailWord_1947699, baseEnd_1947699] using wordTrace_append hprefix tailTrace_1947699
  have hstable : (prefixWord ++ tailWord_1947699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947699).length < 2 ^ (prefixWord ++ tailWord_1947699).sum := by decide
  have hdescent : baseEnd_1947699 < baseStart_1947699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947700 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1947700 : Nat := 118140960795 + 1947700 * 2 ^ 59
def prefixEnd_1947700 : Nat := 4983230072969 + 3 ^ 40 * 1947700 * 2
def baseEnd_1947700 : Nat := 1000106270762134848492697

theorem tailTrace_1947700 : CollatzResearch.WordTrace tailWord_1947700 prefixEnd_1947700 1000106270762134848492697 := by
  unfold tailWord_1947700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519227521911507761116277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47358970029215343681488369 35519227521911507761116277)
  ·
    refine ⟨3329927580179203852604651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35519227521911507761116277 3329927580179203852604651)
    ·
      refine ⟨4994891370268805778906977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329927580179203852604651 4994891370268805778906977)
      ·
        refine ⟨3746168527701604334180233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4994891370268805778906977 3746168527701604334180233)
        ·
          refine ⟨2809626395776203250635175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746168527701604334180233 2809626395776203250635175)
          ·
            refine ⟨4214439593664304875952763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809626395776203250635175 4214439593664304875952763)
            ·
              refine ⟨6321659390496457313929145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214439593664304875952763 6321659390496457313929145)
              ·
                refine ⟨4741244542872342985446859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321659390496457313929145 4741244542872342985446859)
                ·
                  refine ⟨7111866814308514478170289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741244542872342985446859 7111866814308514478170289)
                  ·
                    refine ⟨5333900110731385858627717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7111866814308514478170289 5333900110731385858627717)
                    ·
                      refine ⟨1000106270762134848492697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5333900110731385858627717 1000106270762134848492697)
                      ·
                        rfl

theorem cell23_1947700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1947700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947700 prefixEnd_1947700 := by exact prefixLift 1947700
  have htrace : WordTrace (prefixWord ++ tailWord_1947700) baseStart_1947700 baseEnd_1947700 := by
    simpa [prefixWord, tailWord_1947700, baseEnd_1947700] using wordTrace_append hprefix tailTrace_1947700
  have hstable : (prefixWord ++ tailWord_1947700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947700).length < 2 ^ (prefixWord ++ tailWord_1947700).sum := by decide
  have hdescent : baseEnd_1947700 < baseStart_1947700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947726 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1947726 : Nat := 118140960795 + 1947726 * 2 ^ 59
def prefixEnd_1947726 : Nat := 4983230072969 + 3 ^ 40 * 1947726 * 2
def baseEnd_1947726 : Nat := 1000119621259151746767577

theorem tailTrace_1947726 : CollatzResearch.WordTrace tailWord_1947726 prefixEnd_1947726 1000119621259151746767577 := by
  unfold tailWord_1947726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879925417716102745334879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47359602227819214641786021 8879925417716102745334879)
  ·
    refine ⟨13319888126574154118002319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8879925417716102745334879 13319888126574154118002319)
    ·
      refine ⟨19979832189861231177003479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13319888126574154118002319 19979832189861231177003479)
      ·
        refine ⟨29969748284791846765505219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19979832189861231177003479 29969748284791846765505219)
        ·
          refine ⟨44954622427187770148257829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29969748284791846765505219 44954622427187770148257829)
          ·
            refine ⟨8428991705097706902798343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44954622427187770148257829 8428991705097706902798343)
            ·
              refine ⟨12643487557646560354197515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428991705097706902798343 12643487557646560354197515)
              ·
                refine ⟨18965231336469840531296273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12643487557646560354197515 18965231336469840531296273)
                ·
                  refine ⟨14223923502352380398472205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18965231336469840531296273 14223923502352380398472205)
                  ·
                    refine ⟨5333971313382142649427077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14223923502352380398472205 5333971313382142649427077)
                    ·
                      refine ⟨1000119621259151746767577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5333971313382142649427077 1000119621259151746767577)
                      ·
                        rfl

theorem cell23_1947726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1947726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947726 prefixEnd_1947726 := by exact prefixLift 1947726
  have htrace : WordTrace (prefixWord ++ tailWord_1947726) baseStart_1947726 baseEnd_1947726 := by
    simpa [prefixWord, tailWord_1947726, baseEnd_1947726] using wordTrace_append hprefix tailTrace_1947726
  have hstable : (prefixWord ++ tailWord_1947726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947726).length < 2 ^ (prefixWord ++ tailWord_1947726).sum := by decide
  have hdescent : baseEnd_1947726 < baseStart_1947726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947736 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1947736 : Nat := 118140960795 + 1947736 * 2 ^ 59
def prefixEnd_1947736 : Nat := 4983230072969 + 3 ^ 40 * 1947736 * 2
def baseEnd_1947736 : Nat := 333374918688565569214177

theorem tailTrace_1947736 : CollatzResearch.WordTrace tailWord_1947736 prefixEnd_1947736 333374918688565569214177 := by
  unfold tailWord_1947736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519884035846296835271531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47359845381128395780362041 35519884035846296835271531)
  ·
    refine ⟨53279826053769445252907297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519884035846296835271531 53279826053769445252907297)
    ·
      refine ⟨39959869540327083939680473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53279826053769445252907297 39959869540327083939680473)
      ·
        refine ⟨29969902155245312954760355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39959869540327083939680473 29969902155245312954760355)
        ·
          refine ⟨44954853232867969432140533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29969902155245312954760355 44954853232867969432140533)
          ·
            refine ⟨4214517490581372134263175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44954853232867969432140533 4214517490581372134263175)
            ·
              refine ⟨6321776235872058201394763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214517490581372134263175 6321776235872058201394763)
              ·
                refine ⟨9482664353808087302092145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321776235872058201394763 9482664353808087302092145)
                ·
                  refine ⟨7111998265356065476569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482664353808087302092145 7111998265356065476569109)
                  ·
                    refine ⟨333374918688565569214177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7111998265356065476569109 333374918688565569214177)
                    ·
                      rfl

theorem cell23_1947736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1947736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947736 prefixEnd_1947736 := by exact prefixLift 1947736
  have htrace : WordTrace (prefixWord ++ tailWord_1947736) baseStart_1947736 baseEnd_1947736 := by
    simpa [prefixWord, tailWord_1947736, baseEnd_1947736] using wordTrace_append hprefix tailTrace_1947736
  have hstable : (prefixWord ++ tailWord_1947736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947736).length < 2 ^ (prefixWord ++ tailWord_1947736).sum := by decide
  have hdescent : baseEnd_1947736 < baseStart_1947736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947777 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1947777 : Nat := 118140960795 + 1947777 * 2 ^ 59
def prefixEnd_1947777 : Nat := 4983230072969 + 3 ^ 40 * 1947777 * 2
def baseEnd_1947777 : Nat := 1000145808772531047229843

theorem tailTrace_1947777 : CollatzResearch.WordTrace tailWord_1947777 prefixEnd_1947777 1000145808772531047229843 := by
  unfold tailWord_1947777
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041263464544057672785585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47360842309696038448523723 71041263464544057672785585)
  ·
    refine ⟨53280947598408043254589189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71041263464544057672785585 53280947598408043254589189)
    ·
      refine ⟨9990177674701508110235473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53280947598408043254589189 9990177674701508110235473)
      ·
        refine ⟨7492633256026131082676605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9990177674701508110235473 7492633256026131082676605)
        ·
          refine ⟨2809737471009799156003727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7492633256026131082676605 2809737471009799156003727)
          ·
            refine ⟨4214606206514698734005591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809737471009799156003727 4214606206514698734005591)
            ·
              refine ⟨6321909309772048101008387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214606206514698734005591 6321909309772048101008387)
              ·
                refine ⟨9482863964658072151512581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321909309772048101008387 9482863964658072151512581)
                ·
                  refine ⟨1778036993373388528408609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9482863964658072151512581 1778036993373388528408609)
                  ·
                    refine ⟨1333527745030041396306457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778036993373388528408609 1333527745030041396306457)
                    ·
                      refine ⟨1000145808772531047229843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333527745030041396306457 1000145808772531047229843)
                      ·
                        rfl

theorem cell23_1947777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1947777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947777 prefixEnd_1947777 := by exact prefixLift 1947777
  have htrace : WordTrace (prefixWord ++ tailWord_1947777) baseStart_1947777 baseEnd_1947777 := by
    simpa [prefixWord, tailWord_1947777, baseEnd_1947777] using wordTrace_append hprefix tailTrace_1947777
  have hstable : (prefixWord ++ tailWord_1947777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947777).length < 2 ^ (prefixWord ++ tailWord_1947777).sum := by decide
  have hdescent : baseEnd_1947777 < baseStart_1947777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947783 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 5]
def baseStart_1947783 : Nat := 118140960795 + 1947783 * 2 ^ 59
def prefixEnd_1947783 : Nat := 4983230072969 + 3 ^ 40 * 1947783 * 2
def baseEnd_1947783 : Nat := 111127654406273113750535

theorem tailTrace_1947783 : CollatzResearch.WordTrace tailWord_1947783 prefixEnd_1947783 111127654406273113750535 := by
  unfold tailWord_1947783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041482302522320697504003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47360988201681547131669335 71041482302522320697504003)
  ·
    refine ⟨106562223453783481046256005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71041482302522320697504003 106562223453783481046256005)
    ·
      refine ⟨19980416897584402696173001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106562223453783481046256005 19980416897584402696173001)
      ·
        refine ⟨14985312673188302022129751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19980416897584402696173001 14985312673188302022129751)
        ·
          refine ⟨22477969009782453033194627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985312673188302022129751 22477969009782453033194627)
          ·
            refine ⟨33716953514673679549791941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477969009782453033194627 33716953514673679549791941)
            ·
              refine ⟨6321928784001314915585989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33716953514673679549791941 6321928784001314915585989)
              ·
                refine ⟨1185361647000246546672373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6321928784001314915585989 1185361647000246546672373)
                ·
                  refine ⟨111127654406273113750535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185361647000246546672373 111127654406273113750535)
                  ·
                    rfl

theorem cell23_1947783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 5].length) (baseStart_1947783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947783 prefixEnd_1947783 := by exact prefixLift 1947783
  have htrace : WordTrace (prefixWord ++ tailWord_1947783) baseStart_1947783 baseEnd_1947783 := by
    simpa [prefixWord, tailWord_1947783, baseEnd_1947783] using wordTrace_append hprefix tailTrace_1947783
  have hstable : (prefixWord ++ tailWord_1947783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947783).length < 2 ^ (prefixWord ++ tailWord_1947783).sum := by decide
  have hdescent : baseEnd_1947783 < baseStart_1947783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947794 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1947794 : Nat := 118140960795 + 1947794 * 2 ^ 59
def prefixEnd_1947794 : Nat := 4983230072969 + 3 ^ 40 * 1947794 * 2
def baseEnd_1947794 : Nat := 1000154537943657480717265

theorem tailTrace_1947794 : CollatzResearch.WordTrace tailWord_1947794 prefixEnd_1947794 1000154537943657480717265 := by
  unfold tailWord_1947794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760470876370617394038609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47361255670321646384102957 17760470876370617394038609)
  ·
    refine ⟨13320353157277963045528957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17760470876370617394038609 13320353157277963045528957)
    ·
      refine ⟨4995132433979236142073359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13320353157277963045528957 4995132433979236142073359)
      ·
        refine ⟨7492698650968854213110039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995132433979236142073359 7492698650968854213110039)
        ·
          refine ⟨11239047976453281319665059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492698650968854213110039 11239047976453281319665059)
          ·
            refine ⟨16858571964679921979497589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239047976453281319665059 16858571964679921979497589)
            ·
              refine ⟨1580491121688742685577899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16858571964679921979497589 1580491121688742685577899)
              ·
                refine ⟨2370736682533114028366849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580491121688742685577899 2370736682533114028366849)
                ·
                  refine ⟨1778052511899835521275137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370736682533114028366849 1778052511899835521275137)
                  ·
                    refine ⟨1333539383924876640956353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778052511899835521275137 1333539383924876640956353)
                    ·
                      refine ⟨1000154537943657480717265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333539383924876640956353 1000154537943657480717265)
                      ·
                        rfl

theorem cell23_1947794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1947794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947794 prefixEnd_1947794 := by exact prefixLift 1947794
  have htrace : WordTrace (prefixWord ++ tailWord_1947794) baseStart_1947794 baseEnd_1947794 := by
    simpa [prefixWord, tailWord_1947794, baseEnd_1947794] using wordTrace_append hprefix tailTrace_1947794
  have hstable : (prefixWord ++ tailWord_1947794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947794).length < 2 ^ (prefixWord ++ tailWord_1947794).sum := by decide
  have hdescent : baseEnd_1947794 < baseStart_1947794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947833 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1947833 : Nat := 118140960795 + 1947833 * 2 ^ 59
def prefixEnd_1947833 : Nat := 4983230072969 + 3 ^ 40 * 1947833 * 2
def baseEnd_1947833 : Nat := 1000174563689182828129585

theorem tailTrace_1947833 : CollatzResearch.WordTrace tailWord_1947833 prefixEnd_1947833 1000174563689182828129585 := by
  unfold tailWord_1947833
  simp only [CollatzResearch.WordTrace]
  refine ⟨71043305952341179236824153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47362203968227452824549435 71043305952341179236824153)
  ·
    refine ⟨53282479464255884427618115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71043305952341179236824153 53282479464255884427618115)
    ·
      refine ⟨79923719196383826641427173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53282479464255884427618115 79923719196383826641427173)
      ·
        refine ⟨14985697349321967495267595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79923719196383826641427173 14985697349321967495267595)
        ·
          refine ⟨22478546023982951242901393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985697349321967495267595 22478546023982951242901393)
          ·
            refine ⟨16858909517987213432176045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22478546023982951242901393 16858909517987213432176045)
            ·
              refine ⟨6322091069245205037066017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16858909517987213432176045 6322091069245205037066017)
              ·
                refine ⟨4741568301933903777799513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6322091069245205037066017 4741568301933903777799513)
                ·
                  refine ⟨3556176226450427833349635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741568301933903777799513 3556176226450427833349635)
                  ·
                    refine ⟨5334264339675641750024453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3556176226450427833349635 5334264339675641750024453)
                    ·
                      refine ⟨1000174563689182828129585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5334264339675641750024453 1000174563689182828129585)
                      ·
                        rfl

theorem cell23_1947833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1947833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947833 prefixEnd_1947833 := by exact prefixLift 1947833
  have htrace : WordTrace (prefixWord ++ tailWord_1947833) baseStart_1947833 baseEnd_1947833 := by
    simpa [prefixWord, tailWord_1947833, baseEnd_1947833] using wordTrace_append hprefix tailTrace_1947833
  have hstable : (prefixWord ++ tailWord_1947833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947833).length < 2 ^ (prefixWord ++ tailWord_1947833).sum := by decide
  have hdescent : baseEnd_1947833 < baseStart_1947833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947876 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1947876 : Nat := 118140960795 + 1947876 * 2 ^ 59
def prefixEnd_1947876 : Nat := 4983230072969 + 3 ^ 40 * 1947876 * 2
def baseEnd_1947876 : Nat := 1000196643357326159891887

theorem tailTrace_1947876 : CollatzResearch.WordTrace tailWord_1947876 prefixEnd_1947876 1000196643357326159891887 := by
  unfold tailWord_1947876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35522437145592698790319741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47363249527456931720426321 35522437145592698790319741)
  ·
    refine ⟨13320913929597262046369903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35522437145592698790319741 13320913929597262046369903)
    ·
      refine ⟨19981370894395893069554855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320913929597262046369903 19981370894395893069554855)
      ·
        refine ⟨29972056341593839604332283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981370894395893069554855 29972056341593839604332283)
        ·
          refine ⟨44958084512390759406498425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29972056341593839604332283 44958084512390759406498425)
          ·
            refine ⟨33718563384293069554873819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44958084512390759406498425 33718563384293069554873819)
            ·
              refine ⟨50577845076439604332310729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33718563384293069554873819 50577845076439604332310729)
              ·
                refine ⟨37933383807329703249233047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50577845076439604332310729 37933383807329703249233047)
                ·
                  refine ⟨56900075710994554873849571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37933383807329703249233047 56900075710994554873849571)
                  ·
                    refine ⟨85350113566491832310774357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56900075710994554873849571 85350113566491832310774357)
                    ·
                      refine ⟨1000196643357326159891887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 85350113566491832310774357 1000196643357326159891887)
                      ·
                        rfl

theorem cell23_1947876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1947876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947876 prefixEnd_1947876 := by exact prefixLift 1947876
  have htrace : WordTrace (prefixWord ++ tailWord_1947876) baseStart_1947876 baseEnd_1947876 := by
    simpa [prefixWord, tailWord_1947876, baseEnd_1947876] using wordTrace_append hprefix tailTrace_1947876
  have hstable : (prefixWord ++ tailWord_1947876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947876).length < 2 ^ (prefixWord ++ tailWord_1947876).sum := by decide
  have hdescent : baseEnd_1947876 < baseStart_1947876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947890 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1947890 : Nat := 118140960795 + 1947890 * 2 ^ 59
def prefixEnd_1947890 : Nat := 4983230072969 + 3 ^ 40 * 1947890 * 2
def baseEnd_1947890 : Nat := 111133759120721011679647

theorem tailTrace_1947890 : CollatzResearch.WordTrace tailWord_1947890 prefixEnd_1947890 111133759120721011679647 := by
  unfold tailWord_1947890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17761346228283669492912281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47363589942089785314432749 17761346228283669492912281)
  ·
    refine ⟨13321009671212752119684211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17761346228283669492912281 13321009671212752119684211)
    ·
      refine ⟨19981514506819128179526317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321009671212752119684211 19981514506819128179526317)
      ·
        refine ⟨7493067940057173067322369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19981514506819128179526317 7493067940057173067322369)
        ·
          refine ⟨5619800955042879800491777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7493067940057173067322369 5619800955042879800491777)
          ·
            refine ⟨4214850716282159850368833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5619800955042879800491777 4214850716282159850368833)
            ·
              refine ⟨3161138037211619887776625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214850716282159850368833 3161138037211619887776625)
              ·
                refine ⟨2370853527908714915832469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161138037211619887776625 2370853527908714915832469)
                ·
                  refine ⟨111133759120721011679647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2370853527908714915832469 111133759120721011679647)
                  ·
                    rfl

theorem cell23_1947890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1947890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947890 prefixEnd_1947890 := by exact prefixLift 1947890
  have htrace : WordTrace (prefixWord ++ tailWord_1947890) baseStart_1947890 baseEnd_1947890 := by
    simpa [prefixWord, tailWord_1947890, baseEnd_1947890] using wordTrace_append hprefix tailTrace_1947890
  have hstable : (prefixWord ++ tailWord_1947890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947890).length < 2 ^ (prefixWord ++ tailWord_1947890).sum := by decide
  have hdescent : baseEnd_1947890 < baseStart_1947890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947894 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1947894 : Nat := 118140960795 + 1947894 * 2 ^ 59
def prefixEnd_1947894 : Nat := 4983230072969 + 3 ^ 40 * 1947894 * 2
def baseEnd_1947894 : Nat := 333401962003035696488935

theorem tailTrace_1947894 : CollatzResearch.WordTrace tailWord_1947894 prefixEnd_1947894 333401962003035696488935 := by
  unfold tailWord_1947894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440345675320011665924671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47363687203413457769863157 4440345675320011665924671)
  ·
    refine ⟨6660518512980017498887007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440345675320011665924671 6660518512980017498887007)
    ·
      refine ⟨9990777769470026248330511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660518512980017498887007 9990777769470026248330511)
      ·
        refine ⟨14986166654205039372495767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990777769470026248330511 14986166654205039372495767)
        ·
          refine ⟨22479249981307559058743651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14986166654205039372495767 22479249981307559058743651)
          ·
            refine ⟨33718874971961338588115477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22479249981307559058743651 33718874971961338588115477)
            ·
              refine ⟨1580572264310687746317913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33718874971961338588115477 1580572264310687746317913)
              ·
                refine ⟨1185429198233015809738435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580572264310687746317913 1185429198233015809738435)
                ·
                  refine ⟨1778143797349523714607653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185429198233015809738435 1778143797349523714607653)
                  ·
                    refine ⟨333401962003035696488935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778143797349523714607653 333401962003035696488935)
                    ·
                      rfl

theorem cell23_1947894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1947894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947894 prefixEnd_1947894 := by exact prefixLift 1947894
  have htrace : WordTrace (prefixWord ++ tailWord_1947894) baseStart_1947894 baseEnd_1947894 := by
    simpa [prefixWord, tailWord_1947894, baseEnd_1947894] using wordTrace_append hprefix tailTrace_1947894
  have hstable : (prefixWord ++ tailWord_1947894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947894).length < 2 ^ (prefixWord ++ tailWord_1947894).sum := by decide
  have hdescent : baseEnd_1947894 < baseStart_1947894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947896 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1947896 : Nat := 118140960795 + 1947896 * 2 ^ 59
def prefixEnd_1947896 : Nat := 4983230072969 + 3 ^ 40 * 1947896 * 2
def baseEnd_1947896 : Nat := 1000206912970416081641795

theorem tailTrace_1947896 : CollatzResearch.WordTrace tailWord_1947896 prefixEnd_1947896 1000206912970416081641795 := by
  unfold tailWord_1947896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35522801875556470498183771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47363735834075293997578361 35522801875556470498183771)
  ·
    refine ⟨53284202813334705747275657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35522801875556470498183771 53284202813334705747275657)
    ·
      refine ⟨39963152110001029310456743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53284202813334705747275657 39963152110001029310456743)
      ·
        refine ⟨59944728165001543965685115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39963152110001029310456743 59944728165001543965685115)
        ·
          refine ⟨89917092247502315948527673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59944728165001543965685115 89917092247502315948527673)
          ·
            refine ⟨67437819185626736961395755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89917092247502315948527673 67437819185626736961395755)
            ·
              refine ⟨101156728778440105442093633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67437819185626736961395755 101156728778440105442093633)
              ·
                refine ⟨75867546583830079081570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101156728778440105442093633 75867546583830079081570225)
                ·
                  refine ⟨56900659937872559311177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75867546583830079081570225 56900659937872559311177669)
                  ·
                    refine ⟨10668873738351104870845813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56900659937872559311177669 10668873738351104870845813)
                    ·
                      refine ⟨1000206912970416081641795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10668873738351104870845813 1000206912970416081641795)
                      ·
                        rfl

theorem cell23_1947896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1947896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947896 prefixEnd_1947896 := by exact prefixLift 1947896
  have htrace : WordTrace (prefixWord ++ tailWord_1947896) baseStart_1947896 baseEnd_1947896 := by
    simpa [prefixWord, tailWord_1947896, baseEnd_1947896] using wordTrace_append hprefix tailTrace_1947896
  have hstable : (prefixWord ++ tailWord_1947896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947896).length < 2 ^ (prefixWord ++ tailWord_1947896).sum := by decide
  have hdescent : baseEnd_1947896 < baseStart_1947896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947927 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1947927 : Nat := 118140960795 + 1947927 * 2 ^ 59
def prefixEnd_1947927 : Nat := 4983230072969 + 3 ^ 40 * 1947927 * 2
def baseEnd_1947927 : Nat := 1000222830870705460354153

theorem tailTrace_1947927 : CollatzResearch.WordTrace tailWord_1947927 prefixEnd_1947927 1000222830870705460354153 := by
  unfold tailWord_1947927
  simp only [CollatzResearch.WordTrace]
  refine ⟨71046734414000633290746035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47364489609333755527164023 71046734414000633290746035)
  ·
    refine ⟨106570101621000949936119053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71046734414000633290746035 106570101621000949936119053)
    ·
      refine ⟨39963788107875356226044645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106570101621000949936119053 39963788107875356226044645)
      ·
        refine ⟨7493210270226629292383371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39963788107875356226044645 7493210270226629292383371)
        ·
          refine ⟨11239815405339943938575057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493210270226629292383371 11239815405339943938575057)
          ·
            refine ⟨8429861554004957953931293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11239815405339943938575057 8429861554004957953931293)
            ·
              refine ⟨3161198082751859232724235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8429861554004957953931293 3161198082751859232724235)
              ·
                refine ⟨4741797124127788849086353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161198082751859232724235 4741797124127788849086353)
                ·
                  refine ⟨3556347843095841636814765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741797124127788849086353 3556347843095841636814765)
                  ·
                    refine ⟨1333630441160940613805537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3556347843095841636814765 1333630441160940613805537)
                    ·
                      refine ⟨1000222830870705460354153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333630441160940613805537 1000222830870705460354153)
                      ·
                        rfl

theorem cell23_1947927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1947927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947927 prefixEnd_1947927 := by exact prefixLift 1947927
  have htrace : WordTrace (prefixWord ++ tailWord_1947927) baseStart_1947927 baseEnd_1947927 := by
    simpa [prefixWord, tailWord_1947927, baseEnd_1947927] using wordTrace_append hprefix tailTrace_1947927
  have hstable : (prefixWord ++ tailWord_1947927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947927).length < 2 ^ (prefixWord ++ tailWord_1947927).sum := by decide
  have hdescent : baseEnd_1947927 < baseStart_1947927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947967 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 2, 4]
def baseStart_1947967 : Nat := 118140960795 + 1947967 * 2 ^ 59
def prefixEnd_1947967 : Nat := 4983230072969 + 3 ^ 40 * 1947967 * 2
def baseEnd_1947967 : Nat := 333414456698961767951323

theorem tailTrace_1947967 : CollatzResearch.WordTrace tailWord_1947967 prefixEnd_1947967 333414456698961767951323 := by
  unfold tailWord_1947967
  simp only [CollatzResearch.WordTrace]
  refine ⟨71048193333855720122202155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47365462222570480081468103 71048193333855720122202155)
  ·
    refine ⟨106572290000783580183303233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71048193333855720122202155 106572290000783580183303233)
    ·
      refine ⟨79929217500587685137477425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106572290000783580183303233 79929217500587685137477425)
      ·
        refine ⟨59946913125440763853108069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79929217500587685137477425 59946913125440763853108069)
        ·
          refine ⟨11240046211020143222457763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59946913125440763853108069 11240046211020143222457763)
          ·
            refine ⟨16860069316530214833686645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240046211020143222457763 16860069316530214833686645)
            ·
              refine ⟨1580631498424707640658123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16860069316530214833686645 1580631498424707640658123)
              ·
                refine ⟨2370947247637061460987185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580631498424707640658123 2370947247637061460987185)
                ·
                  refine ⟨1778210435727796095740389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370947247637061460987185 1778210435727796095740389)
                  ·
                    refine ⟨333414456698961767951323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778210435727796095740389 333414456698961767951323)
                    ·
                      rfl

theorem cell23_1947967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_1947967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1947967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1947967 prefixEnd_1947967 := by exact prefixLift 1947967
  have htrace : WordTrace (prefixWord ++ tailWord_1947967) baseStart_1947967 baseEnd_1947967 := by
    simpa [prefixWord, tailWord_1947967, baseEnd_1947967] using wordTrace_append hprefix tailTrace_1947967
  have hstable : (prefixWord ++ tailWord_1947967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947967).length < 2 ^ (prefixWord ++ tailWord_1947967).sum := by decide
  have hdescent : baseEnd_1947967 < baseStart_1947967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948003 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1948003 : Nat := 118140960795 + 1948003 * 2 ^ 59
def prefixEnd_1948003 : Nat := 4983230072969 + 3 ^ 40 * 1948003 * 2
def baseEnd_1948003 : Nat := 1000261855400447163003803

theorem tailTrace_1948003 : CollatzResearch.WordTrace tailWord_1948003 prefixEnd_1948003 1000261855400447163003803 := by
  unfold tailWord_1948003
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049506361725298270512663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47366337574483532180341775 71049506361725298270512663)
  ·
    refine ⟨106574259542587947405768995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71049506361725298270512663 106574259542587947405768995)
    ·
      refine ⟨159861389313881921108653493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106574259542587947405768995 159861389313881921108653493)
      ·
        refine ⟨14987005248176430103936265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159861389313881921108653493 14987005248176430103936265)
        ·
          refine ⟨11240253936132322577952199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14987005248176430103936265 11240253936132322577952199)
          ·
            refine ⟨16860380904198483866928299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240253936132322577952199 16860380904198483866928299)
            ·
              refine ⟨25290571356297725800392449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860380904198483866928299 25290571356297725800392449)
              ·
                refine ⟨18967928517223294350294337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25290571356297725800392449 18967928517223294350294337)
                ·
                  refine ⟨14225946387917470762720753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18967928517223294350294337 14225946387917470762720753)
                  ·
                    refine ⟨10669459790938103072040565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14225946387917470762720753 10669459790938103072040565)
                    ·
                      refine ⟨1000261855400447163003803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10669459790938103072040565 1000261855400447163003803)
                      ·
                        rfl

theorem cell23_1948003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1948003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948003 prefixEnd_1948003 := by exact prefixLift 1948003
  have htrace : WordTrace (prefixWord ++ tailWord_1948003) baseStart_1948003 baseEnd_1948003 := by
    simpa [prefixWord, tailWord_1948003, baseEnd_1948003] using wordTrace_append hprefix tailTrace_1948003
  have hstable : (prefixWord ++ tailWord_1948003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948003).length < 2 ^ (prefixWord ++ tailWord_1948003).sum := by decide
  have hdescent : baseEnd_1948003 < baseStart_1948003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948007 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1948007 : Nat := 118140960795 + 1948007 * 2 ^ 59
def prefixEnd_1948007 : Nat := 4983230072969 + 3 ^ 40 * 1948007 * 2
def baseEnd_1948007 : Nat := 1000263909323065147353785

theorem tailTrace_1948007 : CollatzResearch.WordTrace tailWord_1948007 prefixEnd_1948007 1000263909323065147353785 := by
  unfold tailWord_1948007
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049652253710806953658275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47366434835807204635772183 71049652253710806953658275)
  ·
    refine ⟨106574478380566210430487413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71049652253710806953658275 106574478380566210430487413)
    ·
      refine ⟨9991357348178082227858195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106574478380566210430487413 9991357348178082227858195)
      ·
        refine ⟨14987036022267123341787293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9991357348178082227858195 14987036022267123341787293)
        ·
          refine ⟨5620138508350171253170235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14987036022267123341787293 5620138508350171253170235)
          ·
            refine ⟨8430207762525256879755353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620138508350171253170235 8430207762525256879755353)
            ·
              refine ⟨6322655821893942659816515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8430207762525256879755353 6322655821893942659816515)
              ·
                refine ⟨9483983732840913989724773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322655821893942659816515 9483983732840913989724773)
                ·
                  refine ⟨1778246949907671373073395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9483983732840913989724773 1778246949907671373073395)
                  ·
                    refine ⟨2667370424861507059610093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778246949907671373073395 2667370424861507059610093)
                    ·
                      refine ⟨1000263909323065147353785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667370424861507059610093 1000263909323065147353785)
                      ·
                        rfl

theorem cell23_1948007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1948007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948007 prefixEnd_1948007 := by exact prefixLift 1948007
  have htrace : WordTrace (prefixWord ++ tailWord_1948007) baseStart_1948007 baseEnd_1948007 := by
    simpa [prefixWord, tailWord_1948007, baseEnd_1948007] using wordTrace_append hprefix tailTrace_1948007
  have hstable : (prefixWord ++ tailWord_1948007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948007).length < 2 ^ (prefixWord ++ tailWord_1948007).sum := by decide
  have hdescent : baseEnd_1948007 < baseStart_1948007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948008 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1948008 : Nat := 118140960795 + 1948008 * 2 ^ 59
def prefixEnd_1948008 : Nat := 4983230072969 + 3 ^ 40 * 1948008 * 2
def baseEnd_1948008 : Nat := 1000264422803719643441281

theorem tailTrace_1948008 : CollatzResearch.WordTrace tailWord_1948008 prefixEnd_1948008 1000264422803719643441281 := by
  unfold tailWord_1948008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35524844363353592062222339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47366459151138122749629785 35524844363353592062222339)
  ·
    refine ⟨53287266545030388093333509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35524844363353592062222339 53287266545030388093333509)
    ·
      refine ⟨9991362477193197767500033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53287266545030388093333509 9991362477193197767500033)
      ·
        refine ⟨7493521857894898325625025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9991362477193197767500033 7493521857894898325625025)
        ·
          refine ⟨5620141393421173744218769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7493521857894898325625025 5620141393421173744218769)
          ·
            refine ⟨4215106045065880308164077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5620141393421173744218769 4215106045065880308164077)
            ·
              refine ⟨1580664766899705115561529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4215106045065880308164077 1580664766899705115561529)
              ·
                refine ⟨1185498575174778836671147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580664766899705115561529 1185498575174778836671147)
                ·
                  refine ⟨1778247862762168255006721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185498575174778836671147 1778247862762168255006721)
                  ·
                    refine ⟨1333685897071626191255041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778247862762168255006721 1333685897071626191255041)
                    ·
                      refine ⟨1000264422803719643441281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333685897071626191255041 1000264422803719643441281)
                      ·
                        rfl

theorem cell23_1948008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1948008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948008 prefixEnd_1948008 := by exact prefixLift 1948008
  have htrace : WordTrace (prefixWord ++ tailWord_1948008) baseStart_1948008 baseEnd_1948008 := by
    simpa [prefixWord, tailWord_1948008, baseEnd_1948008] using wordTrace_append hprefix tailTrace_1948008
  have hstable : (prefixWord ++ tailWord_1948008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948008).length < 2 ^ (prefixWord ++ tailWord_1948008).sum := by decide
  have hdescent : baseEnd_1948008 < baseStart_1948008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948064 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2]
def baseStart_1948064 : Nat := 118140960795 + 1948064 * 2 ^ 59
def prefixEnd_1948064 : Nat := 4983230072969 + 3 ^ 40 * 1948064 * 2
def baseEnd_1948064 : Nat := 1000293177720371424341023

theorem tailTrace_1948064 : CollatzResearch.WordTrace tailWord_1948064 prefixEnd_1948064 1000293177720371424341023 := by
  unfold tailWord_1948064
  simp only [CollatzResearch.WordTrace]
  refine ⟨35525865607252152844241623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47367820809669537125655497 35525865607252152844241623)
  ·
    refine ⟨53288798410878229266362435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35525865607252152844241623 53288798410878229266362435)
    ·
      refine ⟨79933197616317343899543653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53288798410878229266362435 79933197616317343899543653)
      ·
        refine ⟨14987474553059501981164435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79933197616317343899543653 14987474553059501981164435)
        ·
          refine ⟨22481211829589252971746653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14987474553059501981164435 22481211829589252971746653)
          ·
            refine ⟨8430454436095969864404995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22481211829589252971746653 8430454436095969864404995)
            ·
              refine ⟨12645681654143954796607493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430454436095969864404995 12645681654143954796607493)
              ·
                refine ⟨2371065310151991524363905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12645681654143954796607493 2371065310151991524363905)
                ·
                  refine ⟨1778298982613993643272929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2371065310151991524363905 1778298982613993643272929)
                  ·
                    refine ⟨1333724236960495232454697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778298982613993643272929 1333724236960495232454697)
                    ·
                      refine ⟨1000293177720371424341023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333724236960495232454697 1000293177720371424341023)
                      ·
                        rfl

theorem cell23_1948064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_1948064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948064 prefixEnd_1948064 := by exact prefixLift 1948064
  have htrace : WordTrace (prefixWord ++ tailWord_1948064) baseStart_1948064 baseEnd_1948064 := by
    simpa [prefixWord, tailWord_1948064, baseEnd_1948064] using wordTrace_append hprefix tailTrace_1948064
  have hstable : (prefixWord ++ tailWord_1948064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948064).length < 2 ^ (prefixWord ++ tailWord_1948064).sum := by decide
  have hdescent : baseEnd_1948064 < baseStart_1948064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948113 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_1948113 : Nat := 118140960795 + 1948113 * 2 ^ 59
def prefixEnd_1948113 : Nat := 4983230072969 + 3 ^ 40 * 1948113 * 2
def baseEnd_1948113 : Nat := 333439446090813910876099

theorem tailTrace_1948113 : CollatzResearch.WordTrace tailWord_1948113 prefixEnd_1948113 333439446090813910876099 := by
  unfold tailWord_1948113
  simp only [CollatzResearch.WordTrace]
  refine ⟨71053518391326787057016993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47369012260884524704677995 71053518391326787057016993)
  ·
    refine ⟨53290138793495090292762745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71053518391326787057016993 53290138793495090292762745)
    ·
      refine ⟨39967604095121317719572059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53290138793495090292762745 39967604095121317719572059)
      ·
        refine ⟨59951406142681976579358089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967604095121317719572059 59951406142681976579358089)
        ·
          refine ⟨44963554607011482434518567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59951406142681976579358089 44963554607011482434518567)
          ·
            refine ⟨67445331910517223651777851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44963554607011482434518567 67445331910517223651777851)
            ·
              refine ⟨101167997865775835477666777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67445331910517223651777851 101167997865775835477666777)
              ·
                refine ⟨75875998399331876608250083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101167997865775835477666777 75875998399331876608250083)
                ·
                  refine ⟨113813997598997814912375125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75875998399331876608250083 113813997598997814912375125)
                  ·
                    refine ⟨333439446090813910876099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 113813997598997814912375125 333439446090813910876099)
                    ·
                      rfl

theorem cell23_1948113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_1948113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948113 prefixEnd_1948113 := by exact prefixLift 1948113
  have htrace : WordTrace (prefixWord ++ tailWord_1948113) baseStart_1948113 baseEnd_1948113 := by
    simpa [prefixWord, tailWord_1948113, baseEnd_1948113] using wordTrace_append hprefix tailTrace_1948113
  have hstable : (prefixWord ++ tailWord_1948113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948113).length < 2 ^ (prefixWord ++ tailWord_1948113).sum := by decide
  have hdescent : baseEnd_1948113 < baseStart_1948113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948120 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1948120 : Nat := 118140960795 + 1948120 * 2 ^ 59
def prefixEnd_1948120 : Nat := 4983230072969 + 3 ^ 40 * 1948120 * 2
def baseEnd_1948120 : Nat := 1000321932637023205240765

theorem tailTrace_1948120 : CollatzResearch.WordTrace tailWord_1948120 prefixEnd_1948120 1000321932637023205240765 := by
  unfold tailWord_1948120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526886851150713626260907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47369182468200951501681209 35526886851150713626260907)
  ·
    refine ⟨53290330276726070439391361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35526886851150713626260907 53290330276726070439391361)
    ·
      refine ⟨39967747707544552829543521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53290330276726070439391361 39967747707544552829543521)
      ·
        refine ⟨29975810780658414622157641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39967747707544552829543521 29975810780658414622157641)
        ·
          refine ⟨22481858085493810966618231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29975810780658414622157641 22481858085493810966618231)
          ·
            refine ⟨33722787128240716449927347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22481858085493810966618231 33722787128240716449927347)
            ·
              refine ⟨50584180692361074674891021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33722787128240716449927347 50584180692361074674891021)
              ·
                refine ⟨18969067759635403003084133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50584180692361074674891021 18969067759635403003084133)
                ·
                  refine ⟨3556700204931638063078275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18969067759635403003084133 3556700204931638063078275)
                  ·
                    refine ⟨5335050307397457094617413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3556700204931638063078275 5335050307397457094617413)
                    ·
                      refine ⟨1000321932637023205240765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5335050307397457094617413 1000321932637023205240765)
                      ·
                        rfl

theorem cell23_1948120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1948120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948120 prefixEnd_1948120 := by exact prefixLift 1948120
  have htrace : WordTrace (prefixWord ++ tailWord_1948120) baseStart_1948120 baseEnd_1948120 := by
    simpa [prefixWord, tailWord_1948120, baseEnd_1948120] using wordTrace_append hprefix tailTrace_1948120
  have hstable : (prefixWord ++ tailWord_1948120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948120).length < 2 ^ (prefixWord ++ tailWord_1948120).sum := by decide
  have hdescent : baseEnd_1948120 < baseStart_1948120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948140 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1948140 : Nat := 118140960795 + 1948140 * 2 ^ 59
def prefixEnd_1948140 : Nat := 4983230072969 + 3 ^ 40 * 1948140 * 2
def baseEnd_1948140 : Nat := 1000332202250113126990673

theorem tailTrace_1948140 : CollatzResearch.WordTrace tailWord_1948140 prefixEnd_1948140 1000332202250113126990673 := by
  unfold tailWord_1948140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35527251581114485334124937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47369668774819313778833249 35527251581114485334124937)
  ·
    refine ⟨26645438685835864000593703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35527251581114485334124937 26645438685835864000593703)
    ·
      refine ⟨39968158028753796000890555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26645438685835864000593703 39968158028753796000890555)
      ·
        refine ⟨59952237043130694001335833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39968158028753796000890555 59952237043130694001335833)
        ·
          refine ⟨44964177782348020501001875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59952237043130694001335833 44964177782348020501001875)
          ·
            refine ⟨67446266673522030751502813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44964177782348020501001875 67446266673522030751502813)
            ·
              refine ⟨25292350002570761531813555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67446266673522030751502813 25292350002570761531813555)
              ·
                refine ⟨37938525003856142297720333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25292350002570761531813555 37938525003856142297720333)
                ·
                  refine ⟨14226946876446053361645125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37938525003856142297720333 14226946876446053361645125)
                  ·
                    refine ⟨2667552539333635005308461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14226946876446053361645125 2667552539333635005308461)
                    ·
                      refine ⟨1000332202250113126990673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667552539333635005308461 1000332202250113126990673)
                      ·
                        rfl

theorem cell23_1948140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1948140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948140 prefixEnd_1948140 := by exact prefixLift 1948140
  have htrace : WordTrace (prefixWord ++ tailWord_1948140) baseStart_1948140 baseEnd_1948140 := by
    simpa [prefixWord, tailWord_1948140, baseEnd_1948140] using wordTrace_append hprefix tailTrace_1948140
  have hstable : (prefixWord ++ tailWord_1948140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948140).length < 2 ^ (prefixWord ++ tailWord_1948140).sum := by decide
  have hdescent : baseEnd_1948140 < baseStart_1948140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948157 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_1948157 : Nat := 118140960795 + 1948157 * 2 ^ 59
def prefixEnd_1948157 : Nat := 4983230072969 + 3 ^ 40 * 1948157 * 2
def baseEnd_1948157 : Nat := 1000340931421239560478095

theorem tailTrace_1948157 : CollatzResearch.WordTrace tailWord_1948157 prefixEnd_1948157 1000340931421239560478095 := by
  unfold tailWord_1948157
  simp only [CollatzResearch.WordTrace]
  refine ⟨71055123203167382571618725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47370082135444921714412483 71055123203167382571618725)
  ·
    refine ⟨13322835600593884232178511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71055123203167382571618725 13322835600593884232178511)
    ·
      refine ⟨19984253400890826348267767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13322835600593884232178511 19984253400890826348267767)
      ·
        refine ⟨29976380101336239522401651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984253400890826348267767 29976380101336239522401651)
        ·
          refine ⟨44964570152004359283602477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29976380101336239522401651 44964570152004359283602477)
          ·
            refine ⟨16861713807001634731350929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44964570152004359283602477 16861713807001634731350929)
            ·
              refine ⟨12646285355251226048513197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16861713807001634731350929 12646285355251226048513197)
              ·
                refine ⟨4742357008219209768192449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12646285355251226048513197 4742357008219209768192449)
                ·
                  refine ⟨3556767756164407326144337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742357008219209768192449 3556767756164407326144337)
                  ·
                    refine ⟨2667575817123305494608253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556767756164407326144337 2667575817123305494608253)
                    ·
                      refine ⟨1000340931421239560478095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667575817123305494608253 1000340931421239560478095)
                      ·
                        rfl

theorem cell23_1948157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_1948157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948157 prefixEnd_1948157 := by exact prefixLift 1948157
  have htrace : WordTrace (prefixWord ++ tailWord_1948157) baseStart_1948157 baseEnd_1948157 := by
    simpa [prefixWord, tailWord_1948157, baseEnd_1948157] using wordTrace_append hprefix tailTrace_1948157
  have hstable : (prefixWord ++ tailWord_1948157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948157).length < 2 ^ (prefixWord ++ tailWord_1948157).sum := by decide
  have hdescent : baseEnd_1948157 < baseStart_1948157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948174 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1948174 : Nat := 118140960795 + 1948174 * 2 ^ 59
def prefixEnd_1948174 : Nat := 4983230072969 + 3 ^ 40 * 1948174 * 2
def baseEnd_1948174 : Nat := 1000349660592365993965517

theorem tailTrace_1948174 : CollatzResearch.WordTrace tailWord_1948174 prefixEnd_1948174 1000349660592365993965517 := by
  unfold tailWord_1948174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881967905513224309373447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47370495496070529649991717 8881967905513224309373447)
  ·
    refine ⟨13322951858269836464060171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8881967905513224309373447 13322951858269836464060171)
    ·
      refine ⟨19984427787404754696090257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13322951858269836464060171 19984427787404754696090257)
      ·
        refine ⟨14988320840553566022067693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19984427787404754696090257 14988320840553566022067693)
        ·
          refine ⟨5620620315207587258275385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14988320840553566022067693 5620620315207587258275385)
          ·
            refine ⟨4215465236405690443706539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5620620315207587258275385 4215465236405690443706539)
            ·
              refine ⟨6323197854608535665559809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215465236405690443706539 6323197854608535665559809)
              ·
                refine ⟨4742398390956401749169857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323197854608535665559809 4742398390956401749169857)
                ·
                  refine ⟨3556798793217301311877393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742398390956401749169857 3556798793217301311877393)
                  ·
                    refine ⟨2667599094912975983908045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556798793217301311877393 2667599094912975983908045)
                    ·
                      refine ⟨1000349660592365993965517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667599094912975983908045 1000349660592365993965517)
                      ·
                        rfl

theorem cell23_1948174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1948174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948174 prefixEnd_1948174 := by exact prefixLift 1948174
  have htrace : WordTrace (prefixWord ++ tailWord_1948174) baseStart_1948174 baseEnd_1948174 := by
    simpa [prefixWord, tailWord_1948174, baseEnd_1948174] using wordTrace_append hprefix tailTrace_1948174
  have hstable : (prefixWord ++ tailWord_1948174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948174).length < 2 ^ (prefixWord ++ tailWord_1948174).sum := by decide
  have hdescent : baseEnd_1948174 < baseStart_1948174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948181 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1948181 : Nat := 118140960795 + 1948181 * 2 ^ 59
def prefixEnd_1948181 : Nat := 4983230072969 + 3 ^ 40 * 1948181 * 2
def baseEnd_1948181 : Nat := 333451084985649155525995

theorem tailTrace_1948181 : CollatzResearch.WordTrace tailWord_1948181 prefixEnd_1948181 333451084985649155525995 := by
  unfold tailWord_1948181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71055998555080434670492397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47370665703386956446994931 71055998555080434670492397)
  ·
    refine ⟨26645999458155163001434649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71055998555080434670492397 26645999458155163001434649)
    ·
      refine ⟨19984499593616372251075987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26645999458155163001434649 19984499593616372251075987)
      ·
        refine ⟨29976749390424558376613981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984499593616372251075987 29976749390424558376613981)
        ·
          refine ⟨11241281021409209391230243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29976749390424558376613981 11241281021409209391230243)
          ·
            refine ⟨16861921532113814086845365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241281021409209391230243 16861921532113814086845365)
            ·
              refine ⟨1580805143635670070641753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16861921532113814086845365 1580805143635670070641753)
              ·
                refine ⟨1185603857726752552981315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580805143635670070641753 1185603857726752552981315)
                ·
                  refine ⟨1778405786590128829471973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185603857726752552981315 1778405786590128829471973)
                  ·
                    refine ⟨333451084985649155525995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778405786590128829471973 333451084985649155525995)
                    ·
                      rfl

theorem cell23_1948181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1948181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948181 prefixEnd_1948181 := by exact prefixLift 1948181
  have htrace : WordTrace (prefixWord ++ tailWord_1948181) baseStart_1948181 baseEnd_1948181 := by
    simpa [prefixWord, tailWord_1948181, baseEnd_1948181] using wordTrace_append hprefix tailTrace_1948181
  have hstable : (prefixWord ++ tailWord_1948181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948181).length < 2 ^ (prefixWord ++ tailWord_1948181).sum := by decide
  have hdescent : baseEnd_1948181 < baseStart_1948181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948197 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_1948197 : Nat := 118140960795 + 1948197 * 2 ^ 59
def prefixEnd_1948197 : Nat := 4983230072969 + 3 ^ 40 * 1948197 * 2
def baseEnd_1948197 : Nat := 1000361470647419403977911

theorem tailTrace_1948197 : CollatzResearch.WordTrace tailWord_1948197 prefixEnd_1948197 1000361470647419403977911 := by
  unfold tailWord_1948197
  simp only [CollatzResearch.WordTrace]
  refine ⟨71056582123022469403074845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47371054748681646268716563 71056582123022469403074845)
  ·
    refine ⟨26646218296133426026153067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71056582123022469403074845 26646218296133426026153067)
    ·
      refine ⟨39969327444200139039229601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26646218296133426026153067 39969327444200139039229601)
      ·
        refine ⟨29976995583150104279422201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39969327444200139039229601 29976995583150104279422201)
        ·
          refine ⟨22482746687362578209566651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29976995583150104279422201 22482746687362578209566651)
          ·
            refine ⟨33724120031043867314349977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22482746687362578209566651 33724120031043867314349977)
            ·
              refine ⟨25293090023282900485762483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33724120031043867314349977 25293090023282900485762483)
              ·
                refine ⟨37939635034924350728643725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25293090023282900485762483 37939635034924350728643725)
                ·
                  refine ⟨14227363138096631523241397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37939635034924350728643725 14227363138096631523241397)
                  ·
                    refine ⟨1333815294196559205303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14227363138096631523241397 1333815294196559205303881)
                    ·
                      refine ⟨1000361470647419403977911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333815294196559205303881 1000361470647419403977911)
                      ·
                        rfl

theorem cell23_1948197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_1948197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948197 prefixEnd_1948197 := by exact prefixLift 1948197
  have htrace : WordTrace (prefixWord ++ tailWord_1948197) baseStart_1948197 baseEnd_1948197 := by
    simpa [prefixWord, tailWord_1948197, baseEnd_1948197] using wordTrace_append hprefix tailTrace_1948197
  have hstable : (prefixWord ++ tailWord_1948197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948197).length < 2 ^ (prefixWord ++ tailWord_1948197).sum := by decide
  have hdescent : baseEnd_1948197 < baseStart_1948197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948227 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 4]
def baseStart_1948227 : Nat := 118140960795 + 1948227 * 2 ^ 59
def prefixEnd_1948227 : Nat := 4983230072969 + 3 ^ 40 * 1948227 * 2
def baseEnd_1948227 : Nat := 1000376875067054286602773

theorem tailTrace_1948227 : CollatzResearch.WordTrace tailWord_1948227 prefixEnd_1948227 1000376875067054286602773 := by
  unfold tailWord_1948227
  simp only [CollatzResearch.WordTrace]
  refine ⟨71057676312913784526666935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47371784208609189684444623 71057676312913784526666935)
  ·
    refine ⟨106586514469370676790000403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71057676312913784526666935 106586514469370676790000403)
    ·
      refine ⟨159879771704056015185000605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106586514469370676790000403 159879771704056015185000605)
      ·
        refine ⟨59954914389021005694375227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159879771704056015185000605 59954914389021005694375227)
        ·
          refine ⟨89932371583531508541562841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59954914389021005694375227 89932371583531508541562841)
          ·
            refine ⟨67449278687648631406172131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89932371583531508541562841 67449278687648631406172131)
            ·
              refine ⟨101173918031472947109258197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67449278687648631406172131 101173918031472947109258197)
              ·
                refine ⟨2371263703862647197873239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101173918031472947109258197 2371263703862647197873239)
                ·
                  refine ⟨3556895555793970796809859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371263703862647197873239 3556895555793970796809859)
                  ·
                    refine ⟨5335343333690956195214789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3556895555793970796809859 5335343333690956195214789)
                    ·
                      refine ⟨1000376875067054286602773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5335343333690956195214789 1000376875067054286602773)
                      ·
                        rfl

theorem cell23_1948227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_1948227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948227 prefixEnd_1948227 := by exact prefixLift 1948227
  have htrace : WordTrace (prefixWord ++ tailWord_1948227) baseStart_1948227 baseEnd_1948227 := by
    simpa [prefixWord, tailWord_1948227, baseEnd_1948227] using wordTrace_append hprefix tailTrace_1948227
  have hstable : (prefixWord ++ tailWord_1948227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948227).length < 2 ^ (prefixWord ++ tailWord_1948227).sum := by decide
  have hdescent : baseEnd_1948227 < baseStart_1948227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948228 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 6]
def baseStart_1948228 : Nat := 118140960795 + 1948228 * 2 ^ 59
def prefixEnd_1948228 : Nat := 4983230072969 + 3 ^ 40 * 1948228 * 2
def baseEnd_1948228 : Nat := 111153043171967642521141

theorem tailTrace_1948228 : CollatzResearch.WordTrace tailWord_1948228 prefixEnd_1948228 111153043171967642521141 := by
  unfold tailWord_1948228
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528856392955080848726669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47371808523940107798302225 35528856392955080848726669)
  ·
    refine ⟨13323321147358155318272501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35528856392955080848726669 13323321147358155318272501)
    ·
      refine ⟨1249061357564827061088047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13323321147358155318272501 1249061357564827061088047)
      ·
        refine ⟨1873592036347240591632071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249061357564827061088047 1873592036347240591632071)
        ·
          refine ⟨2810388054520860887448107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873592036347240591632071 2810388054520860887448107)
          ·
            refine ⟨4215582081781291331172161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810388054520860887448107 4215582081781291331172161)
            ·
              refine ⟨3161686561335968498379121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215582081781291331172161 3161686561335968498379121)
              ·
                refine ⟨2371264921001976373784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161686561335968498379121 2371264921001976373784341)
                ·
                  refine ⟨111153043171967642521141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2371264921001976373784341 111153043171967642521141)
                  ·
                    rfl

theorem cell23_1948228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_1948228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948228 prefixEnd_1948228 := by exact prefixLift 1948228
  have htrace : WordTrace (prefixWord ++ tailWord_1948228) baseStart_1948228 baseEnd_1948228 := by
    simpa [prefixWord, tailWord_1948228, baseEnd_1948228] using wordTrace_append hprefix tailTrace_1948228
  have hstable : (prefixWord ++ tailWord_1948228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948228).length < 2 ^ (prefixWord ++ tailWord_1948228).sum := by decide
  have hdescent : baseEnd_1948228 < baseStart_1948228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948238 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_1948238 : Nat := 118140960795 + 1948238 * 2 ^ 59
def prefixEnd_1948238 : Nat := 4983230072969 + 3 ^ 40 * 1948238 * 2
def baseEnd_1948238 : Nat := 1000382523354253743565223

theorem tailTrace_1948238 : CollatzResearch.WordTrace tailWord_1948238 prefixEnd_1948238 1000382523354253743565223 := by
  unfold tailWord_1948238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882259689484241675664671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47372051677249288936878245 8882259689484241675664671)
  ·
    refine ⟨13323389534226362513497007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8882259689484241675664671 13323389534226362513497007)
    ·
      refine ⟨19985084301339543770245511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323389534226362513497007 19985084301339543770245511)
      ·
        refine ⟨29977626452009315655368267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19985084301339543770245511 29977626452009315655368267)
        ·
          refine ⟨44966439678013973483052401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29977626452009315655368267 44966439678013973483052401)
          ·
            refine ⟨33724829758510480112289301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44966439678013973483052401 33724829758510480112289301)
            ·
              refine ⟨1580851394930178755263561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33724829758510480112289301 1580851394930178755263561)
              ·
                refine ⟨1185638546197634066447671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580851394930178755263561 1185638546197634066447671)
                ·
                  refine ⟨1778457819296451099671507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185638546197634066447671 1778457819296451099671507)
                  ·
                    refine ⟨2667686728944676649507261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1778457819296451099671507 2667686728944676649507261)
                    ·
                      refine ⟨1000382523354253743565223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667686728944676649507261 1000382523354253743565223)
                      ·
                        rfl

theorem cell23_1948238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_1948238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948238 prefixEnd_1948238 := by exact prefixLift 1948238
  have htrace : WordTrace (prefixWord ++ tailWord_1948238) baseStart_1948238 baseEnd_1948238 := by
    simpa [prefixWord, tailWord_1948238, baseEnd_1948238] using wordTrace_append hprefix tailTrace_1948238
  have hstable : (prefixWord ++ tailWord_1948238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948238).length < 2 ^ (prefixWord ++ tailWord_1948238).sum := by decide
  have hdescent : baseEnd_1948238 < baseStart_1948238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948240 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1948240 : Nat := 118140960795 + 1948240 * 2 ^ 59
def prefixEnd_1948240 : Nat := 4983230072969 + 3 ^ 40 * 1948240 * 2
def baseEnd_1948240 : Nat := 1000383550315562735740213

theorem tailTrace_1948240 : CollatzResearch.WordTrace tailWord_1948240 prefixEnd_1948240 1000383550315562735740213 := by
  unfold tailWord_1948240
  simp only [CollatzResearch.WordTrace]
  refine ⟨35529075230933343873445087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47372100307911125164593449 35529075230933343873445087)
  ·
    refine ⟨53293612846400015810167631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35529075230933343873445087 53293612846400015810167631)
    ·
      refine ⟨79940419269600023715251447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53293612846400015810167631 79940419269600023715251447)
      ·
        refine ⟨119910628904400035572877171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79940419269600023715251447 119910628904400035572877171)
        ·
          refine ⟨179865943356600053359315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119910628904400035572877171 179865943356600053359315757)
          ·
            refine ⟨67449728758725020009743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179865943356600053359315757 67449728758725020009743409)
            ·
              refine ⟨50587296569043765007307557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67449728758725020009743409 50587296569043765007307557)
              ·
                refine ⟨9485118106695705938870167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50587296569043765007307557 9485118106695705938870167)
                ·
                  refine ⟨14227677160043558908305251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485118106695705938870167 14227677160043558908305251)
                  ·
                    refine ⟨21341515740065338362457877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14227677160043558908305251 21341515740065338362457877)
                    ·
                      refine ⟨1000383550315562735740213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21341515740065338362457877 1000383550315562735740213)
                      ·
                        rfl

theorem cell23_1948240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1948240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948240 prefixEnd_1948240 := by exact prefixLift 1948240
  have htrace : WordTrace (prefixWord ++ tailWord_1948240) baseStart_1948240 baseEnd_1948240 := by
    simpa [prefixWord, tailWord_1948240, baseEnd_1948240] using wordTrace_append hprefix tailTrace_1948240
  have hstable : (prefixWord ++ tailWord_1948240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948240).length < 2 ^ (prefixWord ++ tailWord_1948240).sum := by decide
  have hdescent : baseEnd_1948240 < baseStart_1948240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948247 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1948247 : Nat := 118140960795 + 1948247 * 2 ^ 59
def prefixEnd_1948247 : Nat := 4983230072969 + 3 ^ 40 * 1948247 * 2
def baseEnd_1948247 : Nat := 1000387144680144208352681

theorem tailTrace_1948247 : CollatzResearch.WordTrace tailWord_1948247 prefixEnd_1948247 1000387144680144208352681 := by
  unfold tailWord_1948247
  simp only [CollatzResearch.WordTrace]
  refine ⟨71058405772841327942394995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47372270515227551961596663 71058405772841327942394995)
  ·
    refine ⟨106587608659261991913592493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71058405772841327942394995 106587608659261991913592493)
    ·
      refine ⟨39970353247223246967597185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106587608659261991913592493 39970353247223246967597185)
      ·
        refine ⟨29977764935417435225697889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39970353247223246967597185 29977764935417435225697889)
        ·
          refine ⟨22483323701563076419273417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29977764935417435225697889 22483323701563076419273417)
          ·
            refine ⟨16862492776172307314455063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22483323701563076419273417 16862492776172307314455063)
            ·
              refine ⟨25293739164258460971682595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16862492776172307314455063 25293739164258460971682595)
              ·
                refine ⟨37940608746387691457523893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25293739164258460971682595 37940608746387691457523893)
                ·
                  refine ⟨3556932069973846074142865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37940608746387691457523893 3556932069973846074142865)
                  ·
                    refine ⟨2667699052480384555607149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556932069973846074142865 2667699052480384555607149)
                    ·
                      refine ⟨1000387144680144208352681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667699052480384555607149 1000387144680144208352681)
                      ·
                        rfl

theorem cell23_1948247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1948247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948247 prefixEnd_1948247 := by exact prefixLift 1948247
  have htrace : WordTrace (prefixWord ++ tailWord_1948247) baseStart_1948247 baseEnd_1948247 := by
    simpa [prefixWord, tailWord_1948247, baseEnd_1948247] using wordTrace_append hprefix tailTrace_1948247
  have hstable : (prefixWord ++ tailWord_1948247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948247).length < 2 ^ (prefixWord ++ tailWord_1948247).sum := by decide
  have hdescent : baseEnd_1948247 < baseStart_1948247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948257 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1948257 : Nat := 118140960795 + 1948257 * 2 ^ 59
def prefixEnd_1948257 : Nat := 4983230072969 + 3 ^ 40 * 1948257 * 2
def baseEnd_1948257 : Nat := 1000392279486689169227635

theorem tailTrace_1948257 : CollatzResearch.WordTrace tailWord_1948257 prefixEnd_1948257 1000392279486689169227635 := by
  unfold tailWord_1948257
  simp only [CollatzResearch.WordTrace]
  refine ⟨71058770502805099650259025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47372513668536733100172683 71058770502805099650259025)
  ·
    refine ⟨53294077877103824737694269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71058770502805099650259025 53294077877103824737694269)
    ·
      refine ⟨19985279203913934276635351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53294077877103824737694269 19985279203913934276635351)
      ·
        refine ⟨29977918805870901414953027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19985279203913934276635351 29977918805870901414953027)
        ·
          refine ⟨44966878208806352122429541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29977918805870901414953027 44966878208806352122429541)
          ·
            refine ⟨8431289664151191022955539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44966878208806352122429541 8431289664151191022955539)
            ·
              refine ⟨12646934496226786534433309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431289664151191022955539 12646934496226786534433309)
              ·
                refine ⟨4742600436085044950412491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12646934496226786534433309 4742600436085044950412491)
                ·
                  refine ⟨7113900654127567425618737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742600436085044950412491 7113900654127567425618737)
                  ·
                    refine ⟨5335425490595675569214053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7113900654127567425618737 5335425490595675569214053)
                    ·
                      refine ⟨1000392279486689169227635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5335425490595675569214053 1000392279486689169227635)
                      ·
                        rfl

theorem cell23_1948257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1948257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948257 prefixEnd_1948257 := by exact prefixLift 1948257
  have htrace : WordTrace (prefixWord ++ tailWord_1948257) baseStart_1948257 baseEnd_1948257 := by
    simpa [prefixWord, tailWord_1948257, baseEnd_1948257] using wordTrace_append hprefix tailTrace_1948257
  have hstable : (prefixWord ++ tailWord_1948257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948257).length < 2 ^ (prefixWord ++ tailWord_1948257).sum := by decide
  have hdescent : baseEnd_1948257 < baseStart_1948257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948280 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1948280 : Nat := 118140960795 + 1948280 * 2 ^ 59
def prefixEnd_1948280 : Nat := 4983230072969 + 3 ^ 40 * 1948280 * 2
def baseEnd_1948280 : Nat := 333468029847247526413343

theorem tailTrace_1948280 : CollatzResearch.WordTrace tailWord_1948280 prefixEnd_1948280 333468029847247526413343 := by
  unfold tailWord_1948280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35529804690860887289173147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47373072921147849718897529 35529804690860887289173147)
  ·
    refine ⟨53294707036291330933759721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35529804690860887289173147 53294707036291330933759721)
    ·
      refine ⟨39971030277218498200319791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53294707036291330933759721 39971030277218498200319791)
      ·
        refine ⟨59956545415827747300479687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39971030277218498200319791 59956545415827747300479687)
        ·
          refine ⟨89934818123741620950719531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59956545415827747300479687 89934818123741620950719531)
          ·
            refine ⟨134902227185612431426079297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89934818123741620950719531 134902227185612431426079297)
            ·
              refine ⟨101176670389209323569559473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134902227185612431426079297 101176670389209323569559473)
              ·
                refine ⟨75882502791906992677169605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101176670389209323569559473 75882502791906992677169605)
                ·
                  refine ⟨14227969273482561126969301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75882502791906992677169605 14227969273482561126969301)
                  ·
                    refine ⟨333468029847247526413343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14227969273482561126969301 333468029847247526413343)
                    ·
                      rfl

theorem cell23_1948280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1948280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948280 prefixEnd_1948280 := by exact prefixLift 1948280
  have htrace : WordTrace (prefixWord ++ tailWord_1948280) baseStart_1948280 baseEnd_1948280 := by
    simpa [prefixWord, tailWord_1948280, baseEnd_1948280] using wordTrace_append hprefix tailTrace_1948280
  have hstable : (prefixWord ++ tailWord_1948280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948280).length < 2 ^ (prefixWord ++ tailWord_1948280).sum := by decide
  have hdescent : baseEnd_1948280 < baseStart_1948280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948281 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 1, 2, 3]
def baseStart_1948281 : Nat := 118140960795 + 1948281 * 2 ^ 59
def prefixEnd_1948281 : Nat := 4983230072969 + 3 ^ 40 * 1948281 * 2
def baseEnd_1948281 : Nat := 1000404603022397075327525

theorem tailTrace_1948281 : CollatzResearch.WordTrace tailWord_1948281 prefixEnd_1948281 1000404603022397075327525 := by
  unfold tailWord_1948281
  simp only [CollatzResearch.WordTrace]
  refine ⟨71059645854718151749132697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47373097236478767832755131 71059645854718151749132697)
  ·
    refine ⟨53294734391038613811849523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71059645854718151749132697 53294734391038613811849523)
    ·
      refine ⟨79942101586557920717774285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53294734391038613811849523 79942101586557920717774285)
      ·
        refine ⟨29978288094959220269165357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79942101586557920717774285 29978288094959220269165357)
        ·
          refine ⟨11241858035609707600937009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29978288094959220269165357 11241858035609707600937009)
          ·
            refine ⟨8431393526707280700702757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241858035609707600937009 8431393526707280700702757)
            ·
              refine ⟨1580886286257615131381767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8431393526707280700702757 1580886286257615131381767)
              ·
                refine ⟨2371329429386422697072651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580886286257615131381767 2371329429386422697072651)
                ·
                  refine ⟨3556994144079634045608977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371329429386422697072651 3556994144079634045608977)
                  ·
                    refine ⟨2667745608059725534206733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556994144079634045608977 2667745608059725534206733)
                    ·
                      refine ⟨1000404603022397075327525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2667745608059725534206733 1000404603022397075327525)
                      ·
                        rfl

theorem cell23_1948281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_1948281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948281 prefixEnd_1948281 := by exact prefixLift 1948281
  have htrace : WordTrace (prefixWord ++ tailWord_1948281) baseStart_1948281 baseEnd_1948281 := by
    simpa [prefixWord, tailWord_1948281, baseEnd_1948281] using wordTrace_append hprefix tailTrace_1948281
  have hstable : (prefixWord ++ tailWord_1948281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948281).length < 2 ^ (prefixWord ++ tailWord_1948281).sum := by decide
  have hdescent : baseEnd_1948281 < baseStart_1948281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948317 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1948317 : Nat := 118140960795 + 1948317 * 2 ^ 59
def prefixEnd_1948317 : Nat := 4983230072969 + 3 ^ 40 * 1948317 * 2
def baseEnd_1948317 : Nat := 1000423088325958934477359

theorem tailTrace_1948317 : CollatzResearch.WordTrace tailWord_1948317 prefixEnd_1948317 1000423088325958934477359 := by
  unfold tailWord_1948317
  simp only [CollatzResearch.WordTrace]
  refine ⟨71060958882587729897443205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47373972588391819931628803 71060958882587729897443205)
  ·
    refine ⟨13323929790485199355770601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71060958882587729897443205 13323929790485199355770601)
    ·
      refine ⟨9992947342863899516827951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13323929790485199355770601 9992947342863899516827951)
      ·
        refine ⟨14989421014295849275241927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992947342863899516827951 14989421014295849275241927)
        ·
          refine ⟨22484131521443773912862891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14989421014295849275241927 22484131521443773912862891)
          ·
            refine ⟨33726197282165660869294337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484131521443773912862891 33726197282165660869294337)
            ·
              refine ⟨25294647961624245651970753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33726197282165660869294337 25294647961624245651970753)
              ·
                refine ⟨18970985971218184238978065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25294647961624245651970753 18970985971218184238978065)
                ·
                  refine ⟨14228239478413638179233549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18970985971218184238978065 14228239478413638179233549)
                  ·
                    refine ⟨5335589804405114317212581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228239478413638179233549 5335589804405114317212581)
                    ·
                      refine ⟨1000423088325958934477359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5335589804405114317212581 1000423088325958934477359)
                      ·
                        rfl

theorem cell23_1948317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1948317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948317 prefixEnd_1948317 := by exact prefixLift 1948317
  have htrace : WordTrace (prefixWord ++ tailWord_1948317) baseStart_1948317 baseEnd_1948317 := by
    simpa [prefixWord, tailWord_1948317, baseEnd_1948317] using wordTrace_append hprefix tailTrace_1948317
  have hstable : (prefixWord ++ tailWord_1948317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948317).length < 2 ^ (prefixWord ++ tailWord_1948317).sum := by decide
  have hdescent : baseEnd_1948317 < baseStart_1948317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948351 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 4, 2, 2]
def baseStart_1948351 : Nat := 118140960795 + 1948351 * 2 ^ 59
def prefixEnd_1948351 : Nat := 4983230072969 + 3 ^ 40 * 1948351 * 2
def baseEnd_1948351 : Nat := 1000440546668211801452203

theorem tailTrace_1948351 : CollatzResearch.WordTrace tailWord_1948351 prefixEnd_1948351 1000440546668211801452203 := by
  unfold tailWord_1948351
  simp only [CollatzResearch.WordTrace]
  refine ⟨71062198964464553704180907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47374799309643035802787271 71062198964464553704180907)
  ·
    refine ⟨106593298446696830556271361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71062198964464553704180907 106593298446696830556271361)
    ·
      refine ⟨79944973835022622917203521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106593298446696830556271361 79944973835022622917203521)
      ·
        refine ⟨59958730376266967187902641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79944973835022622917203521 59958730376266967187902641)
        ·
          refine ⟨44969047782200225390926981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59958730376266967187902641 44969047782200225390926981)
          ·
            refine ⟨8431696459162542260798809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44969047782200225390926981 8431696459162542260798809)
            ·
              refine ⟨6323772344371906695599107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431696459162542260798809 6323772344371906695599107)
              ·
                refine ⟨9485658516557860043398661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323772344371906695599107 9485658516557860043398661)
                ·
                  refine ⟨1778560971854598758137249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9485658516557860043398661 1778560971854598758137249)
                  ·
                    refine ⟨1333920728890949068602937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778560971854598758137249 1333920728890949068602937)
                    ·
                      refine ⟨1000440546668211801452203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333920728890949068602937 1000440546668211801452203)
                      ·
                        rfl

theorem cell23_1948351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_1948351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948351 prefixEnd_1948351 := by exact prefixLift 1948351
  have htrace : WordTrace (prefixWord ++ tailWord_1948351) baseStart_1948351 baseEnd_1948351 := by
    simpa [prefixWord, tailWord_1948351, baseEnd_1948351] using wordTrace_append hprefix tailTrace_1948351
  have hstable : (prefixWord ++ tailWord_1948351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948351).length < 2 ^ (prefixWord ++ tailWord_1948351).sum := by decide
  have hdescent : baseEnd_1948351 < baseStart_1948351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948372 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1948372 : Nat := 118140960795 + 1948372 * 2 ^ 59
def prefixEnd_1948372 : Nat := 4983230072969 + 3 ^ 40 * 1948372 * 2
def baseEnd_1948372 : Nat := 1000451329761956219289607

theorem tailTrace_1948372 : CollatzResearch.WordTrace tailWord_1948372 prefixEnd_1948372 1000451329761956219289607 := by
  unfold tailWord_1948372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35531482448694237145347685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47375309931592316193796913 35531482448694237145347685)
  ·
    refine ⟨6662152959130169464752691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35531482448694237145347685 6662152959130169464752691)
    ·
      refine ⟨9993229438695254197129037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662152959130169464752691 9993229438695254197129037)
      ·
        refine ⟨3747461039510720323923389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9993229438695254197129037 3747461039510720323923389)
        ·
          refine ⟨1405297889816520121471271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3747461039510720323923389 1405297889816520121471271)
          ·
            refine ⟨2107946834724780182206907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405297889816520121471271 2107946834724780182206907)
            ·
              refine ⟨3161920252087170273310361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107946834724780182206907 3161920252087170273310361)
              ·
                refine ⟨2371440189065377704982771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161920252087170273310361 2371440189065377704982771)
                ·
                  refine ⟨3557160283598066557474157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371440189065377704982771 3557160283598066557474157)
                  ·
                    refine ⟨1333935106349274959052809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557160283598066557474157 1333935106349274959052809)
                    ·
                      refine ⟨1000451329761956219289607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1333935106349274959052809 1000451329761956219289607)
                      ·
                        rfl

theorem cell23_1948372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1948372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948372 prefixEnd_1948372 := by exact prefixLift 1948372
  have htrace : WordTrace (prefixWord ++ tailWord_1948372) baseStart_1948372 baseEnd_1948372 := by
    simpa [prefixWord, tailWord_1948372, baseEnd_1948372] using wordTrace_append hprefix tailTrace_1948372
  have hstable : (prefixWord ++ tailWord_1948372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948372).length < 2 ^ (prefixWord ++ tailWord_1948372).sum := by decide
  have hdescent : baseEnd_1948372 < baseStart_1948372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948407 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1948407 : Nat := 118140960795 + 1948407 * 2 ^ 59
def prefixEnd_1948407 : Nat := 4983230072969 + 3 ^ 40 * 1948407 * 2
def baseEnd_1948407 : Nat := 1000469301584863582351945

theorem tailTrace_1948407 : CollatzResearch.WordTrace tailWord_1948407 prefixEnd_1948407 1000469301584863582351945 := by
  unfold tailWord_1948407
  simp only [CollatzResearch.WordTrace]
  refine ⟨71064241452261675268219475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47376160968174450178812983 71064241452261675268219475)
  ·
    refine ⟨106596362178392512902329213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71064241452261675268219475 106596362178392512902329213)
    ·
      refine ⟨39973635816897192338373455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106596362178392512902329213 39973635816897192338373455)
      ·
        refine ⟨59960453725345788507560183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39973635816897192338373455 59960453725345788507560183)
        ·
          refine ⟨89940680588018682761340275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59960453725345788507560183 89940680588018682761340275)
          ·
            refine ⟨134911020882028024142010413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89940680588018682761340275 134911020882028024142010413)
            ·
              refine ⟨50591632830760509053253905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134911020882028024142010413 50591632830760509053253905)
              ·
                refine ⟨37943724623070381789940429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50591632830760509053253905 37943724623070381789940429)
                ·
                  refine ⟨14228896733651393171227661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37943724623070381789940429 14228896733651393171227661)
                  ·
                    refine ⟨5335836275119272439210373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14228896733651393171227661 5335836275119272439210373)
                    ·
                      refine ⟨1000469301584863582351945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5335836275119272439210373 1000469301584863582351945)
                      ·
                        rfl

theorem cell23_1948407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1948407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948407 prefixEnd_1948407 := by exact prefixLift 1948407
  have htrace : WordTrace (prefixWord ++ tailWord_1948407) baseStart_1948407 baseEnd_1948407 := by
    simpa [prefixWord, tailWord_1948407, baseEnd_1948407] using wordTrace_append hprefix tailTrace_1948407
  have hstable : (prefixWord ++ tailWord_1948407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948407).length < 2 ^ (prefixWord ++ tailWord_1948407).sum := by decide
  have hdescent : baseEnd_1948407 < baseStart_1948407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948417 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1948417 : Nat := 118140960795 + 1948417 * 2 ^ 59
def prefixEnd_1948417 : Nat := 4983230072969 + 3 ^ 40 * 1948417 * 2
def baseEnd_1948417 : Nat := 333491478797136181075633

theorem tailTrace_1948417 : CollatzResearch.WordTrace tailWord_1948417 prefixEnd_1948417 333491478797136181075633 := by
  unfold tailWord_1948417
  simp only [CollatzResearch.WordTrace]
  refine ⟨71064606182225446976083505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47376404121483631317389003 71064606182225446976083505)
  ·
    refine ⟨53298454636669085232062629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71064606182225446976083505 53298454636669085232062629)
    ·
      refine ⟨9993460244375453481011743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53298454636669085232062629 9993460244375453481011743)
      ·
        refine ⟨14990190366563180221517615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9993460244375453481011743 14990190366563180221517615)
        ·
          refine ⟨22485285549844770332276423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14990190366563180221517615 22485285549844770332276423)
          ·
            refine ⟨33727928324767155498414635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22485285549844770332276423 33727928324767155498414635)
            ·
              refine ⟨50591892487150733247621953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33727928324767155498414635 50591892487150733247621953)
              ·
                refine ⟨37943919365363049935716465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50591892487150733247621953 37943919365363049935716465)
                ·
                  refine ⟨28457939524022287451787349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37943919365363049935716465 28457939524022287451787349)
                  ·
                    refine ⟨333491478797136181075633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28457939524022287451787349 333491478797136181075633)
                    ·
                      rfl

theorem cell23_1948417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1948417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948417 prefixEnd_1948417 := by exact prefixLift 1948417
  have htrace : WordTrace (prefixWord ++ tailWord_1948417) baseStart_1948417 baseEnd_1948417 := by
    simpa [prefixWord, tailWord_1948417, baseEnd_1948417] using wordTrace_append hprefix tailTrace_1948417
  have hstable : (prefixWord ++ tailWord_1948417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948417).length < 2 ^ (prefixWord ++ tailWord_1948417).sum := by decide
  have hdescent : baseEnd_1948417 < baseStart_1948417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948494 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1948494 : Nat := 118140960795 + 1948494 * 2 ^ 59
def prefixEnd_1948494 : Nat := 4983230072969 + 3 ^ 40 * 1948494 * 2
def baseEnd_1948494 : Nat := 333504658133934913988015

theorem tailTrace_1948494 : CollatzResearch.WordTrace tailWord_1948494 prefixEnd_1948494 333504658133934913988015 := by
  unfold tailWord_1948494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883426825368311140829567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47378276401964326084424357 8883426825368311140829567)
  ·
    refine ⟨13325140238052466711244351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883426825368311140829567 13325140238052466711244351)
    ·
      refine ⟨19987710357078700066866527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325140238052466711244351 19987710357078700066866527)
      ·
        refine ⟨29981565535618050100299791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19987710357078700066866527 29981565535618050100299791)
        ·
          refine ⟨44972348303427075150449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29981565535618050100299791 44972348303427075150449687)
          ·
            refine ⟨67458522455140612725674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44972348303427075150449687 67458522455140612725674531)
            ·
              refine ⟨101187783682710919088511797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67458522455140612725674531 101187783682710919088511797)
              ·
                refine ⟨9486354720254148664547981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101187783682710919088511797 9486354720254148664547981)
                ·
                  refine ⟨3557383020095305749205493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9486354720254148664547981 3557383020095305749205493)
                  ·
                    refine ⟨333504658133934913988015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3557383020095305749205493 333504658133934913988015)
                    ·
                      rfl

theorem cell23_1948494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1948494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948494 prefixEnd_1948494 := by exact prefixLift 1948494
  have htrace : WordTrace (prefixWord ++ tailWord_1948494) baseStart_1948494 baseEnd_1948494 := by
    simpa [prefixWord, tailWord_1948494, baseEnd_1948494] using wordTrace_append hprefix tailTrace_1948494
  have hstable : (prefixWord ++ tailWord_1948494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948494).length < 2 ^ (prefixWord ++ tailWord_1948494).sum := by decide
  have hdescent : baseEnd_1948494 < baseStart_1948494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948501 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1948501 : Nat := 118140960795 + 1948501 * 2 ^ 59
def prefixEnd_1948501 : Nat := 4983230072969 + 3 ^ 40 * 1948501 * 2
def baseEnd_1948501 : Nat := 1000517568766386214576513

theorem tailTrace_1948501 : CollatzResearch.WordTrace tailWord_1948501 prefixEnd_1948501 1000517568766386214576513 := by
  unfold tailWord_1948501
  simp only [CollatzResearch.WordTrace]
  refine ⟨71067669913921129322141357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47378446609280752881427571 71067669913921129322141357)
  ·
    refine ⟨26650376217720423495803009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71067669913921129322141357 26650376217720423495803009)
    ·
      refine ⟨19987782163290317621852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26650376217720423495803009 19987782163290317621852257)
      ·
        refine ⟨14990836622467738216389193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19987782163290317621852257 14990836622467738216389193)
        ·
          refine ⟨11243127466850803662291895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14990836622467738216389193 11243127466850803662291895)
          ·
            refine ⟨16864691200276205493437843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243127466850803662291895 16864691200276205493437843)
            ·
              refine ⟨25297036800414308240156765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16864691200276205493437843 25297036800414308240156765)
              ·
                refine ⟨9486388800155365590058787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25297036800414308240156765 9486388800155365590058787)
                ·
                  refine ⟨14229583200233048385088181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486388800155365590058787 14229583200233048385088181)
                  ·
                    refine ⟨1334023425021848286102017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14229583200233048385088181 1334023425021848286102017)
                    ·
                      refine ⟨1000517568766386214576513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334023425021848286102017 1000517568766386214576513)
                      ·
                        rfl

theorem cell23_1948501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1948501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948501 prefixEnd_1948501 := by exact prefixLift 1948501
  have htrace : WordTrace (prefixWord ++ tailWord_1948501) baseStart_1948501 baseEnd_1948501 := by
    simpa [prefixWord, tailWord_1948501, baseEnd_1948501] using wordTrace_append hprefix tailTrace_1948501
  have hstable : (prefixWord ++ tailWord_1948501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948501).length < 2 ^ (prefixWord ++ tailWord_1948501).sum := by decide
  have hdescent : baseEnd_1948501 < baseStart_1948501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948548 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1948548 : Nat := 118140960795 + 1948548 * 2 ^ 59
def prefixEnd_1948548 : Nat := 4983230072969 + 3 ^ 40 * 1948548 * 2
def baseEnd_1948548 : Nat := 1000541702357147530688797

theorem tailTrace_1948548 : CollatzResearch.WordTrace tailWord_1948548 prefixEnd_1948548 1000541702357147530688797 := by
  unfold tailWord_1948548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35534692072375428174551149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47379589429833904232734865 35534692072375428174551149)
  ·
    refine ⟨13325509527140785565456681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35534692072375428174551149 13325509527140785565456681)
    ·
      refine ⟨9994132145355589174092511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13325509527140785565456681 9994132145355589174092511)
      ·
        refine ⟨14991198218033383761138767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994132145355589174092511 14991198218033383761138767)
        ·
          refine ⟨22486797327050075641708151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14991198218033383761138767 22486797327050075641708151)
          ·
            refine ⟨33730195990575113462562227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22486797327050075641708151 33730195990575113462562227)
            ·
              refine ⟨50595293985862670193843341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33730195990575113462562227 50595293985862670193843341)
              ·
                refine ⟨18973235244698501322691253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50595293985862670193843341 18973235244698501322691253)
                ·
                  refine ⟨1778740804190484499002305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18973235244698501322691253 1778740804190484499002305)
                  ·
                    refine ⟨1334055603142863374251729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1778740804190484499002305 1334055603142863374251729)
                    ·
                      refine ⟨1000541702357147530688797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334055603142863374251729 1000541702357147530688797)
                      ·
                        rfl

theorem cell23_1948548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1948548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948548 prefixEnd_1948548 := by exact prefixLift 1948548
  have htrace : WordTrace (prefixWord ++ tailWord_1948548) baseStart_1948548 baseEnd_1948548 := by
    simpa [prefixWord, tailWord_1948548, baseEnd_1948548] using wordTrace_append hprefix tailTrace_1948548
  have hstable : (prefixWord ++ tailWord_1948548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948548).length < 2 ^ (prefixWord ++ tailWord_1948548).sum := by decide
  have hdescent : baseEnd_1948548 < baseStart_1948548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948594 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1948594 : Nat := 118140960795 + 1948594 * 2 ^ 59
def prefixEnd_1948594 : Nat := 4983230072969 + 3 ^ 40 * 1948594 * 2
def baseEnd_1948594 : Nat := 1000565322467254350713585

theorem tailTrace_1948594 : CollatzResearch.WordTrace tailWord_1948594 prefixEnd_1948594 1000565322467254350713585 := by
  unfold tailWord_1948594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767765475646051551319209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47380707935056137470184557 17767765475646051551319209)
  ·
    refine ⟨13325824106734538663489407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17767765475646051551319209 13325824106734538663489407)
    ·
      refine ⟨19988736160101807995234111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325824106734538663489407 19988736160101807995234111)
      ·
        refine ⟨29983104240152711992851167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19988736160101807995234111 29983104240152711992851167)
        ·
          refine ⟨44974656360229067989276751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29983104240152711992851167 44974656360229067989276751)
          ·
            refine ⟨67461984540343601983915127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44974656360229067989276751 67461984540343601983915127)
            ·
              refine ⟨101192976810515402975872691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67461984540343601983915127 101192976810515402975872691)
              ·
                refine ⟨151789465215773104463809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101192976810515402975872691 151789465215773104463809037)
                ·
                  refine ⟨56921049455914914173928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151789465215773104463809037 56921049455914914173928389)
                  ·
                    refine ⟨10672696772984046407611573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56921049455914914173928389 10672696772984046407611573)
                    ·
                      refine ⟨1000565322467254350713585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10672696772984046407611573 1000565322467254350713585)
                      ·
                        rfl

theorem cell23_1948594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1948594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948594 prefixEnd_1948594 := by exact prefixLift 1948594
  have htrace : WordTrace (prefixWord ++ tailWord_1948594) baseStart_1948594 baseEnd_1948594 := by
    simpa [prefixWord, tailWord_1948594, baseEnd_1948594] using wordTrace_append hprefix tailTrace_1948594
  have hstable : (prefixWord ++ tailWord_1948594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948594).length < 2 ^ (prefixWord ++ tailWord_1948594).sum := by decide
  have hdescent : baseEnd_1948594 < baseStart_1948594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948608 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2]
def baseStart_1948608 : Nat := 118140960795 + 1948608 * 2 ^ 59
def prefixEnd_1948608 : Nat := 4983230072969 + 3 ^ 40 * 1948608 * 2
def baseEnd_1948608 : Nat := 1000572511196417295938521

theorem tailTrace_1948608 : CollatzResearch.WordTrace tailWord_1948608 prefixEnd_1948608 1000572511196417295938521 := by
  unfold tailWord_1948608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35535786262266743298143239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47381048349688991064190985 35535786262266743298143239)
  ·
    refine ⟨53303679393400114947214859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35535786262266743298143239 53303679393400114947214859)
    ·
      refine ⟨79955519090100172420822289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53303679393400114947214859 79955519090100172420822289)
      ·
        refine ⟨59966639317575129315616717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79955519090100172420822289 59966639317575129315616717)
        ·
          refine ⟨22487489744090673493356269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59966639317575129315616717 22487489744090673493356269)
          ·
            refine ⟨8432808654034002560008601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22487489744090673493356269 8432808654034002560008601)
            ·
              refine ⟨6324606490525501920006451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8432808654034002560008601 6324606490525501920006451)
              ·
                refine ⟨9486909735788252880009677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324606490525501920006451 9486909735788252880009677)
                ·
                  refine ⟨3557591150920594830003629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9486909735788252880009677 3557591150920594830003629)
                  ·
                    refine ⟨1334096681595223061251361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3557591150920594830003629 1334096681595223061251361)
                    ·
                      refine ⟨1000572511196417295938521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334096681595223061251361 1000572511196417295938521)
                      ·
                        rfl

theorem cell23_1948608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_1948608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948608 prefixEnd_1948608 := by exact prefixLift 1948608
  have htrace : WordTrace (prefixWord ++ tailWord_1948608) baseStart_1948608 baseEnd_1948608 := by
    simpa [prefixWord, tailWord_1948608, baseEnd_1948608] using wordTrace_append hprefix tailTrace_1948608
  have hstable : (prefixWord ++ tailWord_1948608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948608).length < 2 ^ (prefixWord ++ tailWord_1948608).sum := by decide
  have hdescent : baseEnd_1948608 < baseStart_1948608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948624 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1948624 : Nat := 118140960795 + 1948624 * 2 ^ 59
def prefixEnd_1948624 : Nat := 4983230072969 + 3 ^ 40 * 1948624 * 2
def baseEnd_1948624 : Nat := 1000580726886889233338447

theorem tailTrace_1948624 : CollatzResearch.WordTrace tailWord_1948624 prefixEnd_1948624 1000580726886889233338447 := by
  unfold tailWord_1948624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536078046237760664434463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47381437394983680885912617 35536078046237760664434463)
  ·
    refine ⟨53304117069356640996651695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35536078046237760664434463 53304117069356640996651695)
    ·
      refine ⟨79956175604034961494977543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53304117069356640996651695 79956175604034961494977543)
      ·
        refine ⟨119934263406052442242466315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79956175604034961494977543 119934263406052442242466315)
        ·
          refine ⟨179901395109078663363699473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119934263406052442242466315 179901395109078663363699473)
          ·
            refine ⟨134926046331808997522774605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179901395109078663363699473 134926046331808997522774605)
            ·
              refine ⟨50597267374428374071040477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134926046331808997522774605 50597267374428374071040477)
              ·
                refine ⟨18973975265410640276640179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50597267374428374071040477 18973975265410640276640179)
                ·
                  refine ⟨28460962898115960414960269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18973975265410640276640179 28460962898115960414960269)
                  ·
                    refine ⟨10672861086793485155610101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28460962898115960414960269 10672861086793485155610101)
                    ·
                      refine ⟨1000580726886889233338447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10672861086793485155610101 1000580726886889233338447)
                      ·
                        rfl

theorem cell23_1948624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1948624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948624 prefixEnd_1948624 := by exact prefixLift 1948624
  have htrace : WordTrace (prefixWord ++ tailWord_1948624) baseStart_1948624 baseEnd_1948624 := by
    simpa [prefixWord, tailWord_1948624, baseEnd_1948624] using wordTrace_append hprefix tailTrace_1948624
  have hstable : (prefixWord ++ tailWord_1948624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948624).length < 2 ^ (prefixWord ++ tailWord_1948624).sum := by decide
  have hdescent : baseEnd_1948624 < baseStart_1948624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948655 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 4, 2]
def baseStart_1948655 : Nat := 118140960795 + 1948655 * 2 ^ 59
def prefixEnd_1948655 : Nat := 4983230072969 + 3 ^ 40 * 1948655 * 2
def baseEnd_1948655 : Nat := 1000596644787178612050805

theorem tailTrace_1948655 : CollatzResearch.WordTrace tailWord_1948655 prefixEnd_1948655 1000596644787178612050805 := by
  unfold tailWord_1948655
  simp only [CollatzResearch.WordTrace]
  refine ⟨71073286755363213623247419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47382191170242142415498279 71073286755363213623247419)
  ·
    refine ⟨106609930133044820434871129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71073286755363213623247419 106609930133044820434871129)
    ·
      refine ⟨79957447599783615326153347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106609930133044820434871129 79957447599783615326153347)
      ·
        refine ⟨119936171399675422989230021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79957447599783615326153347 119936171399675422989230021)
        ·
          refine ⟨22488032137439141810480629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119936171399675422989230021 22488032137439141810480629)
          ·
            refine ⟨2108253012884919544732559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22488032137439141810480629 2108253012884919544732559)
            ·
              refine ⟨3162379519327379317098839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108253012884919544732559 3162379519327379317098839)
              ·
                refine ⟨4743569278991068975648259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162379519327379317098839 4743569278991068975648259)
                ·
                  refine ⟨7115353918486603463472389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743569278991068975648259 7115353918486603463472389)
                  ·
                    refine ⟨1334128859716238149401073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115353918486603463472389 1334128859716238149401073)
                    ·
                      refine ⟨1000596644787178612050805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334128859716238149401073 1000596644787178612050805)
                      ·
                        rfl

theorem cell23_1948655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4, 2].length) (baseStart_1948655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948655 prefixEnd_1948655 := by exact prefixLift 1948655
  have htrace : WordTrace (prefixWord ++ tailWord_1948655) baseStart_1948655 baseEnd_1948655 := by
    simpa [prefixWord, tailWord_1948655, baseEnd_1948655] using wordTrace_append hprefix tailTrace_1948655
  have hstable : (prefixWord ++ tailWord_1948655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948655).length < 2 ^ (prefixWord ++ tailWord_1948655).sum := by decide
  have hdescent : baseEnd_1948655 < baseStart_1948655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948698 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_1948698 : Nat := 118140960795 + 1948698 * 2 ^ 59
def prefixEnd_1948698 : Nat := 4983230072969 + 3 ^ 40 * 1948698 * 2
def baseEnd_1948698 : Nat := 1000618724455321943813107

theorem tailTrace_1948698 : CollatzResearch.WordTrace tailWord_1948698 prefixEnd_1948698 1000618724455321943813107 := by
  unfold tailWord_1948698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768713773551857991765687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47383236729471621311375165 17768713773551857991765687)
  ·
    refine ⟨26653070660327786987648531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17768713773551857991765687 26653070660327786987648531)
    ·
      refine ⟨39979605990491680481472797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26653070660327786987648531 39979605990491680481472797)
      ·
        refine ⟨14992352246434380180552299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39979605990491680481472797 14992352246434380180552299)
        ·
          refine ⟨22488528369651570270828449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992352246434380180552299 22488528369651570270828449)
          ·
            refine ⟨16866396277238677703121337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22488528369651570270828449 16866396277238677703121337)
            ·
              refine ⟨12649797207929008277341003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16866396277238677703121337 12649797207929008277341003)
              ·
                refine ⟨18974695811893512416011505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649797207929008277341003 18974695811893512416011505)
                ·
                  refine ⟨14231021858920134312008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18974695811893512416011505 14231021858920134312008629)
                  ·
                    refine ⟨1334158299273762591750809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14231021858920134312008629 1334158299273762591750809)
                    ·
                      refine ⟨1000618724455321943813107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334158299273762591750809 1000618724455321943813107)
                      ·
                        rfl

theorem cell23_1948698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_1948698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948698 prefixEnd_1948698 := by exact prefixLift 1948698
  have htrace : WordTrace (prefixWord ++ tailWord_1948698) baseStart_1948698 baseEnd_1948698 := by
    simpa [prefixWord, tailWord_1948698, baseEnd_1948698] using wordTrace_append hprefix tailTrace_1948698
  have hstable : (prefixWord ++ tailWord_1948698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948698).length < 2 ^ (prefixWord ++ tailWord_1948698).sum := by decide
  have hdescent : baseEnd_1948698 < baseStart_1948698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948728 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1948728 : Nat := 118140960795 + 1948728 * 2 ^ 59
def prefixEnd_1948728 : Nat := 4983230072969 + 3 ^ 40 * 1948728 * 2
def baseEnd_1948728 : Nat := 1000634128874956826437969

theorem tailTrace_1948728 : CollatzResearch.WordTrace tailWord_1948728 prefixEnd_1948728 1000634128874956826437969 := by
  unfold tailWord_1948728
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537974642049373545327419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47383966189399164727103225 35537974642049373545327419)
  ·
    refine ⟨53306961963074060317991129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35537974642049373545327419 53306961963074060317991129)
    ·
      refine ⟨39980221472305545238493347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53306961963074060317991129 39980221472305545238493347)
      ·
        refine ⟨59970332208458317857740021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39980221472305545238493347 59970332208458317857740021)
        ·
          refine ⟨5622218644542967299163127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59970332208458317857740021 5622218644542967299163127)
          ·
            refine ⟨8433327966814450948744691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622218644542967299163127 8433327966814450948744691)
            ·
              refine ⟨12649991950221676423117037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433327966814450948744691 12649991950221676423117037)
              ·
                refine ⟨4743746981333128658668889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12649991950221676423117037 4743746981333128658668889)
                ·
                  refine ⟨3557810235999846494001667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743746981333128658668889 3557810235999846494001667)
                  ·
                    refine ⟨5336715353999769741002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557810235999846494001667 5336715353999769741002501)
                    ·
                      refine ⟨1000634128874956826437969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5336715353999769741002501 1000634128874956826437969)
                      ·
                        rfl

theorem cell23_1948728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1948728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948728 prefixEnd_1948728 := by exact prefixLift 1948728
  have htrace : WordTrace (prefixWord ++ tailWord_1948728) baseStart_1948728 baseEnd_1948728 := by
    simpa [prefixWord, tailWord_1948728, baseEnd_1948728] using wordTrace_append hprefix tailTrace_1948728
  have hstable : (prefixWord ++ tailWord_1948728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948728).length < 2 ^ (prefixWord ++ tailWord_1948728).sum := by decide
  have hdescent : baseEnd_1948728 < baseStart_1948728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948782 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1948782 : Nat := 118140960795 + 1948782 * 2 ^ 59
def prefixEnd_1948782 : Nat := 4983230072969 + 3 ^ 40 * 1948782 * 2
def baseEnd_1948782 : Nat := 1000661856830299615162721

theorem tailTrace_1948782 : CollatzResearch.WordTrace tailWord_1948782 prefixEnd_1948782 1000661856830299615162721 := by
  unfold tailWord_1948782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884739853237889289140075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47385279217268742875413733 8884739853237889289140075)
  ·
    refine ⟨13327109779856833933710113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8884739853237889289140075 13327109779856833933710113)
    ·
      refine ⟨9995332334892625450282585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13327109779856833933710113 9995332334892625450282585)
      ·
        refine ⟨7496499251169469087711939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9995332334892625450282585 7496499251169469087711939)
        ·
          refine ⟨11244748876754203631567909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496499251169469087711939 11244748876754203631567909)
          ·
            refine ⟨2108390414391413180918983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11244748876754203631567909 2108390414391413180918983)
            ·
              refine ⟨3162585621587119771378475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108390414391413180918983 3162585621587119771378475)
              ·
                refine ⟨4743878432380679657067713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162585621587119771378475 4743878432380679657067713)
                ·
                  refine ⟨3557908824285509742800785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743878432380679657067713 3557908824285509742800785)
                  ·
                    refine ⟨2668431618214132307100589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3557908824285509742800785 2668431618214132307100589)
                    ·
                      refine ⟨1000661856830299615162721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2668431618214132307100589 1000661856830299615162721)
                      ·
                        rfl

theorem cell23_1948782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1948782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948782 prefixEnd_1948782 := by exact prefixLift 1948782
  have htrace : WordTrace (prefixWord ++ tailWord_1948782) baseStart_1948782 baseEnd_1948782 := by
    simpa [prefixWord, tailWord_1948782, baseEnd_1948782] using wordTrace_append hprefix tailTrace_1948782
  have hstable : (prefixWord ++ tailWord_1948782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948782).length < 2 ^ (prefixWord ++ tailWord_1948782).sum := by decide
  have hdescent : baseEnd_1948782 < baseStart_1948782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948811 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 6]
def baseStart_1948811 : Nat := 118140960795 + 1948811 * 2 ^ 59
def prefixEnd_1948811 : Nat := 4983230072969 + 3 ^ 40 * 1948811 * 2
def baseEnd_1948811 : Nat := 333558915923093333900029

theorem tailTrace_1948811 : CollatzResearch.WordTrace tailWord_1948811 prefixEnd_1948811 333558915923093333900029 := by
  unfold tailWord_1948811
  simp only [CollatzResearch.WordTrace]
  refine ⟨71078976542798052265926287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47385984361865368177284191 71078976542798052265926287)
  ·
    refine ⟨106618464814197078398889431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71078976542798052265926287 106618464814197078398889431)
    ·
      refine ⟨159927697221295617598334147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106618464814197078398889431 159927697221295617598334147)
      ·
        refine ⟨239891545831943426397501221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159927697221295617598334147 239891545831943426397501221)
        ·
          refine ⟨44979664843489392449531479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239891545831943426397501221 44979664843489392449531479)
          ·
            refine ⟨67469497265234088674297219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44979664843489392449531479 67469497265234088674297219)
            ·
              refine ⟨101204245897851133011445829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67469497265234088674297219 101204245897851133011445829)
              ·
                refine ⟨18975796105847087439646093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101204245897851133011445829 18975796105847087439646093)
                ·
                  refine ⟨7115923539692657789867285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18975796105847087439646093 7115923539692657789867285)
                  ·
                    refine ⟨333558915923093333900029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7115923539692657789867285 333558915923093333900029)
                    ·
                      rfl

theorem cell23_1948811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_1948811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948811 prefixEnd_1948811 := by exact prefixLift 1948811
  have htrace : WordTrace (prefixWord ++ tailWord_1948811) baseStart_1948811 baseEnd_1948811 := by
    simpa [prefixWord, tailWord_1948811, baseEnd_1948811] using wordTrace_append hprefix tailTrace_1948811
  have hstable : (prefixWord ++ tailWord_1948811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948811).length < 2 ^ (prefixWord ++ tailWord_1948811).sum := by decide
  have hdescent : baseEnd_1948811 < baseStart_1948811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948855 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_1948855 : Nat := 118140960795 + 1948855 * 2 ^ 59
def prefixEnd_1948855 : Nat := 4983230072969 + 3 ^ 40 * 1948855 * 2
def baseEnd_1948855 : Nat := 1000699340918077829549885

theorem tailTrace_1948855 : CollatzResearch.WordTrace tailWord_1948855 prefixEnd_1948855 1000699340918077829549885 := by
  unfold tailWord_1948855
  simp only [CollatzResearch.WordTrace]
  refine ⟨71080581354638647780528019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47387054236425765187018679 71080581354638647780528019)
  ·
    refine ⟨106620872031957971670792029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71080581354638647780528019 106620872031957971670792029)
    ·
      refine ⟨39982827011984239376547011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106620872031957971670792029 39982827011984239376547011)
      ·
        refine ⟨59974240517976359064820517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39982827011984239376547011 59974240517976359064820517)
        ·
          refine ⟨11245170097120567324653847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59974240517976359064820517 11245170097120567324653847)
          ·
            refine ⟨16867755145680850986980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245170097120567324653847 16867755145680850986980771)
            ·
              refine ⟨25301632718521276480471157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16867755145680850986980771 25301632718521276480471157)
              ·
                refine ⟨2372028067361369670044171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25301632718521276480471157 2372028067361369670044171)
                ·
                  refine ⟨3558042101042054505066257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372028067361369670044171 3558042101042054505066257)
                  ·
                    refine ⟨2668531575781540878799693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558042101042054505066257 2668531575781540878799693)
                    ·
                      refine ⟨1000699340918077829549885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2668531575781540878799693 1000699340918077829549885)
                      ·
                        rfl

theorem cell23_1948855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_1948855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948855 prefixEnd_1948855 := by exact prefixLift 1948855
  have htrace : WordTrace (prefixWord ++ tailWord_1948855) baseStart_1948855 baseEnd_1948855 := by
    simpa [prefixWord, tailWord_1948855, baseEnd_1948855] using wordTrace_append hprefix tailTrace_1948855
  have hstable : (prefixWord ++ tailWord_1948855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948855).length < 2 ^ (prefixWord ++ tailWord_1948855).sum := by decide
  have hdescent : baseEnd_1948855 < baseStart_1948855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948865 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1948865 : Nat := 118140960795 + 1948865 * 2 ^ 59
def prefixEnd_1948865 : Nat := 4983230072969 + 3 ^ 40 * 1948865 * 2
def baseEnd_1948865 : Nat := 1000704475724622790424839

theorem tailTrace_1948865 : CollatzResearch.WordTrace tailWord_1948865 prefixEnd_1948865 1000704475724622790424839 := by
  unfold tailWord_1948865
  simp only [CollatzResearch.WordTrace]
  refine ⟨71080946084602419488392049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47387297389734946325594699 71080946084602419488392049)
  ·
    refine ⟨53310709563451814616294037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71080946084602419488392049 53310709563451814616294037)
    ·
      refine ⟨2498939510786803810138783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53310709563451814616294037 2498939510786803810138783)
      ·
        refine ⟨3748409266180205715208175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498939510786803810138783 3748409266180205715208175)
        ·
          refine ⟨5622613899270308572812263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748409266180205715208175 5622613899270308572812263)
          ·
            refine ⟨8433920848905462859218395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622613899270308572812263 8433920848905462859218395)
            ·
              refine ⟨12650881273358194288827593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433920848905462859218395 12650881273358194288827593)
              ·
                refine ⟨9488160955018645716620695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12650881273358194288827593 9488160955018645716620695)
                ·
                  refine ⟨14232241432527968574931043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488160955018645716620695 14232241432527968574931043)
                  ·
                    refine ⟨21348362148791952862396565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14232241432527968574931043 21348362148791952862396565)
                    ·
                      refine ⟨1000704475724622790424839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21348362148791952862396565 1000704475724622790424839)
                      ·
                        rfl

theorem cell23_1948865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1948865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948865 prefixEnd_1948865 := by exact prefixLift 1948865
  have htrace : WordTrace (prefixWord ++ tailWord_1948865) baseStart_1948865 baseEnd_1948865 := by
    simpa [prefixWord, tailWord_1948865, baseEnd_1948865] using wordTrace_append hprefix tailTrace_1948865
  have hstable : (prefixWord ++ tailWord_1948865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948865).length < 2 ^ (prefixWord ++ tailWord_1948865).sum := by decide
  have hdescent : baseEnd_1948865 < baseStart_1948865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948886 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1948886 : Nat := 118140960795 + 1948886 * 2 ^ 59
def prefixEnd_1948886 : Nat := 4983230072969 + 3 ^ 40 * 1948886 * 2
def baseEnd_1948886 : Nat := 1000715258818367208262243

theorem tailTrace_1948886 : CollatzResearch.WordTrace tailWord_1948886 prefixEnd_1948886 1000715258818367208262243 := by
  unfold tailWord_1948886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442607001095396254681657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47387808011684226716604341 4442607001095396254681657)
  ·
    refine ⟨3331955250821547191011243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4442607001095396254681657 3331955250821547191011243)
    ·
      refine ⟨4997932876232320786516865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331955250821547191011243 4997932876232320786516865)
      ·
        refine ⟨3748449657174240589887649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997932876232320786516865 3748449657174240589887649)
        ·
          refine ⟨2811337242880680442415737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3748449657174240589887649 2811337242880680442415737)
          ·
            refine ⟨2108502932160510331811803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811337242880680442415737 2108502932160510331811803)
            ·
              refine ⟨3162754398240765497717705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108502932160510331811803 3162754398240765497717705)
              ·
                refine ⟨2372065798680574123288279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162754398240765497717705 2372065798680574123288279)
                ·
                  refine ⟨3558098698020861184932419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372065798680574123288279 3558098698020861184932419)
                  ·
                    refine ⟨5337148047031291777398629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558098698020861184932419 5337148047031291777398629)
                    ·
                      refine ⟨1000715258818367208262243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5337148047031291777398629 1000715258818367208262243)
                      ·
                        rfl

theorem cell23_1948886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1948886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948886 prefixEnd_1948886 := by exact prefixLift 1948886
  have htrace : WordTrace (prefixWord ++ tailWord_1948886) baseStart_1948886 baseEnd_1948886 := by
    simpa [prefixWord, tailWord_1948886, baseEnd_1948886] using wordTrace_append hprefix tailTrace_1948886
  have hstable : (prefixWord ++ tailWord_1948886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948886).length < 2 ^ (prefixWord ++ tailWord_1948886).sum := by decide
  have hdescent : baseEnd_1948886 < baseStart_1948886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948942 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1948942 : Nat := 118140960795 + 1948942 * 2 ^ 59
def prefixEnd_1948942 : Nat := 4983230072969 + 3 ^ 40 * 1948942 * 2
def baseEnd_1948942 : Nat := 1000744013735018989161985

theorem tailTrace_1948942 : CollatzResearch.WordTrace tailWord_1948942 prefixEnd_1948942 1000744013735018989161985 := by
  unfold tailWord_1948942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885469313165432704868135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47389169670215641092630053 8885469313165432704868135)
  ·
    refine ⟨13328203969748149057302203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8885469313165432704868135 13328203969748149057302203)
    ·
      refine ⟨19992305954622223585953305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328203969748149057302203 19992305954622223585953305)
      ·
        refine ⟨14994229465966667689464979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19992305954622223585953305 14994229465966667689464979)
        ·
          refine ⟨22491344198950001534197469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994229465966667689464979 22491344198950001534197469)
          ·
            refine ⟨8434254074606250575324051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22491344198950001534197469 8434254074606250575324051)
            ·
              refine ⟨12651381111909375862986077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434254074606250575324051 12651381111909375862986077)
              ·
                refine ⟨4744267916966015948619779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12651381111909375862986077 4744267916966015948619779)
                ·
                  refine ⟨7116401875449023922929669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744267916966015948619779 7116401875449023922929669)
                  ·
                    refine ⟨1334325351646691985549313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116401875449023922929669 1334325351646691985549313)
                    ·
                      refine ⟨1000744013735018989161985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334325351646691985549313 1000744013735018989161985)
                      ·
                        rfl

theorem cell23_1948942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1948942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948942 prefixEnd_1948942 := by exact prefixLift 1948942
  have htrace : WordTrace (prefixWord ++ tailWord_1948942) baseStart_1948942 baseEnd_1948942 := by
    simpa [prefixWord, tailWord_1948942, baseEnd_1948942] using wordTrace_append hprefix tailTrace_1948942
  have hstable : (prefixWord ++ tailWord_1948942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948942).length < 2 ^ (prefixWord ++ tailWord_1948942).sum := by decide
  have hdescent : baseEnd_1948942 < baseStart_1948942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948993 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1948993 : Nat := 118140960795 + 1948993 * 2 ^ 59
def prefixEnd_1948993 : Nat := 4983230072969 + 3 ^ 40 * 1948993 * 2
def baseEnd_1948993 : Nat := 1000770201248398289624251

theorem tailTrace_1948993 : CollatzResearch.WordTrace tailWord_1948993 prefixEnd_1948993 1000770201248398289624251 := by
  unfold tailWord_1948993
  simp only [CollatzResearch.WordTrace]
  refine ⟨71085614628138697349051633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47390409752092464899367755 71085614628138697349051633)
  ·
    refine ⟨53314210971104023011788725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71085614628138697349051633 53314210971104023011788725)
    ·
      refine ⟨4998207278541002157355193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53314210971104023011788725 4998207278541002157355193)
      ·
        refine ⟨3748655458905751618016395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998207278541002157355193 3748655458905751618016395)
        ·
          refine ⟨5622983188358627427024593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748655458905751618016395 5622983188358627427024593)
          ·
            refine ⟨4217237391268970570268445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5622983188358627427024593 4217237391268970570268445)
            ·
              refine ⟨1581464021725863963850667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4217237391268970570268445 1581464021725863963850667)
              ·
                refine ⟨2372196032588795945776001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581464021725863963850667 2372196032588795945776001)
                ·
                  refine ⟨1779147024441596959332001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372196032588795945776001 1779147024441596959332001)
                  ·
                    refine ⟨1334360268331197719499001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779147024441596959332001 1334360268331197719499001)
                    ·
                      refine ⟨1000770201248398289624251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334360268331197719499001 1000770201248398289624251)
                      ·
                        rfl

theorem cell23_1948993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1948993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1948993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1948993 prefixEnd_1948993 := by exact prefixLift 1948993
  have htrace : WordTrace (prefixWord ++ tailWord_1948993) baseStart_1948993 baseEnd_1948993 := by
    simpa [prefixWord, tailWord_1948993, baseEnd_1948993] using wordTrace_append hprefix tailTrace_1948993
  have hstable : (prefixWord ++ tailWord_1948993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948993).length < 2 ^ (prefixWord ++ tailWord_1948993).sum := by decide
  have hdescent : baseEnd_1948993 < baseStart_1948993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949008 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_1949008 : Nat := 118140960795 + 1949008 * 2 ^ 59
def prefixEnd_1949008 : Nat := 4983230072969 + 3 ^ 40 * 1949008 * 2
def baseEnd_1949008 : Nat := 333592634486071910312227

theorem tailTrace_1949008 : CollatzResearch.WordTrace tailWord_1949008 prefixEnd_1949008 333592634486071910312227 := by
  unfold tailWord_1949008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35543080861542177455423839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47390774482056236607231785 35543080861542177455423839)
  ·
    refine ⟨53314621292313266183135759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35543080861542177455423839 53314621292313266183135759)
    ·
      refine ⟨79971931938469899274703639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53314621292313266183135759 79971931938469899274703639)
      ·
        refine ⟨119957897907704848912055459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79971931938469899274703639 119957897907704848912055459)
        ·
          refine ⟨179936846861557273368083189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119957897907704848912055459 179936846861557273368083189)
          ·
            refine ⟨16869079393270994378257799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179936846861557273368083189 16869079393270994378257799)
            ·
              refine ⟨25303619089906491567386699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16869079393270994378257799 25303619089906491567386699)
              ·
                refine ⟨37955428634859737351080049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25303619089906491567386699 37955428634859737351080049)
                ·
                  refine ⟨28466571476144803013310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37955428634859737351080049 28466571476144803013310037)
                  ·
                    refine ⟨333592634486071910312227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28466571476144803013310037 333592634486071910312227)
                    ·
                      rfl

theorem cell23_1949008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_1949008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949008 prefixEnd_1949008 := by exact prefixLift 1949008
  have htrace : WordTrace (prefixWord ++ tailWord_1949008) baseStart_1949008 baseEnd_1949008 := by
    simpa [prefixWord, tailWord_1949008, baseEnd_1949008] using wordTrace_append hprefix tailTrace_1949008
  have hstable : (prefixWord ++ tailWord_1949008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949008).length < 2 ^ (prefixWord ++ tailWord_1949008).sum := by decide
  have hdescent : baseEnd_1949008 < baseStart_1949008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949015 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1949015 : Nat := 118140960795 + 1949015 * 2 ^ 59
def prefixEnd_1949015 : Nat := 4983230072969 + 3 ^ 40 * 1949015 * 2
def baseEnd_1949015 : Nat := 1000781497822797203549149

theorem tailTrace_1949015 : CollatzResearch.WordTrace tailWord_1949015 prefixEnd_1949015 1000781497822797203549149 := by
  unfold tailWord_1949015
  simp only [CollatzResearch.WordTrace]
  refine ⟨71086417034058995106352499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47390944689372663404234999 71086417034058995106352499)
  ·
    refine ⟨106629625551088492659528749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71086417034058995106352499 106629625551088492659528749)
    ·
      refine ⟨39986109581658184747323281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106629625551088492659528749 39986109581658184747323281)
      ·
        refine ⟨29989582186243638560492461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39986109581658184747323281 29989582186243638560492461)
        ·
          refine ⟨11246093319841364460184673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29989582186243638560492461 11246093319841364460184673)
          ·
            refine ⟨8434569989881023345138505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11246093319841364460184673 8434569989881023345138505)
            ·
              refine ⟨6325927492410767508853879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8434569989881023345138505 6325927492410767508853879)
              ·
                refine ⟨9488891238616151263280819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325927492410767508853879 9488891238616151263280819)
                ·
                  refine ⟨14233336857924226894921229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488891238616151263280819 14233336857924226894921229)
                  ·
                    refine ⟨5337501321721585085595461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14233336857924226894921229 5337501321721585085595461)
                    ·
                      refine ⟨1000781497822797203549149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5337501321721585085595461 1000781497822797203549149)
                      ·
                        rfl

theorem cell23_1949015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1949015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949015 prefixEnd_1949015 := by exact prefixLift 1949015
  have htrace : WordTrace (prefixWord ++ tailWord_1949015) baseStart_1949015 baseEnd_1949015 := by
    simpa [prefixWord, tailWord_1949015, baseEnd_1949015] using wordTrace_append hprefix tailTrace_1949015
  have hstable : (prefixWord ++ tailWord_1949015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949015).length < 2 ^ (prefixWord ++ tailWord_1949015).sum := by decide
  have hdescent : baseEnd_1949015 < baseStart_1949015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949025 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1949025 : Nat := 118140960795 + 1949025 * 2 ^ 59
def prefixEnd_1949025 : Nat := 4983230072969 + 3 ^ 40 * 1949025 * 2
def baseEnd_1949025 : Nat := 333595544209780721474701

theorem tailTrace_1949025 : CollatzResearch.WordTrace tailWord_1949025 prefixEnd_1949025 333595544209780721474701 := by
  unfold tailWord_1949025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71086781764022766814216529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47391187842681844542811019 71086781764022766814216529)
  ·
    refine ⟨53315086323017075110662397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71086781764022766814216529 53315086323017075110662397)
    ·
      refine ⟨19993157371131403166498399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53315086323017075110662397 19993157371131403166498399)
      ·
        refine ⟨29989736056697104749747599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19993157371131403166498399 29989736056697104749747599)
        ·
          refine ⟨44984604085045657124621399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29989736056697104749747599 44984604085045657124621399)
          ·
            refine ⟨67476906127568485686932099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44984604085045657124621399 67476906127568485686932099)
            ·
              refine ⟨101215359191352728530398149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67476906127568485686932099 101215359191352728530398149)
              ·
                refine ⟨18977879848378636599449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101215359191352728530398149 18977879848378636599449653)
                ·
                  refine ⟨1779176235785497181198405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18977879848378636599449653 1779176235785497181198405)
                  ·
                    refine ⟨333595544209780721474701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779176235785497181198405 333595544209780721474701)
                    ·
                      rfl

theorem cell23_1949025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1949025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949025 prefixEnd_1949025 := by exact prefixLift 1949025
  have htrace : WordTrace (prefixWord ++ tailWord_1949025) baseStart_1949025 baseEnd_1949025 := by
    simpa [prefixWord, tailWord_1949025, baseEnd_1949025] using wordTrace_append hprefix tailTrace_1949025
  have hstable : (prefixWord ++ tailWord_1949025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949025).length < 2 ^ (prefixWord ++ tailWord_1949025).sum := by decide
  have hdescent : baseEnd_1949025 < baseStart_1949025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949092 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_1949092 : Nat := 118140960795 + 1949092 * 2 ^ 59
def prefixEnd_1949092 : Nat := 4983230072969 + 3 ^ 40 * 1949092 * 2
def baseEnd_1949092 : Nat := 1000821035833193402286295

theorem tailTrace_1949092 : CollatzResearch.WordTrace tailWord_1949092 prefixEnd_1949092 1000821035833193402286295 := by
  unfold tailWord_1949092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35544612727390018628452765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47392816969853358171270353 35544612727390018628452765)
  ·
    refine ⟨13329229772771256985669787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35544612727390018628452765 13329229772771256985669787)
    ·
      refine ⟨19993844659156885478504681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13329229772771256985669787 19993844659156885478504681)
      ·
        refine ⟨14995383494367664108878511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19993844659156885478504681 14995383494367664108878511)
        ·
          refine ⟨22493075241551496163317767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14995383494367664108878511 22493075241551496163317767)
          ·
            refine ⟨33739612862327244244976651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22493075241551496163317767 33739612862327244244976651)
            ·
              refine ⟨50609419293490866367464977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33739612862327244244976651 50609419293490866367464977)
              ·
                refine ⟨37957064470118149775598733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50609419293490866367464977 37957064470118149775598733)
                ·
                  refine ⟨14233899176294306165849525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37957064470118149775598733 14233899176294306165849525)
                  ·
                    refine ⟨1334428047777591203048393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14233899176294306165849525 1334428047777591203048393)
                    ·
                      refine ⟨1000821035833193402286295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334428047777591203048393 1000821035833193402286295)
                      ·
                        rfl

theorem cell23_1949092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_1949092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949092 prefixEnd_1949092 := by exact prefixLift 1949092
  have htrace : WordTrace (prefixWord ++ tailWord_1949092) baseStart_1949092 baseEnd_1949092 := by
    simpa [prefixWord, tailWord_1949092, baseEnd_1949092] using wordTrace_append hprefix tailTrace_1949092
  have hstable : (prefixWord ++ tailWord_1949092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949092).length < 2 ^ (prefixWord ++ tailWord_1949092).sum := by decide
  have hdescent : baseEnd_1949092 < baseStart_1949092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949116 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1949116 : Nat := 118140960795 + 1949116 * 2 ^ 59
def prefixEnd_1949116 : Nat := 4983230072969 + 3 ^ 40 * 1949116 * 2
def baseEnd_1949116 : Nat := 1000833359368901308386185

theorem tailTrace_1949116 : CollatzResearch.WordTrace tailWord_1949116 prefixEnd_1949116 1000833359368901308386185 := by
  unfold tailWord_1949116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545050403346544677889601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47393400537795392903852801 35545050403346544677889601)
  ·
    refine ⟨26658787802509908508417201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35545050403346544677889601 26658787802509908508417201)
    ·
      refine ⟨19994090851882431381312901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26658787802509908508417201 19994090851882431381312901)
      ·
        refine ⟨3748892034727955883996169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19994090851882431381312901 3748892034727955883996169)
        ·
          refine ⟨2811669026045966912997127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3748892034727955883996169 2811669026045966912997127)
          ·
            refine ⟨4217503539068950369495691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811669026045966912997127 4217503539068950369495691)
            ·
              refine ⟨6326255308603425554243537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217503539068950369495691 6326255308603425554243537)
              ·
                refine ⟨4744691481452569165682653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326255308603425554243537 4744691481452569165682653)
                ·
                  refine ⟨1779259305544713437130995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4744691481452569165682653 1779259305544713437130995)
                  ·
                    refine ⟨2668888958317070155696493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779259305544713437130995 2668888958317070155696493)
                    ·
                      refine ⟨1000833359368901308386185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2668888958317070155696493 1000833359368901308386185)
                      ·
                        rfl

theorem cell23_1949116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1949116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949116 prefixEnd_1949116 := by exact prefixLift 1949116
  have htrace : WordTrace (prefixWord ++ tailWord_1949116) baseStart_1949116 baseEnd_1949116 := by
    simpa [prefixWord, tailWord_1949116, baseEnd_1949116] using wordTrace_append hprefix tailTrace_1949116
  have hstable : (prefixWord ++ tailWord_1949116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949116).length < 2 ^ (prefixWord ++ tailWord_1949116).sum := by decide
  have hdescent : baseEnd_1949116 < baseStart_1949116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949132 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1949132 : Nat := 118140960795 + 1949132 * 2 ^ 59
def prefixEnd_1949132 : Nat := 4983230072969 + 3 ^ 40 * 1949132 * 2
def baseEnd_1949132 : Nat := 333613858353124415262037

theorem tailTrace_1949132 : CollatzResearch.WordTrace tailWord_1949132 prefixEnd_1949132 333613858353124415262037 := by
  unfold tailWord_1949132
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545342187317562044180825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47393789583090082725574433 35545342187317562044180825)
  ·
    refine ⟨26659006640488171533135619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35545342187317562044180825 26659006640488171533135619)
    ·
      refine ⟨39988509960732257299703429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26659006640488171533135619 39988509960732257299703429)
      ·
        refine ⟨7497845617637298243694393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39988509960732257299703429 7497845617637298243694393)
        ·
          refine ⟨5623384213227973682770795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497845617637298243694393 5623384213227973682770795)
          ·
            refine ⟨8435076319841960524156193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623384213227973682770795 8435076319841960524156193)
            ·
              refine ⟨6326307239881470393117145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435076319841960524156193 6326307239881470393117145)
              ·
                refine ⟨4744730429911102794837859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326307239881470393117145 4744730429911102794837859)
                ·
                  refine ⟨7117095644866654192256789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744730429911102794837859 7117095644866654192256789)
                  ·
                    refine ⟨333613858353124415262037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7117095644866654192256789 333613858353124415262037)
                    ·
                      rfl

theorem cell23_1949132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1949132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949132 prefixEnd_1949132 := by exact prefixLift 1949132
  have htrace : WordTrace (prefixWord ++ tailWord_1949132) baseStart_1949132 baseEnd_1949132 := by
    simpa [prefixWord, tailWord_1949132, baseEnd_1949132] using wordTrace_append hprefix tailTrace_1949132
  have hstable : (prefixWord ++ tailWord_1949132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949132).length < 2 ^ (prefixWord ++ tailWord_1949132).sum := by decide
  have hdescent : baseEnd_1949132 < baseStart_1949132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949145 : List Nat := [1, 2, 1, 2, 4, 3, 10]
def baseStart_1949145 : Nat := 118140960795 + 1949145 * 2 ^ 59
def prefixEnd_1949145 : Nat := 4983230072969 + 3 ^ 40 * 1949145 * 2
def baseEnd_1949145 : Nat := 12356151238368909813871

theorem tailTrace_1949145 : CollatzResearch.WordTrace tailWord_1949145 prefixEnd_1949145 12356151238368909813871 := by
  unfold tailWord_1949145
  simp only [CollatzResearch.WordTrace]
  refine ⟨71091158523588027308584889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47394105682392018205723259 71091158523588027308584889)
  ·
    refine ⟨53318368892691020481438667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71091158523588027308584889 53318368892691020481438667)
    ·
      refine ⟨79977553339036530722158001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53318368892691020481438667 79977553339036530722158001)
      ·
        refine ⟨59983165004277398041618501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79977553339036530722158001 59983165004277398041618501)
        ·
          refine ⟨11246843438302012132803469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59983165004277398041618501 11246843438302012132803469)
          ·
            refine ⟨4217566289363254549801301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11246843438302012132803469 4217566289363254549801301)
            ·
              refine ⟨12356151238368909813871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4217566289363254549801301 12356151238368909813871)
              ·
                rfl

theorem cell23_1949145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 10].length) (baseStart_1949145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949145 prefixEnd_1949145 := by exact prefixLift 1949145
  have htrace : WordTrace (prefixWord ++ tailWord_1949145) baseStart_1949145 baseEnd_1949145 := by
    simpa [prefixWord, tailWord_1949145, baseEnd_1949145] using wordTrace_append hprefix tailTrace_1949145
  have hstable : (prefixWord ++ tailWord_1949145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949145).length < 2 ^ (prefixWord ++ tailWord_1949145).sum := by decide
  have hdescent : baseEnd_1949145 < baseStart_1949145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949149 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1949149 : Nat := 118140960795 + 1949149 * 2 ^ 59
def prefixEnd_1949149 : Nat := 4983230072969 + 3 ^ 40 * 1949149 * 2
def baseEnd_1949149 : Nat := 333616768076833226424511

theorem tailTrace_1949149 : CollatzResearch.WordTrace tailWord_1949149 prefixEnd_1949149 333616768076833226424511 := by
  unfold tailWord_1949149
  simp only [CollatzResearch.WordTrace]
  refine ⟨71091304415573535991730501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47394202943715690661153667 71091304415573535991730501)
  ·
    refine ⟨13329619577920037998449469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71091304415573535991730501 13329619577920037998449469)
    ·
      refine ⟨4998607341720014249418551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13329619577920037998449469 4998607341720014249418551)
      ·
        refine ⟨7497911012580021374127827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998607341720014249418551 7497911012580021374127827)
        ·
          refine ⟨11246866518870032061191741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497911012580021374127827 11246866518870032061191741)
          ·
            refine ⟨4217574944576262022946903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11246866518870032061191741 4217574944576262022946903)
            ·
              refine ⟨6326362416864393034420355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217574944576262022946903 6326362416864393034420355)
              ·
                refine ⟨9489543625296589551630533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326362416864393034420355 9489543625296589551630533)
                ·
                  refine ⟨1779289429743110540930725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9489543625296589551630533 1779289429743110540930725)
                  ·
                    refine ⟨333616768076833226424511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779289429743110540930725 333616768076833226424511)
                    ·
                      rfl

theorem cell23_1949149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1949149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949149 prefixEnd_1949149 := by exact prefixLift 1949149
  have htrace : WordTrace (prefixWord ++ tailWord_1949149) baseStart_1949149 baseEnd_1949149 := by
    simpa [prefixWord, tailWord_1949149, baseEnd_1949149] using wordTrace_append hprefix tailTrace_1949149
  have hstable : (prefixWord ++ tailWord_1949149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949149).length < 2 ^ (prefixWord ++ tailWord_1949149).sum := by decide
  have hdescent : baseEnd_1949149 < baseStart_1949149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949166 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1949166 : Nat := 118140960795 + 1949166 * 2 ^ 59
def prefixEnd_1949166 : Nat := 4983230072969 + 3 ^ 40 * 1949166 * 2
def baseEnd_1949166 : Nat := 333619677800542037586985

theorem tailTrace_1949166 : CollatzResearch.WordTrace tailWord_1949166 prefixEnd_1949166 333619677800542037586985 := by
  unfold tailWord_1949166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886490557063993486887419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47394616304341298596732901 8886490557063993486887419)
  ·
    refine ⟨13329735835595990230331129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8886490557063993486887419 13329735835595990230331129)
    ·
      refine ⟨9997301876696992672748347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13329735835595990230331129 9997301876696992672748347)
      ·
        refine ⟨14995952815045489009122521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9997301876696992672748347 14995952815045489009122521)
        ·
          refine ⟨11246964611284116756841891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14995952815045489009122521 11246964611284116756841891)
          ·
            refine ⟨16870446916926175135262837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246964611284116756841891 16870446916926175135262837)
            ·
              refine ⟨1581604398461828918930891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16870446916926175135262837 1581604398461828918930891)
              ·
                refine ⟨2372406597692743378396337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581604398461828918930891 2372406597692743378396337)
                ·
                  refine ⟨1779304948269557533797253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2372406597692743378396337 1779304948269557533797253)
                  ·
                    refine ⟨333619677800542037586985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779304948269557533797253 333619677800542037586985)
                    ·
                      rfl

theorem cell23_1949166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1949166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949166 prefixEnd_1949166 := by exact prefixLift 1949166
  have htrace : WordTrace (prefixWord ++ tailWord_1949166) baseStart_1949166 baseEnd_1949166 := by
    simpa [prefixWord, tailWord_1949166, baseEnd_1949166] using wordTrace_append hprefix tailTrace_1949166
  have hstable : (prefixWord ++ tailWord_1949166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949166).length < 2 ^ (prefixWord ++ tailWord_1949166).sum := by decide
  have hdescent : baseEnd_1949166 < baseStart_1949166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949169 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_1949169 : Nat := 118140960795 + 1949169 * 2 ^ 59
def prefixEnd_1949169 : Nat := 4983230072969 + 3 ^ 40 * 1949169 * 2
def baseEnd_1949169 : Nat := 1000860573843589601023441

theorem tailTrace_1949169 : CollatzResearch.WordTrace tailWord_1949169 prefixEnd_1949169 1000860573843589601023441 := by
  unfold tailWord_1949169
  simp only [CollatzResearch.WordTrace]
  refine ⟨71092033875501079407458561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47394689250334052938305707 71092033875501079407458561)
  ·
    refine ⟨53319025406625809555593921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71092033875501079407458561 53319025406625809555593921)
    ·
      refine ⟨39989269054969357166695441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53319025406625809555593921 39989269054969357166695441)
      ·
        refine ⟨29991951791227017875021581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39989269054969357166695441 29991951791227017875021581)
        ·
          refine ⟨11246981921710131703133093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29991951791227017875021581 11246981921710131703133093)
          ·
            refine ⟨2108809110320649694337455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11246981921710131703133093 2108809110320649694337455)
            ·
              refine ⟨3163213665480974541506183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108809110320649694337455 3163213665480974541506183)
              ·
                refine ⟨4744820498221461812259275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163213665480974541506183 4744820498221461812259275)
                ·
                  refine ⟨7117230747332192718388913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744820498221461812259275 7117230747332192718388913)
                  ·
                    refine ⟨5337923060499144538791685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7117230747332192718388913 5337923060499144538791685)
                    ·
                      refine ⟨1000860573843589601023441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5337923060499144538791685 1000860573843589601023441)
                      ·
                        rfl

theorem cell23_1949169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_1949169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949169 prefixEnd_1949169 := by exact prefixLift 1949169
  have htrace : WordTrace (prefixWord ++ tailWord_1949169) baseStart_1949169 baseEnd_1949169 := by
    simpa [prefixWord, tailWord_1949169, baseEnd_1949169] using wordTrace_append hprefix tailTrace_1949169
  have hstable : (prefixWord ++ tailWord_1949169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949169).length < 2 ^ (prefixWord ++ tailWord_1949169).sum := by decide
  have hdescent : baseEnd_1949169 < baseStart_1949169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949173 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1949173 : Nat := 118140960795 + 1949173 * 2 ^ 59
def prefixEnd_1949173 : Nat := 4983230072969 + 3 ^ 40 * 1949173 * 2
def baseEnd_1949173 : Nat := 1000862627766207585373423

theorem tailTrace_1949173 : CollatzResearch.WordTrace tailWord_1949173 prefixEnd_1949173 1000862627766207585373423 := by
  unfold tailWord_1949173
  simp only [CollatzResearch.WordTrace]
  refine ⟨71092179767486588090604173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47394786511657725393736115 71092179767486588090604173)
  ·
    refine ⟨26659567412807470533976565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71092179767486588090604173 26659567412807470533976565)
    ·
      refine ⟨2499334444950700362560303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26659567412807470533976565 2499334444950700362560303)
      ·
        refine ⟨3749001667426050543840455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499334444950700362560303 3749001667426050543840455)
        ·
          refine ⟨5623502501139075815760683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749001667426050543840455 5623502501139075815760683)
          ·
            refine ⟨8435253751708613723641025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623502501139075815760683 8435253751708613723641025)
            ·
              refine ⟨6326440313781460292730769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435253751708613723641025 6326440313781460292730769)
              ·
                refine ⟨4744830235336095219548077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326440313781460292730769 4744830235336095219548077)
                ·
                  refine ⟨1779311338251035707330529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4744830235336095219548077 1779311338251035707330529)
                  ·
                    refine ⟨1334483503688276780497897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779311338251035707330529 1334483503688276780497897)
                    ·
                      refine ⟨1000862627766207585373423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334483503688276780497897 1000862627766207585373423)
                      ·
                        rfl

theorem cell23_1949173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1949173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949173 prefixEnd_1949173 := by exact prefixLift 1949173
  have htrace : WordTrace (prefixWord ++ tailWord_1949173) baseStart_1949173 baseEnd_1949173 := by
    simpa [prefixWord, tailWord_1949173, baseEnd_1949173] using wordTrace_append hprefix tailTrace_1949173
  have hstable : (prefixWord ++ tailWord_1949173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949173).length < 2 ^ (prefixWord ++ tailWord_1949173).sum := by decide
  have hdescent : baseEnd_1949173 < baseStart_1949173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949212 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1949212 : Nat := 118140960795 + 1949212 * 2 ^ 59
def prefixEnd_1949212 : Nat := 4983230072969 + 3 ^ 40 * 1949212 * 2
def baseEnd_1949212 : Nat := 1000882653511732932785743

theorem tailTrace_1949212 : CollatzResearch.WordTrace tailWord_1949212 prefixEnd_1949212 1000882653511732932785743 := by
  unfold tailWord_1949212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35546801107172648875636945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47395734809563531834182593 35546801107172648875636945)
  ·
    refine ⟨26660100830379486656727709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35546801107172648875636945 26660100830379486656727709)
    ·
      refine ⟨9997537811392307496272891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26660100830379486656727709 9997537811392307496272891)
      ·
        refine ⟨14996306717088461244409337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9997537811392307496272891 14996306717088461244409337)
        ·
          refine ⟨11247230037816345933307003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14996306717088461244409337 11247230037816345933307003)
          ·
            refine ⟨16870845056724518899960505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11247230037816345933307003 16870845056724518899960505)
            ·
              refine ⟨12653133792543389174970379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16870845056724518899960505 12653133792543389174970379)
              ·
                refine ⟨18979700688815083762455569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653133792543389174970379 18979700688815083762455569)
                ·
                  refine ⟨14234775516611312821841677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18979700688815083762455569 14234775516611312821841677)
                  ·
                    refine ⟨5338040818729242308190629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14234775516611312821841677 5338040818729242308190629)
                    ·
                      refine ⟨1000882653511732932785743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5338040818729242308190629 1000882653511732932785743)
                      ·
                        rfl

theorem cell23_1949212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1949212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949212 prefixEnd_1949212 := by exact prefixLift 1949212
  have htrace : WordTrace (prefixWord ++ tailWord_1949212) baseStart_1949212 baseEnd_1949212 := by
    simpa [prefixWord, tailWord_1949212, baseEnd_1949212] using wordTrace_append hprefix tailTrace_1949212
  have hstable : (prefixWord ++ tailWord_1949212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949212).length < 2 ^ (prefixWord ++ tailWord_1949212).sum := by decide
  have hdescent : baseEnd_1949212 < baseStart_1949212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949336 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1949336 : Nat := 118140960795 + 1949336 * 2 ^ 59
def prefixEnd_1949336 : Nat := 4983230072969 + 3 ^ 40 * 1949336 * 2
def baseEnd_1949336 : Nat := 1000946325112890447635173

theorem tailTrace_1949336 : CollatzResearch.WordTrace tailWord_1949336 prefixEnd_1949336 1000946325112890447635173 := by
  unfold tailWord_1949336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549062432948033464393931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47398749910597377952525241 35549062432948033464393931)
  ·
    refine ⟨53323593649422050196590897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35549062432948033464393931 53323593649422050196590897)
    ·
      refine ⟨39992695237066537647443173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53323593649422050196590897 39992695237066537647443173)
      ·
        refine ⟨7498630356949975808895595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39992695237066537647443173 7498630356949975808895595)
        ·
          refine ⟨11247945535424963713343393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498630356949975808895595 11247945535424963713343393)
          ·
            refine ⟨8435959151568722785007545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11247945535424963713343393 8435959151568722785007545)
            ·
              refine ⟨6326969363676542088755659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435959151568722785007545 6326969363676542088755659)
              ·
                refine ⟨9490454045514813133133489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326969363676542088755659 9490454045514813133133489)
                ·
                  refine ⟨7117840534136109849850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9490454045514813133133489 7117840534136109849850117)
                  ·
                    refine ⟨1334595100150520596846897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7117840534136109849850117 1334595100150520596846897)
                    ·
                      refine ⟨1000946325112890447635173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334595100150520596846897 1000946325112890447635173)
                      ·
                        rfl

theorem cell23_1949336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1949336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949336 prefixEnd_1949336 := by exact prefixLift 1949336
  have htrace : WordTrace (prefixWord ++ tailWord_1949336) baseStart_1949336 baseEnd_1949336 := by
    simpa [prefixWord, tailWord_1949336, baseEnd_1949336] using wordTrace_append hprefix tailTrace_1949336
  have hstable : (prefixWord ++ tailWord_1949336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949336).length < 2 ^ (prefixWord ++ tailWord_1949336).sum := by decide
  have hdescent : baseEnd_1949336 < baseStart_1949336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 9, 2]
def baseStart_1949379 : Nat := 118140960795 + 1949379 * 2 ^ 59
def prefixEnd_1949379 : Nat := 4983230072969 + 3 ^ 40 * 1949379 * 2
def baseEnd_1949379 : Nat := 1000968404781033779397475

theorem tailTrace_1949379 : CollatzResearch.WordTrace tailWord_1949379 prefixEnd_1949379 1000968404781033779397475 := by
  unfold tailWord_1949379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71099693204740285272603191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47399795469826856848402127 71099693204740285272603191)
  ·
    refine ⟨106649539807110427908904787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71099693204740285272603191 106649539807110427908904787)
    ·
      refine ⟨159974309710665641863357181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106649539807110427908904787 159974309710665641863357181)
      ·
        refine ⟨59990366141499615698758943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159974309710665641863357181 59990366141499615698758943)
        ·
          refine ⟨89985549212249423548138415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59990366141499615698758943 89985549212249423548138415)
          ·
            refine ⟨134978323818374135322207623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89985549212249423548138415 134978323818374135322207623)
            ·
              refine ⟨202467485727561202983311435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134978323818374135322207623 202467485727561202983311435)
              ·
                refine ⟨303701228591341804474967153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202467485727561202983311435 303701228591341804474967153)
                ·
                  refine ⟨227775921443506353356225365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303701228591341804474967153 227775921443506353356225365)
                  ·
                    refine ⟨1334624539708045039196633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227775921443506353356225365 1334624539708045039196633)
                    ·
                      refine ⟨1000968404781033779397475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334624539708045039196633 1000968404781033779397475)
                      ·
                        rfl

theorem cell23_1949379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_1949379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949379 prefixEnd_1949379 := by exact prefixLift 1949379
  have htrace : WordTrace (prefixWord ++ tailWord_1949379) baseStart_1949379 baseEnd_1949379 := by
    simpa [prefixWord, tailWord_1949379, baseEnd_1949379] using wordTrace_append hprefix tailTrace_1949379
  have hstable : (prefixWord ++ tailWord_1949379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949379).length < 2 ^ (prefixWord ++ tailWord_1949379).sum := by decide
  have hdescent : baseEnd_1949379 < baseStart_1949379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949380 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1949380 : Nat := 118140960795 + 1949380 * 2 ^ 59
def prefixEnd_1949380 : Nat := 4983230072969 + 3 ^ 40 * 1949380 * 2
def baseEnd_1949380 : Nat := 333656306087229425161657

theorem tailTrace_1949380 : CollatzResearch.WordTrace tailWord_1949380 prefixEnd_1949380 333656306087229425161657 := by
  unfold tailWord_1949380
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549864838868331221694797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47399819785157774962259729 35549864838868331221694797)
  ·
    refine ⟨13331199314575624208135549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35549864838868331221694797 13331199314575624208135549)
    ·
      refine ⟨4999199742965859078050831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13331199314575624208135549 4999199742965859078050831)
      ·
        refine ⟨7498799614448788617076247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999199742965859078050831 7498799614448788617076247)
        ·
          refine ⟨11248199421673182925614371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498799614448788617076247 11248199421673182925614371)
          ·
            refine ⟨16872299132509774388421557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248199421673182925614371 16872299132509774388421557)
            ·
              refine ⟨1581778043672791348914521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16872299132509774388421557 1581778043672791348914521)
              ·
                refine ⟨1186333532754593511685891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581778043672791348914521 1186333532754593511685891)
                ·
                  refine ⟨1779500299131890267528837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186333532754593511685891 1779500299131890267528837)
                  ·
                    refine ⟨333656306087229425161657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779500299131890267528837 333656306087229425161657)
                    ·
                      rfl

theorem cell23_1949380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1949380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949380 prefixEnd_1949380 := by exact prefixLift 1949380
  have htrace : WordTrace (prefixWord ++ tailWord_1949380) baseStart_1949380 baseEnd_1949380 := by
    simpa [prefixWord, tailWord_1949380, baseEnd_1949380] using wordTrace_append hprefix tailTrace_1949380
  have hstable : (prefixWord ++ tailWord_1949380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949380).length < 2 ^ (prefixWord ++ tailWord_1949380).sum := by decide
  have hdescent : baseEnd_1949380 < baseStart_1949380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949413 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1949413 : Nat := 118140960795 + 1949413 * 2 ^ 59
def prefixEnd_1949413 : Nat := 4983230072969 + 3 ^ 40 * 1949413 * 2
def baseEnd_1949413 : Nat := 1000985863123286646372319

theorem tailTrace_1949413 : CollatzResearch.WordTrace tailWord_1949413 prefixEnd_1949413 1000985863123286646372319 := by
  unfold tailWord_1949413
  simp only [CollatzResearch.WordTrace]
  refine ⟨71100933286617109079340893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47400622191078072719560595 71100933286617109079340893)
  ·
    refine ⟨26662849982481415904752835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71100933286617109079340893 26662849982481415904752835)
    ·
      refine ⟨39994274973722123857129253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26662849982481415904752835 39994274973722123857129253)
      ·
        refine ⟨7498926557572898223211735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39994274973722123857129253 7498926557572898223211735)
        ·
          refine ⟨11248389836359347334817603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498926557572898223211735 11248389836359347334817603)
          ·
            refine ⟨16872584754539021002226405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248389836359347334817603 16872584754539021002226405)
            ·
              refine ⟨3163609641476066437917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16872584754539021002226405 3163609641476066437917451)
              ·
                refine ⟨4745414462214099656876177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163609641476066437917451 4745414462214099656876177)
                ·
                  refine ⟨3559060846660574742657133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745414462214099656876177 3559060846660574742657133)
                  ·
                    refine ⟨1334647817497715528496425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559060846660574742657133 1334647817497715528496425)
                    ·
                      refine ⟨1000985863123286646372319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334647817497715528496425 1000985863123286646372319)
                      ·
                        rfl

theorem cell23_1949413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1949413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949413 prefixEnd_1949413 := by exact prefixLift 1949413
  have htrace : WordTrace (prefixWord ++ tailWord_1949413) baseStart_1949413 baseEnd_1949413 := by
    simpa [prefixWord, tailWord_1949413, baseEnd_1949413] using wordTrace_append hprefix tailTrace_1949413
  have hstable : (prefixWord ++ tailWord_1949413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949413).length < 2 ^ (prefixWord ++ tailWord_1949413).sum := by decide
  have hdescent : baseEnd_1949413 < baseStart_1949413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949419 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 6, 4]
def baseStart_1949419 : Nat := 118140960795 + 1949419 * 2 ^ 59
def prefixEnd_1949419 : Nat := 4983230072969 + 3 ^ 40 * 1949419 * 2
def baseEnd_1949419 : Nat := 333662981335737874299097

theorem tailTrace_1949419 : CollatzResearch.WordTrace tailWord_1949419 prefixEnd_1949419 333662981335737874299097 := by
  unfold tailWord_1949419
  simp only [CollatzResearch.WordTrace]
  refine ⟨71101152124595372104059311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47400768083063581402706207 71101152124595372104059311)
  ·
    refine ⟨106651728186893058156088967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71101152124595372104059311 106651728186893058156088967)
    ·
      refine ⟨159977592280339587234133451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106651728186893058156088967 159977592280339587234133451)
      ·
        refine ⟨239966388420509380851200177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159977592280339587234133451 239966388420509380851200177)
        ·
          refine ⟨179974791315382035638400133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239966388420509380851200177 179974791315382035638400133)
          ·
            refine ⟨33745273371634131682200025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179974791315382035638400133 33745273371634131682200025)
            ·
              refine ⟨25308955028725598761650019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33745273371634131682200025 25308955028725598761650019)
              ·
                refine ⟨37963432543088398142475029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25308955028725598761650019 37963432543088398142475029)
                ·
                  refine ⟨1779535900457268662928517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37963432543088398142475029 1779535900457268662928517)
                  ·
                    refine ⟨333662981335737874299097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779535900457268662928517 333662981335737874299097)
                    ·
                      rfl

theorem cell23_1949419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 4].length) (baseStart_1949419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949419 prefixEnd_1949419 := by exact prefixLift 1949419
  have htrace : WordTrace (prefixWord ++ tailWord_1949419) baseStart_1949419 baseEnd_1949419 := by
    simpa [prefixWord, tailWord_1949419, baseEnd_1949419] using wordTrace_append hprefix tailTrace_1949419
  have hstable : (prefixWord ++ tailWord_1949419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949419).length < 2 ^ (prefixWord ++ tailWord_1949419).sum := by decide
  have hdescent : baseEnd_1949419 < baseStart_1949419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949466 : List Nat := [3, 1, 1, 3, 2, 3, 3, 7]
def baseStart_1949466 : Nat := 118140960795 + 1949466 * 2 ^ 59
def prefixEnd_1949466 : Nat := 4983230072969 + 3 ^ 40 * 1949466 * 2
def baseEnd_1949466 : Nat := 37074558429554627370725

theorem tailTrace_1949466 : CollatzResearch.WordTrace tailWord_1949466 prefixEnd_1949466 37074558429554627370725 := by
  unfold tailWord_1949466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775716588856274782755063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47401910903616732754013501 17775716588856274782755063)
  ·
    refine ⟨26663574883284412174132595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775716588856274782755063 26663574883284412174132595)
    ·
      refine ⟨39995362324926618261198893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663574883284412174132595 39995362324926618261198893)
      ·
        refine ⟨14998260871847481847949585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39995362324926618261198893 14998260871847481847949585)
        ·
          refine ⟨11248695653885611385962189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14998260871847481847949585 11248695653885611385962189)
          ·
            refine ⟨4218260870207104269735821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11248695653885611385962189 4218260870207104269735821)
            ·
              refine ⟨1581847826327664101150933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4218260870207104269735821 1581847826327664101150933)
              ·
                refine ⟨37074558429554627370725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1581847826327664101150933 37074558429554627370725)
                ·
                  rfl

theorem cell23_1949466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_1949466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949466 prefixEnd_1949466 := by exact prefixLift 1949466
  have htrace : WordTrace (prefixWord ++ tailWord_1949466) baseStart_1949466 baseEnd_1949466 := by
    simpa [prefixWord, tailWord_1949466, baseEnd_1949466] using wordTrace_append hprefix tailTrace_1949466
  have hstable : (prefixWord ++ tailWord_1949466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949466).length < 2 ^ (prefixWord ++ tailWord_1949466).sum := by decide
  have hdescent : baseEnd_1949466 < baseStart_1949466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949477 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_1949477 : Nat := 118140960795 + 1949477 * 2 ^ 59
def prefixEnd_1949477 : Nat := 4983230072969 + 3 ^ 40 * 1949477 * 2
def baseEnd_1949477 : Nat := 1001018725885174395972025

theorem tailTrace_1949477 : CollatzResearch.WordTrace tailWord_1949477 prefixEnd_1949477 1001018725885174395972025 := by
  unfold tailWord_1949477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71103267558385248009670685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47402178372256832006447123 71103267558385248009670685)
  ·
    refine ⟨26663725334394468003626507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71103267558385248009670685 26663725334394468003626507)
    ·
      refine ⟨39995588001591702005439761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663725334394468003626507 39995588001591702005439761)
      ·
        refine ⟨29996691001193776504079821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39995588001591702005439761 29996691001193776504079821)
        ·
          refine ⟨11248759125447666189029933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29996691001193776504079821 11248759125447666189029933)
          ·
            refine ⟨4218284672042874820886225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11248759125447666189029933 4218284672042874820886225)
            ·
              refine ⟨3163713504032156115664669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218284672042874820886225 3163713504032156115664669)
              ·
                refine ⟨1186392564012058543374251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163713504032156115664669 1186392564012058543374251)
                ·
                  refine ⟨1779588846018087815061377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186392564012058543374251 1779588846018087815061377)
                  ·
                    refine ⟨1334691634513565861296033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779588846018087815061377 1334691634513565861296033)
                    ·
                      refine ⟨1001018725885174395972025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334691634513565861296033 1001018725885174395972025)
                      ·
                        rfl

theorem cell23_1949477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_1949477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949477 prefixEnd_1949477 := by exact prefixLift 1949477
  have htrace : WordTrace (prefixWord ++ tailWord_1949477) baseStart_1949477 baseEnd_1949477 := by
    simpa [prefixWord, tailWord_1949477, baseEnd_1949477] using wordTrace_append hprefix tailTrace_1949477
  have hstable : (prefixWord ++ tailWord_1949477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949477).length < 2 ^ (prefixWord ++ tailWord_1949477).sum := by decide
  have hdescent : baseEnd_1949477 < baseStart_1949477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949480 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1949480 : Nat := 118140960795 + 1949480 * 2 ^ 59
def prefixEnd_1949480 : Nat := 4983230072969 + 3 ^ 40 * 1949480 * 2
def baseEnd_1949480 : Nat := 1001020266327137884234511

theorem tailTrace_1949480 : CollatzResearch.WordTrace tailWord_1949480 prefixEnd_1949480 1001020266327137884234511 := by
  unfold tailWord_1949480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551688488687189761014947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47402251318249586348019929 35551688488687189761014947)
  ·
    refine ⟨53327532733030784641522421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35551688488687189761014947 53327532733030784641522421)
    ·
      refine ⟨4999456193721636060142727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53327532733030784641522421 4999456193721636060142727)
      ·
        refine ⟨7499184290582454090214091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999456193721636060142727 7499184290582454090214091)
        ·
          refine ⟨11248776435873681135321137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499184290582454090214091 11248776435873681135321137)
          ·
            refine ⟨8436582326905260851490853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11248776435873681135321137 8436582326905260851490853)
            ·
              refine ⟨1581859186294736409654535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8436582326905260851490853 1581859186294736409654535)
              ·
                refine ⟨2372788779442104614481803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581859186294736409654535 2372788779442104614481803)
                ·
                  refine ⟨3559183169163156921722705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372788779442104614481803 3559183169163156921722705)
                  ·
                    refine ⟨2669387376872367691292029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559183169163156921722705 2669387376872367691292029)
                    ·
                      refine ⟨1001020266327137884234511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2669387376872367691292029 1001020266327137884234511)
                      ·
                        rfl

theorem cell23_1949480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1949480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949480 prefixEnd_1949480 := by exact prefixLift 1949480
  have htrace : WordTrace (prefixWord ++ tailWord_1949480) baseStart_1949480 baseEnd_1949480 := by
    simpa [prefixWord, tailWord_1949480, baseEnd_1949480] using wordTrace_append hprefix tailTrace_1949480
  have hstable : (prefixWord ++ tailWord_1949480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949480).length < 2 ^ (prefixWord ++ tailWord_1949480).sum := by decide
  have hdescent : baseEnd_1949480 < baseStart_1949480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949494 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1949494 : Nat := 118140960795 + 1949494 * 2 ^ 59
def prefixEnd_1949494 : Nat := 4983230072969 + 3 ^ 40 * 1949494 * 2
def baseEnd_1949494 : Nat := 1001027455056300829459447

theorem tailTrace_1949494 : CollatzResearch.WordTrace tailWord_1949494 prefixEnd_1949494 1001027455056300829459447 := by
  unfold tailWord_1949494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443992974957728744564971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47402591732882439942026357 4443992974957728744564971)
  ·
    refine ⟨6665989462436593116847457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443992974957728744564971 6665989462436593116847457)
    ·
      refine ⟨4999492096827444837635593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6665989462436593116847457 4999492096827444837635593)
      ·
        refine ⟨3749619072620583628226695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4999492096827444837635593 3749619072620583628226695)
        ·
          refine ⟨5624428608930875442340043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749619072620583628226695 5624428608930875442340043)
          ·
            refine ⟨8436642913396313163510065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624428608930875442340043 8436642913396313163510065)
            ·
              refine ⟨6327482185047234872632549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436642913396313163510065 6327482185047234872632549)
              ·
                refine ⟨1186402909696356538618603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6327482185047234872632549 1186402909696356538618603)
                ·
                  refine ⟨1779604364544534807927905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186402909696356538618603 1779604364544534807927905)
                  ·
                    refine ⟨1334703273408401105945929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779604364544534807927905 1334703273408401105945929)
                    ·
                      refine ⟨1001027455056300829459447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334703273408401105945929 1001027455056300829459447)
                      ·
                        rfl

theorem cell23_1949494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1949494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949494 prefixEnd_1949494 := by exact prefixLift 1949494
  have htrace : WordTrace (prefixWord ++ tailWord_1949494) baseStart_1949494 baseEnd_1949494 := by
    simpa [prefixWord, tailWord_1949494, baseEnd_1949494] using wordTrace_append hprefix tailTrace_1949494
  have hstable : (prefixWord ++ tailWord_1949494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949494).length < 2 ^ (prefixWord ++ tailWord_1949494).sum := by decide
  have hdescent : baseEnd_1949494 < baseStart_1949494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949509 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1949509 : Nat := 118140960795 + 1949509 * 2 ^ 59
def prefixEnd_1949509 : Nat := 4983230072969 + 3 ^ 40 * 1949509 * 2
def baseEnd_1949509 : Nat := 333678385755372756923959

theorem tailTrace_1949509 : CollatzResearch.WordTrace tailWord_1949509 prefixEnd_1949509 333678385755372756923959 := by
  unfold tailWord_1949509
  simp only [CollatzResearch.WordTrace]
  refine ⟨71104434694269317474835581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47402956462846211649890387 71104434694269317474835581)
  ·
    refine ⟨26664163010350994053063343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71104434694269317474835581 26664163010350994053063343)
    ·
      refine ⟨39996244515526491079595015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26664163010350994053063343 39996244515526491079595015)
      ·
        refine ⟨59994366773289736619392523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39996244515526491079595015 59994366773289736619392523)
        ·
          refine ⟨89991550159934604929088785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59994366773289736619392523 89991550159934604929088785)
          ·
            refine ⟨67493662619950953696816589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89991550159934604929088785 67493662619950953696816589)
            ·
              refine ⟨25310123482481607636306221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67493662619950953696816589 25310123482481607636306221)
              ·
                refine ⟨9491296305930602863614833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25310123482481607636306221 9491296305930602863614833)
                ·
                  refine ⟨7118472229447952147711125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491296305930602863614833 7118472229447952147711125)
                  ·
                    refine ⟨333678385755372756923959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7118472229447952147711125 333678385755372756923959)
                    ·
                      rfl

theorem cell23_1949509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1949509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949509 prefixEnd_1949509 := by exact prefixLift 1949509
  have htrace : WordTrace (prefixWord ++ tailWord_1949509) baseStart_1949509 baseEnd_1949509 := by
    simpa [prefixWord, tailWord_1949509, baseEnd_1949509] using wordTrace_append hprefix tailTrace_1949509
  have hstable : (prefixWord ++ tailWord_1949509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949509).length < 2 ^ (prefixWord ++ tailWord_1949509).sum := by decide
  have hdescent : baseEnd_1949509 < baseStart_1949509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949536 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1949536 : Nat := 118140960795 + 1949536 * 2 ^ 59
def prefixEnd_1949536 : Nat := 4983230072969 + 3 ^ 40 * 1949536 * 2
def baseEnd_1949536 : Nat := 1001049021243789665134253

theorem tailTrace_1949536 : CollatzResearch.WordTrace tailWord_1949536 prefixEnd_1949536 1001049021243789665134253 := by
  unfold tailWord_1949536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552709732585750543034231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47403612976781000724045641 35552709732585750543034231)
  ·
    refine ⟨53329064598878625814551347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35552709732585750543034231 53329064598878625814551347)
    ·
      refine ⟨79993596898317938721827021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53329064598878625814551347 79993596898317938721827021)
      ·
        refine ⟨29997598836869227020685133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79993596898317938721827021 29997598836869227020685133)
        ·
          refine ⟨11249099563825960132756925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29997598836869227020685133 11249099563825960132756925)
          ·
            refine ⟨4218412336434735049783847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11249099563825960132756925 4218412336434735049783847)
            ·
              refine ⟨6327618504652102574675771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218412336434735049783847 6327618504652102574675771)
              ·
                refine ⟨9491427756978153862013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327618504652102574675771 9491427756978153862013657)
                ·
                  refine ⟨7118570817733615396510243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491427756978153862013657 7118570817733615396510243)
                  ·
                    refine ⟨10677856226600423094765365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118570817733615396510243 10677856226600423094765365)
                    ·
                      refine ⟨1001049021243789665134253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10677856226600423094765365 1001049021243789665134253)
                      ·
                        rfl

theorem cell23_1949536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1949536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949536 prefixEnd_1949536 := by exact prefixLift 1949536
  have htrace : WordTrace (prefixWord ++ tailWord_1949536) baseStart_1949536 baseEnd_1949536 := by
    simpa [prefixWord, tailWord_1949536, baseEnd_1949536] using wordTrace_append hprefix tailTrace_1949536
  have hstable : (prefixWord ++ tailWord_1949536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949536).length < 2 ^ (prefixWord ++ tailWord_1949536).sum := by decide
  have hdescent : baseEnd_1949536 < baseStart_1949536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949579 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_1949579 : Nat := 118140960795 + 1949579 * 2 ^ 59
def prefixEnd_1949579 : Nat := 4983230072969 + 3 ^ 40 * 1949579 * 2
def baseEnd_1949579 : Nat := 1001071100911932996896555

theorem tailTrace_1949579 : CollatzResearch.WordTrace tailWord_1949579 prefixEnd_1949579 1001071100911932996896555 := by
  unfold tailWord_1949579
  simp only [CollatzResearch.WordTrace]
  refine ⟨71106987804015719429883791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47404658536010479619922527 71106987804015719429883791)
  ·
    refine ⟨106660481706023579144825687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71106987804015719429883791 106660481706023579144825687)
    ·
      refine ⟨159990722559035368717238531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106660481706023579144825687 159990722559035368717238531)
      ·
        refine ⟨239986083838553053075857797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159990722559035368717238531 239986083838553053075857797)
        ·
          refine ⟨44997390719728697451723337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239986083838553053075857797 44997390719728697451723337)
          ·
            refine ⟨33748043039796523088792503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44997390719728697451723337 33748043039796523088792503)
            ·
              refine ⟨50622064559694784633188755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33748043039796523088792503 50622064559694784633188755)
              ·
                refine ⟨75933096839542176949783133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50622064559694784633188755 75933096839542176949783133)
                ·
                  refine ⟨28474911314828316356168675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75933096839542176949783133 28474911314828316356168675)
                  ·
                    refine ⟨42712366972242474534253013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28474911314828316356168675 42712366972242474534253013)
                    ·
                      refine ⟨1001071100911932996896555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42712366972242474534253013 1001071100911932996896555)
                      ·
                        rfl

theorem cell23_1949579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_1949579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949579 prefixEnd_1949579 := by exact prefixLift 1949579
  have htrace : WordTrace (prefixWord ++ tailWord_1949579) baseStart_1949579 baseEnd_1949579 := by
    simpa [prefixWord, tailWord_1949579, baseEnd_1949579] using wordTrace_append hprefix tailTrace_1949579
  have hstable : (prefixWord ++ tailWord_1949579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949579).length < 2 ^ (prefixWord ++ tailWord_1949579).sum := by decide
  have hdescent : baseEnd_1949579 < baseStart_1949579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949607 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 5]
def baseStart_1949607 : Nat := 118140960795 + 1949607 * 2 ^ 59
def prefixEnd_1949607 : Nat := 4983230072969 + 3 ^ 40 * 1949607 * 2
def baseEnd_1949607 : Nat := 111231719818917654149603

theorem tailTrace_1949607 : CollatzResearch.WordTrace tailWord_1949607 prefixEnd_1949607 111231719818917654149603 := by
  unfold tailWord_1949607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71108009047914280211903075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47405339365276186807935383 71108009047914280211903075)
  ·
    refine ⟨106662013571871420317854613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71108009047914280211903075 106662013571871420317854613)
    ·
      refine ⟨4999781886181472827399435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106662013571871420317854613 4999781886181472827399435)
      ·
        refine ⟨7499672829272209241099153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999781886181472827399435 7499672829272209241099153)
        ·
          refine ⟨5624754621954156930824365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499672829272209241099153 5624754621954156930824365)
          ·
            refine ⟨2109282983232808849059137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5624754621954156930824365 2109282983232808849059137)
            ·
              refine ⟨1581962237424606636794353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109282983232808849059137 1581962237424606636794353)
              ·
                refine ⟨1186471678068454977595765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581962237424606636794353 1186471678068454977595765)
                ·
                  refine ⟨111231719818917654149603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1186471678068454977595765 111231719818917654149603)
                  ·
                    rfl

theorem cell23_1949607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 5].length) (baseStart_1949607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949607 prefixEnd_1949607 := by exact prefixLift 1949607
  have htrace : WordTrace (prefixWord ++ tailWord_1949607) baseStart_1949607 baseEnd_1949607 := by
    simpa [prefixWord, tailWord_1949607, baseEnd_1949607] using wordTrace_append hprefix tailTrace_1949607
  have hstable : (prefixWord ++ tailWord_1949607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949607).length < 2 ^ (prefixWord ++ tailWord_1949607).sum := by decide
  have hdescent : baseEnd_1949607 < baseStart_1949607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949616 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_1949616 : Nat := 118140960795 + 1949616 * 2 ^ 59
def prefixEnd_1949616 : Nat := 4983230072969 + 3 ^ 40 * 1949616 * 2
def baseEnd_1949616 : Nat := 333696699898716450711295

theorem tailTrace_1949616 : CollatzResearch.WordTrace tailWord_1949616 prefixEnd_1949616 333696699898716450711295 := by
  unfold tailWord_1949616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35554168652440837374490351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47405558203254449832653801 35554168652440837374490351)
  ·
    refine ⟨53331252978661256061735527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35554168652440837374490351 53331252978661256061735527)
    ·
      refine ⟨79996879467991884092603291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331252978661256061735527 79996879467991884092603291)
      ·
        refine ⟨119995319201987826138904937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79996879467991884092603291 119995319201987826138904937)
        ·
          refine ⟨89996489401490869604178703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119995319201987826138904937 89996489401490869604178703)
          ·
            refine ⟨134994734102236304406268055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89996489401490869604178703 134994734102236304406268055)
            ·
              refine ⟨202492101153354456609402083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134994734102236304406268055 202492101153354456609402083)
              ·
                refine ⟨303738151730031684914103125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202492101153354456609402083 303738151730031684914103125)
                ·
                  refine ⟨1779715732793154403793573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 303738151730031684914103125 1779715732793154403793573)
                  ·
                    refine ⟨333696699898716450711295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779715732793154403793573 333696699898716450711295)
                    ·
                      rfl

theorem cell23_1949616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_1949616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949616 prefixEnd_1949616 := by exact prefixLift 1949616
  have htrace : WordTrace (prefixWord ++ tailWord_1949616) baseStart_1949616 baseEnd_1949616 := by
    simpa [prefixWord, tailWord_1949616, baseEnd_1949616] using wordTrace_append hprefix tailTrace_1949616
  have hstable : (prefixWord ++ tailWord_1949616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949616).length < 2 ^ (prefixWord ++ tailWord_1949616).sum := by decide
  have hdescent : baseEnd_1949616 < baseStart_1949616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949640 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1949640 : Nat := 118140960795 + 1949640 * 2 ^ 59
def prefixEnd_1949640 : Nat := 4983230072969 + 3 ^ 40 * 1949640 * 2
def baseEnd_1949640 : Nat := 1001102423231857258233775

theorem tailTrace_1949640 : CollatzResearch.WordTrace tailWord_1949640 prefixEnd_1949640 1001102423231857258233775 := by
  unfold tailWord_1949640
  simp only [CollatzResearch.WordTrace]
  refine ⟨35554606328397363423927187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47406141771196484565236249 35554606328397363423927187)
  ·
    refine ⟨53331909492596045135890781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35554606328397363423927187 53331909492596045135890781)
    ·
      refine ⟨19999466059723516925959043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53331909492596045135890781 19999466059723516925959043)
      ·
        refine ⟨29999199089585275388938565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19999466059723516925959043 29999199089585275388938565)
        ·
          refine ⟨5624849829297239135425981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29999199089585275388938565 5624849829297239135425981)
          ·
            refine ⟨2109318685986464675784743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5624849829297239135425981 2109318685986464675784743)
            ·
              refine ⟨3163978028979697013677115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109318685986464675784743 3163978028979697013677115)
              ·
                refine ⟨4745967043469545520515673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163978028979697013677115 4745967043469545520515673)
                ·
                  refine ⟨3559475282602159140386755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745967043469545520515673 3559475282602159140386755)
                  ·
                    refine ⟨5339212923903238710580133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559475282602159140386755 5339212923903238710580133)
                    ·
                      refine ⟨1001102423231857258233775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5339212923903238710580133 1001102423231857258233775)
                      ·
                        rfl

theorem cell23_1949640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1949640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949640 prefixEnd_1949640 := by exact prefixLift 1949640
  have htrace : WordTrace (prefixWord ++ tailWord_1949640) baseStart_1949640 baseEnd_1949640 := by
    simpa [prefixWord, tailWord_1949640, baseEnd_1949640] using wordTrace_append hprefix tailTrace_1949640
  have hstable : (prefixWord ++ tailWord_1949640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949640).length < 2 ^ (prefixWord ++ tailWord_1949640).sum := by decide
  have hdescent : baseEnd_1949640 < baseStart_1949640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949646 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1949646 : Nat := 118140960795 + 1949646 * 2 ^ 59
def prefixEnd_1949646 : Nat := 4983230072969 + 3 ^ 40 * 1949646 * 2
def baseEnd_1949646 : Nat := 111233944901753803862083

theorem tailTrace_1949646 : CollatzResearch.WordTrace tailWord_1949646 prefixEnd_1949646 111233944901753803862083 := by
  unfold tailWord_1949646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888678936846623734071599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47406287663181993248381861 8888678936846623734071599)
  ·
    refine ⟨13333018405269935601107399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8888678936846623734071599 13333018405269935601107399)
    ·
      refine ⟨19999527607904903401661099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333018405269935601107399 19999527607904903401661099)
      ·
        refine ⟨29999291411857355102491649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19999527607904903401661099 29999291411857355102491649)
        ·
          refine ⟨22499468558893016326868737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29999291411857355102491649 22499468558893016326868737)
          ·
            refine ⟨16874601419169762245151553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499468558893016326868737 16874601419169762245151553)
            ·
              refine ⟨12655951064377321683863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874601419169762245151553 12655951064377321683863665)
              ·
                refine ⟨9491963298282991262897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12655951064377321683863665 9491963298282991262897749)
                ·
                  refine ⟨111233944901753803862083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9491963298282991262897749 111233944901753803862083)
                  ·
                    rfl

theorem cell23_1949646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1949646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949646 prefixEnd_1949646 := by exact prefixLift 1949646
  have htrace : WordTrace (prefixWord ++ tailWord_1949646) baseStart_1949646 baseEnd_1949646 := by
    simpa [prefixWord, tailWord_1949646, baseEnd_1949646] using wordTrace_append hprefix tailTrace_1949646
  have hstable : (prefixWord ++ tailWord_1949646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949646).length < 2 ^ (prefixWord ++ tailWord_1949646).sum := by decide
  have hdescent : baseEnd_1949646 < baseStart_1949646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949663 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 6]
def baseStart_1949663 : Nat := 118140960795 + 1949663 * 2 ^ 59
def prefixEnd_1949663 : Nat := 4983230072969 + 3 ^ 40 * 1949663 * 2
def baseEnd_1949663 : Nat := 111234914809656740916241

theorem tailTrace_1949663 : CollatzResearch.WordTrace tailWord_1949663 prefixEnd_1949663 111234914809656740916241 := by
  unfold tailWord_1949663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71110051535711401775941643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47406701023807601183961095 71110051535711401775941643)
  ·
    refine ⟨106665077303567102663912465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71110051535711401775941643 106665077303567102663912465)
    ·
      refine ⟨79998807977675326997934349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106665077303567102663912465 79998807977675326997934349)
      ·
        refine ⟨29999552991628247624225381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79998807977675326997934349 29999552991628247624225381)
        ·
          refine ⟨5624916185930296429542259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29999552991628247624225381 5624916185930296429542259)
          ·
            refine ⟨8437374278895444644313389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624916185930296429542259 8437374278895444644313389)
            ·
              refine ⟨3164015354585791741617521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8437374278895444644313389 3164015354585791741617521)
              ·
                refine ⟨2373011515939343806213141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164015354585791741617521 2373011515939343806213141)
                ·
                  refine ⟨111234914809656740916241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2373011515939343806213141 111234914809656740916241)
                  ·
                    rfl

theorem cell23_1949663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 6].length) (baseStart_1949663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949663 prefixEnd_1949663 := by exact prefixLift 1949663
  have htrace : WordTrace (prefixWord ++ tailWord_1949663) baseStart_1949663 baseEnd_1949663 := by
    simpa [prefixWord, tailWord_1949663, baseEnd_1949663] using wordTrace_append hprefix tailTrace_1949663
  have hstable : (prefixWord ++ tailWord_1949663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949663).length < 2 ^ (prefixWord ++ tailWord_1949663).sum := by decide
  have hdescent : baseEnd_1949663 < baseStart_1949663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949676 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1949676 : Nat := 118140960795 + 1949676 * 2 ^ 59
def prefixEnd_1949676 : Nat := 4983230072969 + 3 ^ 40 * 1949676 * 2
def baseEnd_1949676 : Nat := 333706969511806372461203

theorem tailTrace_1949676 : CollatzResearch.WordTrace tailWord_1949676 prefixEnd_1949676 333706969511806372461203 := by
  unfold tailWord_1949676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35555262842332152498082441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47407017123109536664109921 35555262842332152498082441)
  ·
    refine ⟨26666447131749114373561831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35555262842332152498082441 26666447131749114373561831)
    ·
      refine ⟨39999670697623671560342747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26666447131749114373561831 39999670697623671560342747)
      ·
        refine ⟨59999506046435507340514121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39999670697623671560342747 59999506046435507340514121)
        ·
          refine ⟨44999629534826630505385591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59999506046435507340514121 44999629534826630505385591)
          ·
            refine ⟨67499444302239945758078387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44999629534826630505385591 67499444302239945758078387)
            ·
              refine ⟨101249166453359918637117581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67499444302239945758078387 101249166453359918637117581)
              ·
                refine ⟨37968437420009969488919093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101249166453359918637117581 37968437420009969488919093)
                ·
                  refine ⟨3559541008125934639586165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37968437420009969488919093 3559541008125934639586165)
                  ·
                    refine ⟨333706969511806372461203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3559541008125934639586165 333706969511806372461203)
                    ·
                      rfl

theorem cell23_1949676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1949676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949676 prefixEnd_1949676 := by exact prefixLift 1949676
  have htrace : WordTrace (prefixWord ++ tailWord_1949676) baseStart_1949676 baseEnd_1949676 := by
    simpa [prefixWord, tailWord_1949676, baseEnd_1949676] using wordTrace_append hprefix tailTrace_1949676
  have hstable : (prefixWord ++ tailWord_1949676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949676).length < 2 ^ (prefixWord ++ tailWord_1949676).sum := by decide
  have hdescent : baseEnd_1949676 < baseStart_1949676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949693 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1949693 : Nat := 118140960795 + 1949693 * 2 ^ 59
def prefixEnd_1949693 : Nat := 4983230072969 + 3 ^ 40 * 1949693 * 2
def baseEnd_1949693 : Nat := 333709879235515183623677

theorem tailTrace_1949693 : CollatzResearch.WordTrace tailWord_1949693 prefixEnd_1949693 333709879235515183623677 := by
  unfold tailWord_1949693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71111145725602716899533733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47407430483735144599689155 71111145725602716899533733)
  ·
    refine ⟨13333339823550509418662575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71111145725602716899533733 13333339823550509418662575)
    ·
      refine ⟨20000009735325764127993863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333339823550509418662575 20000009735325764127993863)
      ·
        refine ⟨30000014602988646191990795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000009735325764127993863 30000014602988646191990795)
        ·
          refine ⟨45000021904482969287986193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30000014602988646191990795 45000021904482969287986193)
          ·
            refine ⟨33750016428362226965989645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45000021904482969287986193 33750016428362226965989645)
            ·
              refine ⟨12656256160635835112246117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33750016428362226965989645 12656256160635835112246117)
              ·
                refine ⟨2373048030119219083546147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12656256160635835112246117 2373048030119219083546147)
                ·
                  refine ⟨3559572045178828625319221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373048030119219083546147 3559572045178828625319221)
                  ·
                    refine ⟨333709879235515183623677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3559572045178828625319221 333709879235515183623677)
                    ·
                      rfl

theorem cell23_1949693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1949693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949693 prefixEnd_1949693 := by exact prefixLift 1949693
  have htrace : WordTrace (prefixWord ++ tailWord_1949693) baseStart_1949693 baseEnd_1949693 := by
    simpa [prefixWord, tailWord_1949693, baseEnd_1949693] using wordTrace_append hprefix tailTrace_1949693
  have hstable : (prefixWord ++ tailWord_1949693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949693).length < 2 ^ (prefixWord ++ tailWord_1949693).sum := by decide
  have hdescent : baseEnd_1949693 < baseStart_1949693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949717 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_1949717 : Nat := 118140960795 + 1949717 * 2 ^ 59
def prefixEnd_1949717 : Nat := 4983230072969 + 3 ^ 40 * 1949717 * 2
def baseEnd_1949717 : Nat := 1001141961242253456970921

theorem tailTrace_1949717 : CollatzResearch.WordTrace tailWord_1949717 prefixEnd_1949717 1001141961242253456970921 := by
  unfold tailWord_1949717
  simp only [CollatzResearch.WordTrace]
  refine ⟨71112021077515768998407405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47408014051677179332271603 71112021077515768998407405)
  ·
    refine ⟨26667007904068413374402777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71112021077515768998407405 26667007904068413374402777)
    ·
      refine ⟨20000255928051310030802083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26667007904068413374402777 20000255928051310030802083)
      ·
        refine ⟨30000383892076965046203125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000255928051310030802083 30000383892076965046203125)
        ·
          refine ⟨2812535989882215473081543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30000383892076965046203125 2812535989882215473081543)
          ·
            refine ⟨4218803984823323209622315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812535989882215473081543 4218803984823323209622315)
            ·
              refine ⟨6328205977234984814433473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218803984823323209622315 6328205977234984814433473)
              ·
                refine ⟨4746154482926238610825105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328205977234984814433473 4746154482926238610825105)
                ·
                  refine ⟨3559615862194678958118829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746154482926238610825105 3559615862194678958118829)
                  ·
                    refine ⟨1334855948323004609294561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3559615862194678958118829 1334855948323004609294561)
                    ·
                      refine ⟨1001141961242253456970921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334855948323004609294561 1001141961242253456970921)
                      ·
                        rfl

theorem cell23_1949717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_1949717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949717 prefixEnd_1949717 := by exact prefixLift 1949717
  have htrace : WordTrace (prefixWord ++ tailWord_1949717) baseStart_1949717 baseEnd_1949717 := by
    simpa [prefixWord, tailWord_1949717, baseEnd_1949717] using wordTrace_append hprefix tailTrace_1949717
  have hstable : (prefixWord ++ tailWord_1949717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949717).length < 2 ^ (prefixWord ++ tailWord_1949717).sum := by decide
  have hdescent : baseEnd_1949717 < baseStart_1949717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949733 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1949733 : Nat := 118140960795 + 1949733 * 2 ^ 59
def prefixEnd_1949733 : Nat := 4983230072969 + 3 ^ 40 * 1949733 * 2
def baseEnd_1949733 : Nat := 1001150176932725394370847

theorem tailTrace_1949733 : CollatzResearch.WordTrace tailWord_1949733 prefixEnd_1949733 1001150176932725394370847 := by
  unfold tailWord_1949733
  simp only [CollatzResearch.WordTrace]
  refine ⟨71112604645457803730989853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47408403096971869153993235 71112604645457803730989853)
  ·
    refine ⟨26667226742046676399121195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71112604645457803730989853 26667226742046676399121195)
    ·
      refine ⟨40000840113070014598681793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26667226742046676399121195 40000840113070014598681793)
      ·
        refine ⟨30000630084802510949011345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40000840113070014598681793 30000630084802510949011345)
        ·
          refine ⟨22500472563601883211758509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30000630084802510949011345 22500472563601883211758509)
          ·
            refine ⟨8437677211350706204409441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22500472563601883211758509 8437677211350706204409441)
            ·
              refine ⟨6328257908513029653307081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437677211350706204409441 6328257908513029653307081)
              ·
                refine ⟨4746193431384772239980311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328257908513029653307081 4746193431384772239980311)
                ·
                  refine ⟨7119290147077158359970467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746193431384772239980311 7119290147077158359970467)
                  ·
                    refine ⟨10678935220615737539955701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119290147077158359970467 10678935220615737539955701)
                    ·
                      refine ⟨1001150176932725394370847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10678935220615737539955701 1001150176932725394370847)
                      ·
                        rfl

theorem cell23_1949733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1949733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949733 prefixEnd_1949733 := by exact prefixLift 1949733
  have htrace : WordTrace (prefixWord ++ tailWord_1949733) baseStart_1949733 baseEnd_1949733 := by
    simpa [prefixWord, tailWord_1949733, baseEnd_1949733] using wordTrace_append hprefix tailTrace_1949733
  have hstable : (prefixWord ++ tailWord_1949733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949733).length < 2 ^ (prefixWord ++ tailWord_1949733).sum := by decide
  have hdescent : baseEnd_1949733 < baseStart_1949733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949767 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_1949767 : Nat := 118140960795 + 1949767 * 2 ^ 59
def prefixEnd_1949767 : Nat := 4983230072969 + 3 ^ 40 * 1949767 * 2
def baseEnd_1949767 : Nat := 1001167635274978261345691

theorem tailTrace_1949767 : CollatzResearch.WordTrace tailWord_1949767 prefixEnd_1949767 1001167635274978261345691 := by
  unfold tailWord_1949767
  simp only [CollatzResearch.WordTrace]
  refine ⟨71113844727334627537727555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47409229818223085025151703 71113844727334627537727555)
  ·
    refine ⟨106670767091001941306591333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71113844727334627537727555 106670767091001941306591333)
    ·
      refine ⟨20000768829562863994985875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106670767091001941306591333 20000768829562863994985875)
      ·
        refine ⟨30001153244344295992478813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000768829562863994985875 30001153244344295992478813)
        ·
          refine ⟨11250432466629110997179555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30001153244344295992478813 11250432466629110997179555)
          ·
            refine ⟨16875648699943666495769333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250432466629110997179555 16875648699943666495769333)
            ·
              refine ⟨1582092065619718733978375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16875648699943666495769333 1582092065619718733978375)
              ·
                refine ⟨2373138098429578100967563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582092065619718733978375 2373138098429578100967563)
                ·
                  refine ⟨3559707147644367151451345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373138098429578100967563 3559707147644367151451345)
                  ·
                    refine ⟨2669780360733275363588509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559707147644367151451345 2669780360733275363588509)
                    ·
                      refine ⟨1001167635274978261345691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2669780360733275363588509 1001167635274978261345691)
                      ·
                        rfl

theorem cell23_1949767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_1949767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949767 prefixEnd_1949767 := by exact prefixLift 1949767
  have htrace : WordTrace (prefixWord ++ tailWord_1949767) baseStart_1949767 baseEnd_1949767 := by
    simpa [prefixWord, tailWord_1949767, baseEnd_1949767] using wordTrace_append hprefix tailTrace_1949767
  have hstable : (prefixWord ++ tailWord_1949767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949767).length < 2 ^ (prefixWord ++ tailWord_1949767).sum := by decide
  have hdescent : baseEnd_1949767 < baseStart_1949767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949776 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1949776 : Nat := 118140960795 + 1949776 * 2 ^ 59
def prefixEnd_1949776 : Nat := 4983230072969 + 3 ^ 40 * 1949776 * 2
def baseEnd_1949776 : Nat := 1001172256600868726133149

theorem tailTrace_1949776 : CollatzResearch.WordTrace tailWord_1949776 prefixEnd_1949776 1001172256600868726133149 := by
  unfold tailWord_1949776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35557086492151011037402591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47409448656201348049870121 35557086492151011037402591)
  ·
    refine ⟨53335629738226516556103887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35557086492151011037402591 53335629738226516556103887)
    ·
      refine ⟨80003444607339774834155831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53335629738226516556103887 80003444607339774834155831)
      ·
        refine ⟨120005166911009662251233747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80003444607339774834155831 120005166911009662251233747)
        ·
          refine ⟨180007750366514493376850621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120005166911009662251233747 180007750366514493376850621)
          ·
            refine ⟨67502906387442935016318983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180007750366514493376850621 67502906387442935016318983)
            ·
              refine ⟨101254359581164402524478475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67502906387442935016318983 101254359581164402524478475)
              ·
                refine ⟨151881539371746603786717713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101254359581164402524478475 151881539371746603786717713)
                ·
                  refine ⟨113911154528809952840038285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151881539371746603786717713 113911154528809952840038285)
                  ·
                    refine ⟨42716682948303732315014357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113911154528809952840038285 42716682948303732315014357)
                    ·
                      refine ⟨1001172256600868726133149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42716682948303732315014357 1001172256600868726133149)
                      ·
                        rfl

theorem cell23_1949776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1949776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949776 prefixEnd_1949776 := by exact prefixLift 1949776
  have htrace : WordTrace (prefixWord ++ tailWord_1949776) baseStart_1949776 baseEnd_1949776 := by
    simpa [prefixWord, tailWord_1949776, baseEnd_1949776] using wordTrace_append hprefix tailTrace_1949776
  have hstable : (prefixWord ++ tailWord_1949776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949776).length < 2 ^ (prefixWord ++ tailWord_1949776).sum := by decide
  have hdescent : baseEnd_1949776 < baseStart_1949776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949781 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1949781 : Nat := 118140960795 + 1949781 * 2 ^ 59
def prefixEnd_1949781 : Nat := 4983230072969 + 3 ^ 40 * 1949781 * 2
def baseEnd_1949781 : Nat := 1001174824004141206570627

theorem tailTrace_1949781 : CollatzResearch.WordTrace tailWord_1949781 prefixEnd_1949781 1001174824004141206570627 := by
  unfold tailWord_1949781
  simp only [CollatzResearch.WordTrace]
  refine ⟨71114355349283907928737197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47409570232855938619158131 71114355349283907928737197)
  ·
    refine ⟨26667883255981465473276449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71114355349283907928737197 26667883255981465473276449)
    ·
      refine ⟨20000912441986099104957337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26667883255981465473276449 20000912441986099104957337)
      ·
        refine ⟨15000684331489574328718003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20000912441986099104957337 15000684331489574328718003)
        ·
          refine ⟨22501026497234361493077005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15000684331489574328718003 22501026497234361493077005)
          ·
            refine ⟨8437884936462885559903877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22501026497234361493077005 8437884936462885559903877)
            ·
              refine ⟨1582103425586791042481977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8437884936462885559903877 1582103425586791042481977)
              ·
                refine ⟨1186577569190093281861483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582103425586791042481977 1186577569190093281861483)
                ·
                  refine ⟨1779866353785139922792225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186577569190093281861483 1779866353785139922792225)
                  ·
                    refine ⟨1334899765338854942094169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1779866353785139922792225 1334899765338854942094169)
                    ·
                      refine ⟨1001174824004141206570627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1334899765338854942094169 1001174824004141206570627)
                      ·
                        rfl

theorem cell23_1949781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1949781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949781 prefixEnd_1949781 := by exact prefixLift 1949781
  have htrace : WordTrace (prefixWord ++ tailWord_1949781) baseStart_1949781 baseEnd_1949781 := by
    simpa [prefixWord, tailWord_1949781, baseEnd_1949781] using wordTrace_append hprefix tailTrace_1949781
  have hstable : (prefixWord ++ tailWord_1949781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949781).length < 2 ^ (prefixWord ++ tailWord_1949781).sum := by decide
  have hdescent : baseEnd_1949781 < baseStart_1949781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949797 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1949797 : Nat := 118140960795 + 1949797 * 2 ^ 59
def prefixEnd_1949797 : Nat := 4983230072969 + 3 ^ 40 * 1949797 * 2
def baseEnd_1949797 : Nat := 1001183039694613143970553

theorem tailTrace_1949797 : CollatzResearch.WordTrace tailWord_1949797 prefixEnd_1949797 1001183039694613143970553 := by
  unfold tailWord_1949797
  simp only [CollatzResearch.WordTrace]
  refine ⟨71114938917225942661319645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47409959278150628440879763 71114938917225942661319645)
  ·
    refine ⟨26668102093959728497994867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71114938917225942661319645 26668102093959728497994867)
    ·
      refine ⟨40002153140939592746992301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26668102093959728497994867 40002153140939592746992301)
      ·
        refine ⟨15000807427852347280122113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40002153140939592746992301 15000807427852347280122113)
        ·
          refine ⟨11250605570889260460091585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15000807427852347280122113 11250605570889260460091585)
          ·
            refine ⟨8437954178166945345068689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11250605570889260460091585 8437954178166945345068689)
            ·
              refine ⟨6328465633625209008801517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437954178166945345068689 6328465633625209008801517)
              ·
                refine ⟨2373174612609453378300569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6328465633625209008801517 2373174612609453378300569)
                ·
                  refine ⟨1779880959457090033725427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373174612609453378300569 1779880959457090033725427)
                  ·
                    refine ⟨2669821439185635050588141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1779880959457090033725427 2669821439185635050588141)
                    ·
                      refine ⟨1001183039694613143970553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2669821439185635050588141 1001183039694613143970553)
                      ·
                        rfl

theorem cell23_1949797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1949797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949797 prefixEnd_1949797 := by exact prefixLift 1949797
  have htrace : WordTrace (prefixWord ++ tailWord_1949797) baseStart_1949797 baseEnd_1949797 := by
    simpa [prefixWord, tailWord_1949797, baseEnd_1949797] using wordTrace_append hprefix tailTrace_1949797
  have hstable : (prefixWord ++ tailWord_1949797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949797).length < 2 ^ (prefixWord ++ tailWord_1949797).sum := by decide
  have hdescent : baseEnd_1949797 < baseStart_1949797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949833 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_1949833 : Nat := 118140960795 + 1949833 * 2 ^ 59
def prefixEnd_1949833 : Nat := 4983230072969 + 3 ^ 40 * 1949833 * 2
def baseEnd_1949833 : Nat := 1001201524998175003120387

theorem tailTrace_1949833 : CollatzResearch.WordTrace tailWord_1949833 prefixEnd_1949833 1001201524998175003120387 := by
  unfold tailWord_1949833
  simp only [CollatzResearch.WordTrace]
  refine ⟨71116251945095520809630153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47410834630063680539753435 71116251945095520809630153)
  ·
    refine ⟨53337188958821640607222615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71116251945095520809630153 53337188958821640607222615)
    ·
      refine ⟨80005783438232460910833923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53337188958821640607222615 80005783438232460910833923)
      ·
        refine ⟨120008675157348691366250885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80005783438232460910833923 120008675157348691366250885)
        ·
          refine ⟨22501626592002879631172041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120008675157348691366250885 22501626592002879631172041)
          ·
            refine ⟨16876219944002159723379031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22501626592002879631172041 16876219944002159723379031)
            ·
              refine ⟨25314329916003239585068547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876219944002159723379031 25314329916003239585068547)
              ·
                refine ⟨37971494874004859377602821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25314329916003239585068547 37971494874004859377602821)
                ·
                  refine ⟨7119655288875911133300529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37971494874004859377602821 7119655288875911133300529)
                  ·
                    refine ⟨5339741466656933349975397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7119655288875911133300529 5339741466656933349975397)
                    ·
                      refine ⟨1001201524998175003120387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5339741466656933349975397 1001201524998175003120387)
                      ·
                        rfl

theorem cell23_1949833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_1949833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949833 prefixEnd_1949833 := by exact prefixLift 1949833
  have htrace : WordTrace (prefixWord ++ tailWord_1949833) baseStart_1949833 baseEnd_1949833 := by
    simpa [prefixWord, tailWord_1949833, baseEnd_1949833] using wordTrace_append hprefix tailTrace_1949833
  have hstable : (prefixWord ++ tailWord_1949833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949833).length < 2 ^ (prefixWord ++ tailWord_1949833).sum := by decide
  have hdescent : baseEnd_1949833 < baseStart_1949833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949883 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_1949883 : Nat := 118140960795 + 1949883 * 2 ^ 59
def prefixEnd_1949883 : Nat := 4983230072969 + 3 ^ 40 * 1949883 * 2
def baseEnd_1949883 : Nat := 1001227199030899807495157

theorem tailTrace_1949883 : CollatzResearch.WordTrace tailWord_1949883 prefixEnd_1949883 1001227199030899807495157 := by
  unfold tailWord_1949883
  simp only [CollatzResearch.WordTrace]
  refine ⟨71118075594914379348950303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47412050396609586232633535 71118075594914379348950303)
  ·
    refine ⟨106677113392371569023425455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71118075594914379348950303 106677113392371569023425455)
    ·
      refine ⟨160015670088557353535138183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106677113392371569023425455 160015670088557353535138183)
      ·
        refine ⟨240023505132836030302707275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160015670088557353535138183 240023505132836030302707275)
        ·
          refine ⟨360035257699254045454060913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240023505132836030302707275 360035257699254045454060913)
          ·
            refine ⟨270026443274440534090545685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360035257699254045454060913 270026443274440534090545685)
            ·
              refine ⟨12657489528489400035494329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270026443274440534090545685 12657489528489400035494329)
              ·
                refine ⟨9493117146367050026620747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12657489528489400035494329 9493117146367050026620747)
                ·
                  refine ⟨14239675719550575039931121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493117146367050026620747 14239675719550575039931121)
                  ·
                    refine ⟨10679756789662931279948341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14239675719550575039931121 10679756789662931279948341)
                    ·
                      refine ⟨1001227199030899807495157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10679756789662931279948341 1001227199030899807495157)
                      ·
                        rfl

theorem cell23_1949883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_1949883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949883 prefixEnd_1949883 := by exact prefixLift 1949883
  have htrace : WordTrace (prefixWord ++ tailWord_1949883) baseStart_1949883 baseEnd_1949883 := by
    simpa [prefixWord, tailWord_1949883, baseEnd_1949883] using wordTrace_append hprefix tailTrace_1949883
  have hstable : (prefixWord ++ tailWord_1949883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949883).length < 2 ^ (prefixWord ++ tailWord_1949883).sum := by decide
  have hdescent : baseEnd_1949883 < baseStart_1949883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949920 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_1949920 : Nat := 118140960795 + 1949920 * 2 ^ 59
def prefixEnd_1949920 : Nat := 4983230072969 + 3 ^ 40 * 1949920 * 2
def baseEnd_1949920 : Nat := 333748732605038720910829

theorem tailTrace_1949920 : CollatzResearch.WordTrace tailWord_1949920 prefixEnd_1949920 333748732605038720910829 := by
  unfold tailWord_1949920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559712547890167334023607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47412950063853556445364809 35559712547890167334023607)
  ·
    refine ⟨53339568821835251001035411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35559712547890167334023607 53339568821835251001035411)
    ·
      refine ⟨80009353232752876501553117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53339568821835251001035411 80009353232752876501553117)
      ·
        refine ⟨30003507462282328688082419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80009353232752876501553117 30003507462282328688082419)
        ·
          refine ⟨45005261193423493032123629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30003507462282328688082419 45005261193423493032123629)
          ·
            refine ⟨16876972947533809887046361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45005261193423493032123629 16876972947533809887046361)
            ·
              refine ⟨12657729710650357415284771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16876972947533809887046361 12657729710650357415284771)
              ·
                refine ⟨18986594565975536122927157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12657729710650357415284771 18986594565975536122927157)
                ·
                  refine ⟨1779993240560206511524421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18986594565975536122927157 1779993240560206511524421)
                  ·
                    refine ⟨333748732605038720910829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779993240560206511524421 333748732605038720910829)
                    ·
                      rfl

theorem cell23_1949920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_1949920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949920 prefixEnd_1949920 := by exact prefixLift 1949920
  have htrace : WordTrace (prefixWord ++ tailWord_1949920) baseStart_1949920 baseEnd_1949920 := by
    simpa [prefixWord, tailWord_1949920, baseEnd_1949920] using wordTrace_append hprefix tailTrace_1949920
  have hstable : (prefixWord ++ tailWord_1949920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949920).length < 2 ^ (prefixWord ++ tailWord_1949920).sum := by decide
  have hdescent : baseEnd_1949920 < baseStart_1949920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949927 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1949927 : Nat := 118140960795 + 1949927 * 2 ^ 59
def prefixEnd_1949927 : Nat := 4983230072969 + 3 ^ 40 * 1949927 * 2
def baseEnd_1949927 : Nat := 1001249792179697635344955

theorem tailTrace_1949927 : CollatzResearch.WordTrace tailWord_1949927 prefixEnd_1949927 1001249792179697635344955 := by
  unfold tailWord_1949927
  simp only [CollatzResearch.WordTrace]
  refine ⟨71119680406754974863552035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47413120271169983242368023 71119680406754974863552035)
  ·
    refine ⟨106679520610132462295328053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71119680406754974863552035 106679520610132462295328053)
    ·
      refine ⟨10001205057199918340187005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106679520610132462295328053 10001205057199918340187005)
      ·
        refine ⟨3750451896449969377570127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10001205057199918340187005 3750451896449969377570127)
        ·
          refine ⟨5625677844674954066355191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750451896449969377570127 5625677844674954066355191)
          ·
            refine ⟨8438516767012431099532787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625677844674954066355191 8438516767012431099532787)
            ·
              refine ⟨12657775150518646649299181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438516767012431099532787 12657775150518646649299181)
              ·
                refine ⟨4746665681444492493487193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12657775150518646649299181 4746665681444492493487193)
                ·
                  refine ⟨3559999261083369370115395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746665681444492493487193 3559999261083369370115395)
                  ·
                    refine ⟨5339998891625054055173093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559999261083369370115395 5339998891625054055173093)
                    ·
                      refine ⟨1001249792179697635344955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5339998891625054055173093 1001249792179697635344955)
                      ·
                        rfl

theorem cell23_1949927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1949927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949927 prefixEnd_1949927 := by exact prefixLift 1949927
  have htrace : WordTrace (prefixWord ++ tailWord_1949927) baseStart_1949927 baseEnd_1949927 := by
    simpa [prefixWord, tailWord_1949927, baseEnd_1949927] using wordTrace_append hprefix tailTrace_1949927
  have hstable : (prefixWord ++ tailWord_1949927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949927).length < 2 ^ (prefixWord ++ tailWord_1949927).sum := by decide
  have hdescent : baseEnd_1949927 < baseStart_1949927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949981 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1949981 : Nat := 118140960795 + 1949981 * 2 ^ 59
def prefixEnd_1949981 : Nat := 4983230072969 + 3 ^ 40 * 1949981 * 2
def baseEnd_1949981 : Nat := 1001277520135040424069707

theorem tailTrace_1949981 : CollatzResearch.WordTrace tailWord_1949981 prefixEnd_1949981 1001277520135040424069707 := by
  unfold tailWord_1949981
  simp only [CollatzResearch.WordTrace]
  refine ⟨71121649948559342086017797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47414433299039561390678531 71121649948559342086017797)
  ·
    refine ⟨13335309365354876641128337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71121649948559342086017797 13335309365354876641128337)
    ·
      refine ⟨10001482024016157480846253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13335309365354876641128337 10001482024016157480846253)
      ·
        refine ⟨3750555759006059055317345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10001482024016157480846253 3750555759006059055317345)
        ·
          refine ⟨2812916819254544291488009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750555759006059055317345 2812916819254544291488009)
          ·
            refine ⟨2109687614440908218616007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2812916819254544291488009 2109687614440908218616007)
            ·
              refine ⟨3164531421661362327924011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109687614440908218616007 3164531421661362327924011)
              ·
                refine ⟨4746797132492043491886017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164531421661362327924011 4746797132492043491886017)
                ·
                  refine ⟨3560097849369032618914513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746797132492043491886017 3560097849369032618914513)
                  ·
                    refine ⟨2670073387026774464185885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560097849369032618914513 2670073387026774464185885)
                    ·
                      refine ⟨1001277520135040424069707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2670073387026774464185885 1001277520135040424069707)
                      ·
                        rfl

theorem cell23_1949981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1949981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949981 prefixEnd_1949981 := by exact prefixLift 1949981
  have htrace : WordTrace (prefixWord ++ tailWord_1949981) baseStart_1949981 baseEnd_1949981 := by
    simpa [prefixWord, tailWord_1949981, baseEnd_1949981] using wordTrace_append hprefix tailTrace_1949981
  have hstable : (prefixWord ++ tailWord_1949981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949981).length < 2 ^ (prefixWord ++ tailWord_1949981).sum := by decide
  have hdescent : baseEnd_1949981 < baseStart_1949981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949987 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 5, 2]
def baseStart_1949987 : Nat := 118140960795 + 1949987 * 2 ^ 59
def prefixEnd_1949987 : Nat := 4983230072969 + 3 ^ 40 * 1949987 * 2
def baseEnd_1949987 : Nat := 1001280601018967400594679

theorem tailTrace_1949987 : CollatzResearch.WordTrace tailWord_1949987 prefixEnd_1949987 1001280601018967400594679 := by
  unfold tailWord_1949987
  simp only [CollatzResearch.WordTrace]
  refine ⟨71121868786537605110736215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47414579191025070073824143 71121868786537605110736215)
  ·
    refine ⟨106682803179806407666104323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71121868786537605110736215 106682803179806407666104323)
    ·
      refine ⟨160024204769709611499156485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106682803179806407666104323 160024204769709611499156485)
      ·
        refine ⟨30004538394320552156091841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160024204769709611499156485 30004538394320552156091841)
        ·
          refine ⟨22503403795740414117068881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30004538394320552156091841 22503403795740414117068881)
          ·
            refine ⟨16877552846805310587801661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22503403795740414117068881 16877552846805310587801661)
            ·
              refine ⟨6329082317551991470425623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16877552846805310587801661 6329082317551991470425623)
              ·
                refine ⟨9493623476327987205638435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329082317551991470425623 9493623476327987205638435)
                ·
                  refine ⟨14240435214491980808457653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493623476327987205638435 14240435214491980808457653)
                  ·
                    refine ⟨1335040801358623200792905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14240435214491980808457653 1335040801358623200792905)
                    ·
                      refine ⟨1001280601018967400594679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335040801358623200792905 1001280601018967400594679)
                      ·
                        rfl

theorem cell23_1949987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_1949987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1949987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1949987 prefixEnd_1949987 := by exact prefixLift 1949987
  have htrace : WordTrace (prefixWord ++ tailWord_1949987) baseStart_1949987 baseEnd_1949987 := by
    simpa [prefixWord, tailWord_1949987, baseEnd_1949987] using wordTrace_append hprefix tailTrace_1949987
  have hstable : (prefixWord ++ tailWord_1949987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949987).length < 2 ^ (prefixWord ++ tailWord_1949987).sum := by decide
  have hdescent : baseEnd_1949987 < baseStart_1949987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950000 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1950000 : Nat := 118140960795 + 1950000 * 2 ^ 59
def prefixEnd_1950000 : Nat := 4983230072969 + 3 ^ 40 * 1950000 * 2
def baseEnd_1950000 : Nat := 1001287276267475849732119

theorem tailTrace_1950000 : CollatzResearch.WordTrace tailWord_1950000 prefixEnd_1950000 1001287276267475849732119 := by
  unfold tailWord_1950000
  simp only [CollatzResearch.WordTrace]
  refine ⟨35561171467745254165479727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47414895290327005553972969 35561171467745254165479727)
  ·
    refine ⟨53341757201617881248219591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35561171467745254165479727 53341757201617881248219591)
    ·
      refine ⟨80012635802426821872329387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53341757201617881248219591 80012635802426821872329387)
      ·
        refine ⟨120018953703640232808494081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80012635802426821872329387 120018953703640232808494081)
        ·
          refine ⟨90014215277730174606370561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120018953703640232808494081 90014215277730174606370561)
          ·
            refine ⟨67510661458297630954777921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90014215277730174606370561 67510661458297630954777921)
            ·
              refine ⟨50632996093723223216083441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67510661458297630954777921 50632996093723223216083441)
              ·
                refine ⟨37974747070292417412062581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50632996093723223216083441 37974747070292417412062581)
                ·
                  refine ⟨3560132537839914132380867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37974747070292417412062581 3560132537839914132380867)
                  ·
                    refine ⟨5340198806759871198571301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560132537839914132380867 5340198806759871198571301)
                    ·
                      refine ⟨1001287276267475849732119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5340198806759871198571301 1001287276267475849732119)
                      ·
                        rfl

theorem cell23_1950000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1950000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950000 prefixEnd_1950000 := by exact prefixLift 1950000
  have htrace : WordTrace (prefixWord ++ tailWord_1950000) baseStart_1950000 baseEnd_1950000 := by
    simpa [prefixWord, tailWord_1950000, baseEnd_1950000] using wordTrace_append hprefix tailTrace_1950000
  have hstable : (prefixWord ++ tailWord_1950000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950000).length < 2 ^ (prefixWord ++ tailWord_1950000).sum := by decide
  have hdescent : baseEnd_1950000 < baseStart_1950000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950102 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1950102 : Nat := 118140960795 + 1950102 * 2 ^ 59
def prefixEnd_1950102 : Nat := 4983230072969 + 3 ^ 40 * 1950102 * 2
def baseEnd_1950102 : Nat := 1001339651294234450656651

theorem tailTrace_1950102 : CollatzResearch.WordTrace tailWord_1950102 prefixEnd_1950102 1001339651294234450656651 := by
  unfold tailWord_1950102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445378948820061234448285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47417375454080653167448373 4445378948820061234448285)
  ·
    refine ⟨1667017105807522962918107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4445378948820061234448285 1667017105807522962918107)
    ·
      refine ⟨2500525658711284444377161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667017105807522962918107 2500525658711284444377161)
      ·
        refine ⟨1875394244033463333282871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2500525658711284444377161 1875394244033463333282871)
        ·
          refine ⟨2813091366050194999924307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875394244033463333282871 2813091366050194999924307)
          ·
            refine ⟨4219637049075292499886461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813091366050194999924307 4219637049075292499886461)
            ·
              refine ⟨1582363893403234687457423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219637049075292499886461 1582363893403234687457423)
              ·
                refine ⟨2373545840104852031186135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582363893403234687457423 2373545840104852031186135)
                ·
                  refine ⟨3560318760157278046779203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373545840104852031186135 3560318760157278046779203)
                  ·
                    refine ⟨5340478140235917070168805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560318760157278046779203 5340478140235917070168805)
                    ·
                      refine ⟨1001339651294234450656651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5340478140235917070168805 1001339651294234450656651)
                      ·
                        rfl

theorem cell23_1950102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1950102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950102 prefixEnd_1950102 := by exact prefixLift 1950102
  have htrace : WordTrace (prefixWord ++ tailWord_1950102) baseStart_1950102 baseEnd_1950102 := by
    simpa [prefixWord, tailWord_1950102, baseEnd_1950102] using wordTrace_append hprefix tailTrace_1950102
  have hstable : (prefixWord ++ tailWord_1950102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950102).length < 2 ^ (prefixWord ++ tailWord_1950102).sum := by decide
  have hdescent : baseEnd_1950102 < baseStart_1950102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950137 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1950137 : Nat := 118140960795 + 1950137 * 2 ^ 59
def prefixEnd_1950137 : Nat := 4983230072969 + 3 ^ 40 * 1950137 * 2
def baseEnd_1950137 : Nat := 1001357623117141813718989

theorem tailTrace_1950137 : CollatzResearch.WordTrace tailWord_1950137 prefixEnd_1950137 1001357623117141813718989 := by
  unfold tailWord_1950137
  simp only [CollatzResearch.WordTrace]
  refine ⟨71127339735994180728696665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47418226490662787152464443 71127339735994180728696665)
  ·
    refine ⟨53345504801995635546522499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71127339735994180728696665 53345504801995635546522499)
    ·
      refine ⟨80018257202993453319783749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53345504801995635546522499 80018257202993453319783749)
      ·
        refine ⟨15003423225561272497459453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80018257202993453319783749 15003423225561272497459453)
        ·
          refine ⟨5626283709585477186547295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15003423225561272497459453 5626283709585477186547295)
          ·
            refine ⟨8439425564378215779820943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626283709585477186547295 8439425564378215779820943)
            ·
              refine ⟨12659138346567323669731415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439425564378215779820943 12659138346567323669731415)
              ·
                refine ⟨18988707519850985504597123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659138346567323669731415 18988707519850985504597123)
                ·
                  refine ⟨28483061279776478256895685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18988707519850985504597123 28483061279776478256895685)
                  ·
                    refine ⟨5340573989958089673167941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28483061279776478256895685 5340573989958089673167941)
                    ·
                      refine ⟨1001357623117141813718989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5340573989958089673167941 1001357623117141813718989)
                      ·
                        rfl

theorem cell23_1950137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1950137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950137 prefixEnd_1950137 := by exact prefixLift 1950137
  have htrace : WordTrace (prefixWord ++ tailWord_1950137) baseStart_1950137 baseEnd_1950137 := by
    simpa [prefixWord, tailWord_1950137, baseEnd_1950137] using wordTrace_append hprefix tailTrace_1950137
  have hstable : (prefixWord ++ tailWord_1950137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950137).length < 2 ^ (prefixWord ++ tailWord_1950137).sum := by decide
  have hdescent : baseEnd_1950137 < baseStart_1950137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950141 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1950141 : Nat := 118140960795 + 1950141 * 2 ^ 59
def prefixEnd_1950141 : Nat := 4983230072969 + 3 ^ 40 * 1950141 * 2
def baseEnd_1950141 : Nat := 1001359677039759798068971

theorem tailTrace_1950141 : CollatzResearch.WordTrace tailWord_1950141 prefixEnd_1950141 1001359677039759798068971 := by
  unfold tailWord_1950141
  simp only [CollatzResearch.WordTrace]
  refine ⟨71127485627979689411842277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47418323751986459607894851 71127485627979689411842277)
  ·
    refine ⟨13336403555246191764720427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71127485627979689411842277 13336403555246191764720427)
    ·
      refine ⟨20004605332869287647080641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13336403555246191764720427 20004605332869287647080641)
      ·
        refine ⟨15003453999651965735310481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20004605332869287647080641 15003453999651965735310481)
        ·
          refine ⟨11252590499738974301482861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15003453999651965735310481 11252590499738974301482861)
          ·
            refine ⟨4219721437402115363056073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11252590499738974301482861 4219721437402115363056073)
            ·
              refine ⟨3164791078051586522292055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219721437402115363056073 3164791078051586522292055)
              ·
                refine ⟨4747186617077379783438083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164791078051586522292055 4747186617077379783438083)
                ·
                  refine ⟨7120779925616069675157125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747186617077379783438083 7120779925616069675157125)
                  ·
                    refine ⟨1335146236053013064091961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120779925616069675157125 1335146236053013064091961)
                    ·
                      refine ⟨1001359677039759798068971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335146236053013064091961 1001359677039759798068971)
                      ·
                        rfl

theorem cell23_1950141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1950141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950141 prefixEnd_1950141 := by exact prefixLift 1950141
  have htrace : WordTrace (prefixWord ++ tailWord_1950141) baseStart_1950141 baseEnd_1950141 := by
    simpa [prefixWord, tailWord_1950141, baseEnd_1950141] using wordTrace_append hprefix tailTrace_1950141
  have hstable : (prefixWord ++ tailWord_1950141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950141).length < 2 ^ (prefixWord ++ tailWord_1950141).sum := by decide
  have hdescent : baseEnd_1950141 < baseStart_1950141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950162 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1950162 : Nat := 118140960795 + 1950162 * 2 ^ 59
def prefixEnd_1950162 : Nat := 4983230072969 + 3 ^ 40 * 1950162 * 2
def baseEnd_1950162 : Nat := 1001370460133504215906375

theorem tailTrace_1950162 : CollatzResearch.WordTrace tailWord_1950162 prefixEnd_1950162 1001370460133504215906375 := by
  unfold tailWord_1950162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782062890225902499589185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47418834373935739998904493 17782062890225902499589185)
  ·
    refine ⟨13336547167669426874691889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17782062890225902499589185 13336547167669426874691889)
    ·
      refine ⟨10002410375752070156018917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13336547167669426874691889 10002410375752070156018917)
      ·
        refine ⟨1875451945453513154253547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10002410375752070156018917 1875451945453513154253547)
        ·
          refine ⟨2813177918180269731380321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875451945453513154253547 2813177918180269731380321)
          ·
            refine ⟨2109883438635202298535241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813177918180269731380321 2109883438635202298535241)
            ·
              refine ⟨1582412578976401723901431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109883438635202298535241 1582412578976401723901431)
              ·
                refine ⟨2373618868464602585852147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582412578976401723901431 2373618868464602585852147)
                ·
                  refine ⟨3560428302696903878778221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373618868464602585852147 3560428302696903878778221)
                  ·
                    refine ⟨1335160613511338954541833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3560428302696903878778221 1335160613511338954541833)
                    ·
                      refine ⟨1001370460133504215906375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335160613511338954541833 1001370460133504215906375)
                      ·
                        rfl

theorem cell23_1950162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1950162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950162 prefixEnd_1950162 := by exact prefixLift 1950162
  have htrace : WordTrace (prefixWord ++ tailWord_1950162) baseStart_1950162 baseEnd_1950162 := by
    simpa [prefixWord, tailWord_1950162, baseEnd_1950162] using wordTrace_append hprefix tailTrace_1950162
  have hstable : (prefixWord ++ tailWord_1950162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950162).length < 2 ^ (prefixWord ++ tailWord_1950162).sum := by decide
  have hdescent : baseEnd_1950162 < baseStart_1950162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950177 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1950177 : Nat := 118140960795 + 1950177 * 2 ^ 59
def prefixEnd_1950177 : Nat := 4983230072969 + 3 ^ 40 * 1950177 * 2
def baseEnd_1950177 : Nat := 333792720781107219072935

theorem tailTrace_1950177 : CollatzResearch.WordTrace tailWord_1950177 prefixEnd_1950177 333792720781107219072935 := by
  unfold tailWord_1950177
  simp only [CollatzResearch.WordTrace]
  refine ⟨71128798655849267560152785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47419199103899511706768523 71128798655849267560152785)
  ·
    refine ⟨53346598991886950670114589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71128798655849267560152785 53346598991886950670114589)
    ·
      refine ⟨20004974621957606501292971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53346598991886950670114589 20004974621957606501292971)
      ·
        refine ⟨30007461932936409751939457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20004974621957606501292971 30007461932936409751939457)
        ·
          refine ⟨22505596449702307313954593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30007461932936409751939457 22505596449702307313954593)
          ·
            refine ⟨16879197337276730485465945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22505596449702307313954593 16879197337276730485465945)
            ·
              refine ⟨12659398002957547864099459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16879197337276730485465945 12659398002957547864099459)
              ·
                refine ⟨18989097004436321796149189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659398002957547864099459 18989097004436321796149189)
                ·
                  refine ⟨3560455688331810336777973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18989097004436321796149189 3560455688331810336777973)
                  ·
                    refine ⟨333792720781107219072935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3560455688331810336777973 333792720781107219072935)
                    ·
                      rfl

theorem cell23_1950177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1950177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950177 prefixEnd_1950177 := by exact prefixLift 1950177
  have htrace : WordTrace (prefixWord ++ tailWord_1950177) baseStart_1950177 baseEnd_1950177 := by
    simpa [prefixWord, tailWord_1950177, baseEnd_1950177] using wordTrace_append hprefix tailTrace_1950177
  have hstable : (prefixWord ++ tailWord_1950177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950177).length < 2 ^ (prefixWord ++ tailWord_1950177).sum := by decide
  have hdescent : baseEnd_1950177 < baseStart_1950177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950234 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1950234 : Nat := 118140960795 + 1950234 * 2 ^ 59
def prefixEnd_1950234 : Nat := 4983230072969 + 3 ^ 40 * 1950234 * 2
def baseEnd_1950234 : Nat := 1001407430740627934206043

theorem tailTrace_1950234 : CollatzResearch.WordTrace tailWord_1950234 prefixEnd_1950234 1001407430740627934206043 := by
  unfold tailWord_1950234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782719404160691573744439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47420585077761844196651837 17782719404160691573744439)
  ·
    refine ⟨26674079106241037360616659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17782719404160691573744439 26674079106241037360616659)
    ·
      refine ⟨40011118659361556040924989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26674079106241037360616659 40011118659361556040924989)
      ·
        refine ⟨15004169497260583515346871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40011118659361556040924989 15004169497260583515346871)
        ·
          refine ⟨22506254245890875273020307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004169497260583515346871 22506254245890875273020307)
          ·
            refine ⟨33759381368836312909530461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22506254245890875273020307 33759381368836312909530461)
            ·
              refine ⟨12659768013313617341073923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33759381368836312909530461 12659768013313617341073923)
              ·
                refine ⟨18989652019970426011610885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659768013313617341073923 18989652019970426011610885)
                ·
                  refine ⟨3560559753744454877177041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18989652019970426011610885 3560559753744454877177041)
                  ·
                    refine ⟨2670419815308341157882781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560559753744454877177041 2670419815308341157882781)
                    ·
                      refine ⟨1001407430740627934206043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2670419815308341157882781 1001407430740627934206043)
                      ·
                        rfl

theorem cell23_1950234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1950234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950234 prefixEnd_1950234 := by exact prefixLift 1950234
  have htrace : WordTrace (prefixWord ++ tailWord_1950234) baseStart_1950234 baseEnd_1950234 := by
    simpa [prefixWord, tailWord_1950234, baseEnd_1950234] using wordTrace_append hprefix tailTrace_1950234
  have hstable : (prefixWord ++ tailWord_1950234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950234).length < 2 ^ (prefixWord ++ tailWord_1950234).sum := by decide
  have hdescent : baseEnd_1950234 < baseStart_1950234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950257 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1950257 : Nat := 118140960795 + 1950257 * 2 ^ 59
def prefixEnd_1950257 : Nat := 4983230072969 + 3 ^ 40 * 1950257 * 2
def baseEnd_1950257 : Nat := 1001419240795681344218437

theorem tailTrace_1950257 : CollatzResearch.WordTrace tailWord_1950257 prefixEnd_1950257 1001419240795681344218437 := by
  unfold tailWord_1950257
  simp only [CollatzResearch.WordTrace]
  refine ⟨71131716495559441223065025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47421144330372960815376683 71131716495559441223065025)
  ·
    refine ⟨53348787371669580917298769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71131716495559441223065025 53348787371669580917298769)
    ·
      refine ⟨40011590528752185687974077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53348787371669580917298769 40011590528752185687974077)
      ·
        refine ⟨15004346448282069632990279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40011590528752185687974077 15004346448282069632990279)
        ·
          refine ⟨22506519672423104449485419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004346448282069632990279 22506519672423104449485419)
          ·
            refine ⟨33759779508634656674228129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22506519672423104449485419 33759779508634656674228129)
            ·
              refine ⟨25319834631475992505671097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33759779508634656674228129 25319834631475992505671097)
              ·
                refine ⟨18989875973606994379253323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25319834631475992505671097 18989875973606994379253323)
                ·
                  refine ⟨28484813960410491568879985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18989875973606994379253323 28484813960410491568879985)
                  ·
                    refine ⟨21363610470307868676659989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28484813960410491568879985 21363610470307868676659989)
                    ·
                      refine ⟨1001419240795681344218437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21363610470307868676659989 1001419240795681344218437)
                      ·
                        rfl

theorem cell23_1950257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1950257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950257 prefixEnd_1950257 := by exact prefixLift 1950257
  have htrace : WordTrace (prefixWord ++ tailWord_1950257) baseStart_1950257 baseEnd_1950257 := by
    simpa [prefixWord, tailWord_1950257, baseEnd_1950257] using wordTrace_append hprefix tailTrace_1950257
  have hstable : (prefixWord ++ tailWord_1950257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950257).length < 2 ^ (prefixWord ++ tailWord_1950257).sum := by decide
  have hdescent : baseEnd_1950257 < baseStart_1950257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950304 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1950304 : Nat := 118140960795 + 1950304 * 2 ^ 59
def prefixEnd_1950304 : Nat := 4983230072969 + 3 ^ 40 * 1950304 * 2
def baseEnd_1950304 : Nat := 1001443374386442660330721

theorem tailTrace_1950304 : CollatzResearch.WordTrace tailWord_1950304 prefixEnd_1950304 1001443374386442660330721 := by
  unfold tailWord_1950304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566715363194584125012983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47422287150926112166683977 35566715363194584125012983)
  ·
    refine ⟨53350073044791876187519475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566715363194584125012983 53350073044791876187519475)
    ·
      refine ⟨80025109567187814281279213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53350073044791876187519475 80025109567187814281279213)
      ·
        refine ⟨30009416087695430355479705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80025109567187814281279213 30009416087695430355479705)
        ·
          refine ⟨22507062065771572766609779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30009416087695430355479705 22507062065771572766609779)
          ·
            refine ⟨33760593098657359149914669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22507062065771572766609779 33760593098657359149914669)
            ·
              refine ⟨12660222411996509681218001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33760593098657359149914669 12660222411996509681218001)
              ·
                refine ⟨9495166808997382260913501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660222411996509681218001 9495166808997382260913501)
                ·
                  refine ⟨3560687553374018347842563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495166808997382260913501 3560687553374018347842563)
                  ·
                    refine ⟨5341031330061027521763845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560687553374018347842563 5341031330061027521763845)
                    ·
                      refine ⟨1001443374386442660330721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5341031330061027521763845 1001443374386442660330721)
                      ·
                        rfl

theorem cell23_1950304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1950304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950304 prefixEnd_1950304 := by exact prefixLift 1950304
  have htrace : WordTrace (prefixWord ++ tailWord_1950304) baseStart_1950304 baseEnd_1950304 := by
    simpa [prefixWord, tailWord_1950304, baseEnd_1950304] using wordTrace_append hprefix tailTrace_1950304
  have hstable : (prefixWord ++ tailWord_1950304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950304).length < 2 ^ (prefixWord ++ tailWord_1950304).sum := by decide
  have hdescent : baseEnd_1950304 < baseStart_1950304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950327 : List Nat := [1, 1, 3, 1, 1, 3, 2, 11]
def baseStart_1950327 : Nat := 118140960795 + 1950327 * 2 ^ 59
def prefixEnd_1950327 : Nat := 4983230072969 + 3 ^ 40 * 1950327 * 2
def baseEnd_1950327 : Nat := 37090932757092447049745

theorem tailTrace_1950327 : CollatzResearch.WordTrace tailWord_1950327 prefixEnd_1950327 37090932757092447049745 := by
  unfold tailWord_1950327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71134269605305843178113235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47422846403537228785408823 71134269605305843178113235)
  ·
    refine ⟨106701404407958764767169853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71134269605305843178113235 106701404407958764767169853)
    ·
      refine ⟨40013026652984536787688695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106701404407958764767169853 40013026652984536787688695)
      ·
        refine ⟨60019539979476805181533043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40013026652984536787688695 60019539979476805181533043)
        ·
          refine ⟨90029309969215207772299565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60019539979476805181533043 90029309969215207772299565)
          ·
            refine ⟨33760991238455702914612337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90029309969215207772299565 33760991238455702914612337)
            ·
              refine ⟨25320743428841777185959253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33760991238455702914612337 25320743428841777185959253)
              ·
                refine ⟨37090932757092447049745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25320743428841777185959253 37090932757092447049745)
                ·
                  rfl

theorem cell23_1950327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 11].length) (baseStart_1950327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950327 prefixEnd_1950327 := by exact prefixLift 1950327
  have htrace : WordTrace (prefixWord ++ tailWord_1950327) baseStart_1950327 baseEnd_1950327 := by
    simpa [prefixWord, tailWord_1950327, baseEnd_1950327] using wordTrace_append hprefix tailTrace_1950327
  have hstable : (prefixWord ++ tailWord_1950327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950327).length < 2 ^ (prefixWord ++ tailWord_1950327).sum := by decide
  have hdescent : baseEnd_1950327 < baseStart_1950327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950368 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1950368 : Nat := 118140960795 + 1950368 * 2 ^ 59
def prefixEnd_1950368 : Nat := 4983230072969 + 3 ^ 40 * 1950368 * 2
def baseEnd_1950368 : Nat := 1001476237148330409930427

theorem tailTrace_1950368 : CollatzResearch.WordTrace tailWord_1950368 prefixEnd_1950368 1001476237148330409930427 := by
  unfold tailWord_1950368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35567882499078653590177879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47423843332104871453570505 35567882499078653590177879)
  ·
    refine ⟨53351823748617980385266819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35567882499078653590177879 53351823748617980385266819)
    ·
      refine ⟨80027735622926970577900229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53351823748617980385266819 80027735622926970577900229)
      ·
        refine ⟨15005200429298806983356293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80027735622926970577900229 15005200429298806983356293)
        ·
          refine ⟨2813475080493526309379305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15005200429298806983356293 2813475080493526309379305)
          ·
            refine ⟨2110106310370144732034479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813475080493526309379305 2110106310370144732034479)
            ·
              refine ⟨3165159465555217098051719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110106310370144732034479 3165159465555217098051719)
              ·
                refine ⟨4747739198332825647077579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165159465555217098051719 4747739198332825647077579)
                ·
                  refine ⟨7121608797499238470616369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747739198332825647077579 7121608797499238470616369)
                  ·
                    refine ⟨5341206598124428852962277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7121608797499238470616369 5341206598124428852962277)
                    ·
                      refine ⟨1001476237148330409930427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5341206598124428852962277 1001476237148330409930427)
                      ·
                        rfl

theorem cell23_1950368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1950368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950368 prefixEnd_1950368 := by exact prefixLift 1950368
  have htrace : WordTrace (prefixWord ++ tailWord_1950368) baseStart_1950368 baseEnd_1950368 := by
    simpa [prefixWord, tailWord_1950368, baseEnd_1950368] using wordTrace_append hprefix tailTrace_1950368
  have hstable : (prefixWord ++ tailWord_1950368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950368).length < 2 ^ (prefixWord ++ tailWord_1950368).sum := by decide
  have hdescent : baseEnd_1950368 < baseStart_1950368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950378 : List Nat := [3, 1, 5, 2, 1, 1, 1, 9]
def baseStart_1950378 : Nat := 118140960795 + 1950378 * 2 ^ 59
def prefixEnd_1950378 : Nat := 4983230072969 + 3 ^ 40 * 1950378 * 2
def baseEnd_1950378 : Nat := 37091902664995384103903

theorem tailTrace_1950378 : CollatzResearch.WordTrace tailWord_1950378 prefixEnd_1950378 37091902664995384103903 := by
  unfold tailWord_1950378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17784032432030269722054947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47424086485414052592146525 17784032432030269722054947)
  ·
    refine ⟨26676048648045404583082421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17784032432030269722054947 26676048648045404583082421)
    ·
      refine ⟨2500879560754256679663977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26676048648045404583082421 2500879560754256679663977)
      ·
        refine ⟨1875659670565692509747983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2500879560754256679663977 1875659670565692509747983)
        ·
          refine ⟨2813489505848538764621975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875659670565692509747983 2813489505848538764621975)
          ·
            refine ⟨4220234258772808146932963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813489505848538764621975 4220234258772808146932963)
            ·
              refine ⟨6330351388159212220399445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220234258772808146932963 6330351388159212220399445)
              ·
                refine ⟨37091902664995384103903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6330351388159212220399445 37091902664995384103903)
                ·
                  rfl

theorem cell23_1950378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_1950378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950378 prefixEnd_1950378 := by exact prefixLift 1950378
  have htrace : WordTrace (prefixWord ++ tailWord_1950378) baseStart_1950378 baseEnd_1950378 := by
    simpa [prefixWord, tailWord_1950378, baseEnd_1950378] using wordTrace_append hprefix tailTrace_1950378
  have hstable : (prefixWord ++ tailWord_1950378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950378).length < 2 ^ (prefixWord ++ tailWord_1950378).sum := by decide
  have hdescent : baseEnd_1950378 < baseStart_1950378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950389 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1950389 : Nat := 118140960795 + 1950389 * 2 ^ 59
def prefixEnd_1950389 : Nat := 4983230072969 + 3 ^ 40 * 1950389 * 2
def baseEnd_1950389 : Nat := 1001487020242074827767831

theorem tailTrace_1950389 : CollatzResearch.WordTrace tailWord_1950389 prefixEnd_1950389 1001487020242074827767831 := by
  unfold tailWord_1950389
  simp only [CollatzResearch.WordTrace]
  refine ⟨71136530931081227766870221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47424353954054151844580147 71136530931081227766870221)
  ·
    refine ⟨26676199099155460412576333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71136530931081227766870221 26676199099155460412576333)
    ·
      refine ⟨10003574662183297654716125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26676199099155460412576333 10003574662183297654716125)
      ·
        refine ⟨3751340498318736620518547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10003574662183297654716125 3751340498318736620518547)
        ·
          refine ⟨5627010747478104930777821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751340498318736620518547 5627010747478104930777821)
          ·
            refine ⟨2110129030304289349041683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5627010747478104930777821 2110129030304289349041683)
            ·
              refine ⟨3165193545456434023562525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110129030304289349041683 3165193545456434023562525)
              ·
                refine ⟨1186947579546162758835947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3165193545456434023562525 1186947579546162758835947)
                ·
                  refine ⟨1780421369319244138253921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186947579546162758835947 1780421369319244138253921)
                  ·
                    refine ⟨1335316026989433103690441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780421369319244138253921 1335316026989433103690441)
                    ·
                      refine ⟨1001487020242074827767831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335316026989433103690441 1001487020242074827767831)
                      ·
                        rfl

theorem cell23_1950389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1950389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950389 prefixEnd_1950389 := by exact prefixLift 1950389
  have htrace : WordTrace (prefixWord ++ tailWord_1950389) baseStart_1950389 baseEnd_1950389 := by
    simpa [prefixWord, tailWord_1950389, baseEnd_1950389] using wordTrace_append hprefix tailTrace_1950389
  have hstable : (prefixWord ++ tailWord_1950389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950389).length < 2 ^ (prefixWord ++ tailWord_1950389).sum := by decide
  have hdescent : baseEnd_1950389 < baseStart_1950389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950406 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1950406 : Nat := 118140960795 + 1950406 * 2 ^ 59
def prefixEnd_1950406 : Nat := 4983230072969 + 3 ^ 40 * 1950406 * 2
def baseEnd_1950406 : Nat := 1001495749413201261255253

theorem tailTrace_1950406 : CollatzResearch.WordTrace tailWord_1950406 prefixEnd_1950406 1001495749413201261255253 := by
  unfold tailWord_1950406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223035967875613739694971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47424767314679759780159381 2223035967875613739694971)
  ·
    refine ⟨3334553951813420609542457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223035967875613739694971 3334553951813420609542457)
    ·
      refine ⟨2500915463860065457156843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334553951813420609542457 2500915463860065457156843)
      ·
        refine ⟨3751373195790098185735265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500915463860065457156843 3751373195790098185735265)
        ·
          refine ⟨2813529896842573639301449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751373195790098185735265 2813529896842573639301449)
          ·
            refine ⟨2110147422631930229476087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2813529896842573639301449 2110147422631930229476087)
            ·
              refine ⟨3165221133947895344214131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110147422631930229476087 3165221133947895344214131)
              ·
                refine ⟨4747831700921843016321197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165221133947895344214131 4747831700921843016321197)
                ·
                  refine ⟨1780436887845691131120449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4747831700921843016321197 1780436887845691131120449)
                  ·
                    refine ⟨1335327665884268348340337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780436887845691131120449 1335327665884268348340337)
                    ·
                      refine ⟨1001495749413201261255253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335327665884268348340337 1001495749413201261255253)
                      ·
                        rfl

theorem cell23_1950406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1950406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950406 prefixEnd_1950406 := by exact prefixLift 1950406
  have htrace : WordTrace (prefixWord ++ tailWord_1950406) baseStart_1950406 baseEnd_1950406 := by
    simpa [prefixWord, tailWord_1950406, baseEnd_1950406] using wordTrace_append hprefix tailTrace_1950406
  have hstable : (prefixWord ++ tailWord_1950406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950406).length < 2 ^ (prefixWord ++ tailWord_1950406).sum := by decide
  have hdescent : baseEnd_1950406 < baseStart_1950406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950451 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 5]
def baseStart_1950451 : Nat := 118140960795 + 1950451 * 2 ^ 59
def prefixEnd_1950451 : Nat := 4983230072969 + 3 ^ 40 * 1950451 * 2
def baseEnd_1950451 : Nat := 111279872893628176132505

theorem tailTrace_1950451 : CollatzResearch.WordTrace tailWord_1950451 prefixEnd_1950451 111279872893628176132505 := by
  unfold tailWord_1950451
  simp only [CollatzResearch.WordTrace]
  refine ⟨71138792256856612355627207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47425861504571074903751471 71138792256856612355627207)
  ·
    refine ⟨106708188385284918533440811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71138792256856612355627207 106708188385284918533440811)
    ·
      refine ⟨160062282577927377800161217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106708188385284918533440811 160062282577927377800161217)
      ·
        refine ⟨120046711933445533350120913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160062282577927377800161217 120046711933445533350120913)
        ·
          refine ⟨90035033950084150012590685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120046711933445533350120913 90035033950084150012590685)
          ·
            refine ⟨33763137731281556254721507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90035033950084150012590685 33763137731281556254721507)
            ·
              refine ⟨50644706596922334382082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33763137731281556254721507 50644706596922334382082261)
              ·
                refine ⟨1186985310865367212080053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50644706596922334382082261 1186985310865367212080053)
                ·
                  refine ⟨111279872893628176132505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1186985310865367212080053 111279872893628176132505)
                  ·
                    rfl

theorem cell23_1950451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 5].length) (baseStart_1950451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950451 prefixEnd_1950451 := by exact prefixLift 1950451
  have htrace : WordTrace (prefixWord ++ tailWord_1950451) baseStart_1950451 baseEnd_1950451 := by
    simpa [prefixWord, tailWord_1950451, baseEnd_1950451] using wordTrace_append hprefix tailTrace_1950451
  have hstable : (prefixWord ++ tailWord_1950451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950451).length < 2 ^ (prefixWord ++ tailWord_1950451).sum := by decide
  have hdescent : baseEnd_1950451 < baseStart_1950451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950461 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_1950461 : Nat := 118140960795 + 1950461 * 2 ^ 59
def prefixEnd_1950461 : Nat := 4983230072969 + 3 ^ 40 * 1950461 * 2
def baseEnd_1950461 : Nat := 1001523990849198546067499

theorem tailTrace_1950461 : CollatzResearch.WordTrace tailWord_1950461 prefixEnd_1950461 1001523990849198546067499 := by
  unfold tailWord_1950461
  simp only [CollatzResearch.WordTrace]
  refine ⟨71139156986820384063491237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47426104657880256042327491 71139156986820384063491237)
  ·
    refine ⟨13338591935028822011904607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71139156986820384063491237 13338591935028822011904607)
    ·
      refine ⟨20007887902543233017856911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338591935028822011904607 20007887902543233017856911)
      ·
        refine ⟨30011831853814849526785367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007887902543233017856911 30011831853814849526785367)
        ·
          refine ⟨45017747780722274290178051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30011831853814849526785367 45017747780722274290178051)
          ·
            refine ⟨67526621671083411435267077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45017747780722274290178051 67526621671083411435267077)
            ·
              refine ⟨12661241563328139644112577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67526621671083411435267077 12661241563328139644112577)
              ·
                refine ⟨9495931172496104733084433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12661241563328139644112577 9495931172496104733084433)
                ·
                  refine ⟨7121948379372078549813325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495931172496104733084433 7121948379372078549813325)
                  ·
                    refine ⟨2670730642264529456179997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7121948379372078549813325 2670730642264529456179997)
                    ·
                      refine ⟨1001523990849198546067499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2670730642264529456179997 1001523990849198546067499)
                      ·
                        rfl

theorem cell23_1950461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_1950461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950461 prefixEnd_1950461 := by exact prefixLift 1950461
  have htrace : WordTrace (prefixWord ++ tailWord_1950461) baseStart_1950461 baseEnd_1950461 := by
    simpa [prefixWord, tailWord_1950461, baseEnd_1950461] using wordTrace_append hprefix tailTrace_1950461
  have hstable : (prefixWord ++ tailWord_1950461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950461).length < 2 ^ (prefixWord ++ tailWord_1950461).sum := by decide
  have hdescent : baseEnd_1950461 < baseStart_1950461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950462 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1950462 : Nat := 118140960795 + 1950462 * 2 ^ 59
def prefixEnd_1950462 : Nat := 4983230072969 + 3 ^ 40 * 1950462 * 2
def baseEnd_1950462 : Nat := 1001524504329853042154995

theorem tailTrace_1950462 : CollatzResearch.WordTrace tailWord_1950462 prefixEnd_1950462 1001524504329853042154995 := by
  unfold tailWord_1950462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892399182477095154284705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47426128973211174156185093 8892399182477095154284705)
  ·
    refine ⟨6669299386857821365713529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8892399182477095154284705 6669299386857821365713529)
    ·
      refine ⟨5001974540143366024285147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669299386857821365713529 5001974540143366024285147)
      ·
        refine ⟨7502961810215049036427721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001974540143366024285147 7502961810215049036427721)
        ·
          refine ⟨5627221357661286777320791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7502961810215049036427721 5627221357661286777320791)
          ·
            refine ⟨8440832036491930165981187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627221357661286777320791 8440832036491930165981187)
            ·
              refine ⟨12661248054737895248971781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440832036491930165981187 12661248054737895248971781)
              ·
                refine ⟨2373984010263355359182209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12661248054737895248971781 2373984010263355359182209)
                ·
                  refine ⟨1780488007697516519386657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373984010263355359182209 1780488007697516519386657)
                  ·
                    refine ⟨1335366005773137389539993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780488007697516519386657 1335366005773137389539993)
                    ·
                      refine ⟨1001524504329853042154995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335366005773137389539993 1001524504329853042154995)
                      ·
                        rfl

theorem cell23_1950462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1950462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950462 prefixEnd_1950462 := by exact prefixLift 1950462
  have htrace : WordTrace (prefixWord ++ tailWord_1950462) baseStart_1950462 baseEnd_1950462 := by
    simpa [prefixWord, tailWord_1950462, baseEnd_1950462] using wordTrace_append hprefix tailTrace_1950462
  have hstable : (prefixWord ++ tailWord_1950462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950462).length < 2 ^ (prefixWord ++ tailWord_1950462).sum := by decide
  have hdescent : baseEnd_1950462 < baseStart_1950462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950468 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 5]
def baseStart_1950468 : Nat := 118140960795 + 1950468 * 2 ^ 59
def prefixEnd_1950468 : Nat := 4983230072969 + 3 ^ 40 * 1950468 * 2
def baseEnd_1950468 : Nat := 111280842801531113186663

theorem tailTrace_1950468 : CollatzResearch.WordTrace tailWord_1950468 prefixEnd_1950468 111280842801531113186663 := by
  unfold tailWord_1950468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569706148897512129498029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47426274865196682839330705 35569706148897512129498029)
  ·
    refine ⟨13338639805836567048561761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35569706148897512129498029 13338639805836567048561761)
    ·
      refine ⟨10003979854377425286421321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13338639805836567048561761 10003979854377425286421321)
      ·
        refine ⟨7502984890783068964815991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10003979854377425286421321 7502984890783068964815991)
        ·
          refine ⟨11254477336174603447223987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502984890783068964815991 11254477336174603447223987)
          ·
            refine ⟨16881716004261905170835981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254477336174603447223987 16881716004261905170835981)
            ·
              refine ⟨6330643501598214439063493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16881716004261905170835981 6330643501598214439063493)
              ·
                refine ⟨1186995656549665207324405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6330643501598214439063493 1186995656549665207324405)
                ·
                  refine ⟨111280842801531113186663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1186995656549665207324405 111280842801531113186663)
                  ·
                    rfl

theorem cell23_1950468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_1950468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950468 prefixEnd_1950468 := by exact prefixLift 1950468
  have htrace : WordTrace (prefixWord ++ tailWord_1950468) baseStart_1950468 baseEnd_1950468 := by
    simpa [prefixWord, tailWord_1950468, baseEnd_1950468] using wordTrace_append hprefix tailTrace_1950468
  have hstable : (prefixWord ++ tailWord_1950468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950468).length < 2 ^ (prefixWord ++ tailWord_1950468).sum := by decide
  have hdescent : baseEnd_1950468 < baseStart_1950468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950498 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1950498 : Nat := 118140960795 + 1950498 * 2 ^ 59
def prefixEnd_1950498 : Nat := 4983230072969 + 3 ^ 40 * 1950498 * 2
def baseEnd_1950498 : Nat := 333847663211138300434943

theorem tailTrace_1950498 : CollatzResearch.WordTrace tailWord_1950498 prefixEnd_1950498 333847663211138300434943 := by
  unfold tailWord_1950498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17785126621921584845647037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47427004325124226255058765 17785126621921584845647037)
  ·
    refine ⟨6669422483220594317117639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17785126621921584845647037 6669422483220594317117639)
    ·
      refine ⟨10004133724830891475676459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669422483220594317117639 10004133724830891475676459)
      ·
        refine ⟨15006200587246337213514689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10004133724830891475676459 15006200587246337213514689)
        ·
          refine ⟨11254650440434752910136017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15006200587246337213514689 11254650440434752910136017)
          ·
            refine ⟨8440987830326064682602013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11254650440434752910136017 8440987830326064682602013)
            ·
              refine ⟨3165370436372274255975755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8440987830326064682602013 3165370436372274255975755)
              ·
                refine ⟨4748055654558411383963633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165370436372274255975755 4748055654558411383963633)
                ·
                  refine ⟨3561041740918808537972725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4748055654558411383963633 3561041740918808537972725)
                  ·
                    refine ⟨333847663211138300434943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3561041740918808537972725 333847663211138300434943)
                    ·
                      rfl

theorem cell23_1950498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1950498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950498 prefixEnd_1950498 := by exact prefixLift 1950498
  have htrace : WordTrace (prefixWord ++ tailWord_1950498) baseStart_1950498 baseEnd_1950498 := by
    simpa [prefixWord, tailWord_1950498, baseEnd_1950498] using wordTrace_append hprefix tailTrace_1950498
  have hstable : (prefixWord ++ tailWord_1950498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950498).length < 2 ^ (prefixWord ++ tailWord_1950498).sum := by decide
  have hdescent : baseEnd_1950498 < baseStart_1950498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950501 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1950501 : Nat := 118140960795 + 1950501 * 2 ^ 59
def prefixEnd_1950501 : Nat := 4983230072969 + 3 ^ 40 * 1950501 * 2
def baseEnd_1950501 : Nat := 1001544530075378389567315

theorem tailTrace_1950501 : CollatzResearch.WordTrace tailWord_1950501 prefixEnd_1950501 1001544530075378389567315 := by
  unfold tailWord_1950501
  simp only [CollatzResearch.WordTrace]
  refine ⟨71140615906675470894947357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47427077271116980596631571 71140615906675470894947357)
  ·
    refine ⟨26677730965003301585605259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71140615906675470894947357 26677730965003301585605259)
    ·
      refine ⟨40016596447504952378407889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26677730965003301585605259 40016596447504952378407889)
      ·
        refine ⟨30012447335628714283805917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40016596447504952378407889 30012447335628714283805917)
        ·
          refine ⟨11254667750860767856427219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30012447335628714283805917 11254667750860767856427219)
          ·
            refine ⟨16882001626291151784640829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254667750860767856427219 16882001626291151784640829)
            ·
              refine ⟨6330750609859181919240311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16882001626291151784640829 6330750609859181919240311)
              ·
                refine ⟨9496125914788772878860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330750609859181919240311 9496125914788772878860467)
                ·
                  refine ⟨14244188872183159318290701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496125914788772878860467 14244188872183159318290701)
                  ·
                    refine ⟨5341570827068684744359013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14244188872183159318290701 5341570827068684744359013)
                    ·
                      refine ⟨1001544530075378389567315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5341570827068684744359013 1001544530075378389567315)
                      ·
                        rfl

theorem cell23_1950501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1950501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950501 prefixEnd_1950501 := by exact prefixLift 1950501
  have htrace : WordTrace (prefixWord ++ tailWord_1950501) baseStart_1950501 baseEnd_1950501 := by
    simpa [prefixWord, tailWord_1950501, baseEnd_1950501] using wordTrace_append hprefix tailTrace_1950501
  have hstable : (prefixWord ++ tailWord_1950501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950501).length < 2 ^ (prefixWord ++ tailWord_1950501).sum := by decide
  have hdescent : baseEnd_1950501 < baseStart_1950501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950585 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1950585 : Nat := 118140960795 + 1950585 * 2 ^ 59
def prefixEnd_1950585 : Nat := 4983230072969 + 3 ^ 40 * 1950585 * 2
def baseEnd_1950585 : Nat := 1001587662450356060916929

theorem tailTrace_1950585 : CollatzResearch.WordTrace tailWord_1950585 prefixEnd_1950585 1001587662450356060916929 := by
  unfold tailWord_1950585
  simp only [CollatzResearch.WordTrace]
  refine ⟨71143679638371153241005209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47429119758914102160670139 71143679638371153241005209)
  ·
    refine ⟨53357759728778364930753907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71143679638371153241005209 53357759728778364930753907)
    ·
      refine ⟨80036639593167547396130861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53357759728778364930753907 80036639593167547396130861)
      ·
        refine ⟨30013739847437830273549073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80036639593167547396130861 30013739847437830273549073)
        ·
          refine ⟨22510304885578372705161805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30013739847437830273549073 22510304885578372705161805)
          ·
            refine ⟨8441364332091889764435677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22510304885578372705161805 8441364332091889764435677)
            ·
              refine ⟨3165511624534458661663379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8441364332091889764435677 3165511624534458661663379)
              ·
                refine ⟨4748267436801687992495069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165511624534458661663379 4748267436801687992495069)
                ·
                  refine ⟨1780600288800632997185651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748267436801687992495069 1780600288800632997185651)
                  ·
                    refine ⟨2670900433200949495778477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1780600288800632997185651 2670900433200949495778477)
                    ·
                      refine ⟨1001587662450356060916929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2670900433200949495778477 1001587662450356060916929)
                      ·
                        rfl

theorem cell23_1950585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1950585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950585 prefixEnd_1950585 := by exact prefixLift 1950585
  have htrace : WordTrace (prefixWord ++ tailWord_1950585) baseStart_1950585 baseEnd_1950585 := by
    simpa [prefixWord, tailWord_1950585, baseEnd_1950585] using wordTrace_append hprefix tailTrace_1950585
  have hstable : (prefixWord ++ tailWord_1950585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950585).length < 2 ^ (prefixWord ++ tailWord_1950585).sum := by decide
  have hdescent : baseEnd_1950585 < baseStart_1950585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950612 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1950612 : Nat := 118140960795 + 1950612 * 2 ^ 59
def prefixEnd_1950612 : Nat := 4983230072969 + 3 ^ 40 * 1950612 * 2
def baseEnd_1950612 : Nat := 1001601526428027455279305

theorem tailTrace_1950612 : CollatzResearch.WordTrace tailWord_1950612 prefixEnd_1950612 1001601526428027455279305 := by
  unfold tailWord_1950612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35572332204636668426119045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47429776272848891234825393 35572332204636668426119045)
  ·
    refine ⟨6669812288369375329897321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35572332204636668426119045 6669812288369375329897321)
    ·
      refine ⟨5002359216277031497422991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669812288369375329897321 5002359216277031497422991)
      ·
        refine ⟨7503538824415547246134487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002359216277031497422991 7503538824415547246134487)
        ·
          refine ⟨11255308236623320869201731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503538824415547246134487 11255308236623320869201731)
          ·
            refine ⟨16882962354934981303802597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255308236623320869201731 16882962354934981303802597)
            ·
              refine ⟨3165555441550308994462987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16882962354934981303802597 3165555441550308994462987)
              ·
                refine ⟨4748333162325463491694481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165555441550308994462987 4748333162325463491694481)
                ·
                  refine ⟨3561249871744097618770861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4748333162325463491694481 3561249871744097618770861)
                  ·
                    refine ⟨1335468701904036607039073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561249871744097618770861 1335468701904036607039073)
                    ·
                      refine ⟨1001601526428027455279305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335468701904036607039073 1001601526428027455279305)
                      ·
                        rfl

theorem cell23_1950612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1950612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950612 prefixEnd_1950612 := by exact prefixLift 1950612
  have htrace : WordTrace (prefixWord ++ tailWord_1950612) baseStart_1950612 baseEnd_1950612 := by
    simpa [prefixWord, tailWord_1950612, baseEnd_1950612] using wordTrace_append hprefix tailTrace_1950612
  have hstable : (prefixWord ++ tailWord_1950612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950612).length < 2 ^ (prefixWord ++ tailWord_1950612).sum := by decide
  have hdescent : baseEnd_1950612 < baseStart_1950612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950631 : List Nat := [1, 1, 6, 1, 14]
def baseStart_1950631 : Nat := 118140960795 + 1950631 * 2 ^ 59
def prefixEnd_1950631 : Nat := 4983230072969 + 3 ^ 40 * 1950631 * 2
def baseEnd_1950631 : Nat := 1373952376626149356573

theorem tailTrace_1950631 : CollatzResearch.WordTrace tailWord_1950631 prefixEnd_1950631 1373952376626149356573 := by
  unfold tailWord_1950631
  simp only [CollatzResearch.WordTrace]
  refine ⟨71145357396204503097179747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47430238264136335398119831 71145357396204503097179747)
  ·
    refine ⟨106718036094306754645769621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71145357396204503097179747 106718036094306754645769621)
    ·
      refine ⟨5002407941920629124020451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106718036094306754645769621 5002407941920629124020451)
      ·
        refine ⟨7503611912880943686030677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002407941920629124020451 7503611912880943686030677)
        ·
          refine ⟨1373952376626149356573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 7503611912880943686030677 1373952376626149356573)
          ·
            rfl

theorem cell23_1950631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 14].length) (baseStart_1950631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950631 prefixEnd_1950631 := by exact prefixLift 1950631
  have htrace : WordTrace (prefixWord ++ tailWord_1950631) baseStart_1950631 baseEnd_1950631 := by
    simpa [prefixWord, tailWord_1950631, baseEnd_1950631] using wordTrace_append hprefix tailTrace_1950631
  have hstable : (prefixWord ++ tailWord_1950631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950631).length < 2 ^ (prefixWord ++ tailWord_1950631).sum := by decide
  have hdescent : baseEnd_1950631 < baseStart_1950631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950648 : List Nat := [2, 1, 2, 1, 2, 6, 1, 8]
def baseStart_1950648 : Nat := 118140960795 + 1950648 * 2 ^ 59
def prefixEnd_1950648 : Nat := 4983230072969 + 3 ^ 40 * 1950648 * 2
def baseEnd_1950648 : Nat := 37097037471540344978857

theorem tailTrace_1950648 : CollatzResearch.WordTrace tailWord_1950648 prefixEnd_1950648 37097037471540344978857 := by
  unfold tailWord_1950648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35572988718571457500274299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47430651624761943333699065 35572988718571457500274299)
  ·
    refine ⟨53359483077857186250411449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35572988718571457500274299 53359483077857186250411449)
    ·
      refine ⟨40019612308392889687808587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53359483077857186250411449 40019612308392889687808587)
      ·
        refine ⟨60029418462589334531712881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40019612308392889687808587 60029418462589334531712881)
        ·
          refine ⟨45022063846942000898784661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60029418462589334531712881 45022063846942000898784661)
          ·
            refine ⟨2110409242825406292130531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45022063846942000898784661 2110409242825406292130531)
            ·
              refine ⟨3165613864238109438195797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110409242825406292130531 3165613864238109438195797)
              ·
                refine ⟨37097037471540344978857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3165613864238109438195797 37097037471540344978857)
                ·
                  rfl

theorem cell23_1950648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 8].length) (baseStart_1950648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950648 prefixEnd_1950648 := by exact prefixLift 1950648
  have htrace : WordTrace (prefixWord ++ tailWord_1950648) baseStart_1950648 baseEnd_1950648 := by
    simpa [prefixWord, tailWord_1950648, baseEnd_1950648] using wordTrace_append hprefix tailTrace_1950648
  have hstable : (prefixWord ++ tailWord_1950648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950648).length < 2 ^ (prefixWord ++ tailWord_1950648).sum := by decide
  have hdescent : baseEnd_1950648 < baseStart_1950648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950676 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1950676 : Nat := 118140960795 + 1950676 * 2 ^ 59
def prefixEnd_1950676 : Nat := 4983230072969 + 3 ^ 40 * 1950676 * 2
def baseEnd_1950676 : Nat := 1001634389189915204879011

theorem tailTrace_1950676 : CollatzResearch.WordTrace tailWord_1950676 prefixEnd_1950676 1001634389189915204879011 := by
  unfold tailWord_1950676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35573499340520737891283941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47431332454027650521711921 35573499340520737891283941)
  ·
    refine ⟨6670031126347638354615739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35573499340520737891283941 6670031126347638354615739)
    ·
      refine ⟨10005046689521457531923609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6670031126347638354615739 10005046689521457531923609)
      ·
        refine ⟨7503785017141093148942707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10005046689521457531923609 7503785017141093148942707)
        ·
          refine ⟨11255677525711639723414061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503785017141093148942707 11255677525711639723414061)
          ·
            refine ⟨4220879072141864896280273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11255677525711639723414061 4220879072141864896280273)
            ·
              refine ⟨3165659304106398672210205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220879072141864896280273 3165659304106398672210205)
              ·
                refine ⟨1187122239039899502078827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3165659304106398672210205 1187122239039899502078827)
                ·
                  refine ⟨1780683358559849253118241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187122239039899502078827 1780683358559849253118241)
                  ·
                    refine ⟨1335512518919886939838681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780683358559849253118241 1335512518919886939838681)
                    ·
                      refine ⟨1001634389189915204879011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335512518919886939838681 1001634389189915204879011)
                      ·
                        rfl

theorem cell23_1950676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1950676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950676 prefixEnd_1950676 := by exact prefixLift 1950676
  have htrace : WordTrace (prefixWord ++ tailWord_1950676) baseStart_1950676 baseEnd_1950676 := by
    simpa [prefixWord, tailWord_1950676, baseEnd_1950676] using wordTrace_append hprefix tailTrace_1950676
  have hstable : (prefixWord ++ tailWord_1950676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950676).length < 2 ^ (prefixWord ++ tailWord_1950676).sum := by decide
  have hdescent : baseEnd_1950676 < baseStart_1950676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950711 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1950711 : Nat := 118140960795 + 1950711 * 2 ^ 59
def prefixEnd_1950711 : Nat := 4983230072969 + 3 ^ 40 * 1950711 * 2
def baseEnd_1950711 : Nat := 1001652361012822567941349

theorem tailTrace_1950711 : CollatzResearch.WordTrace tailWord_1950711 prefixEnd_1950711 1001652361012822567941349 := by
  unfold tailWord_1950711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71148275235914676760091987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47432183490609784506727991 71148275235914676760091987)
  ·
    refine ⟨106722412853872015140137981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71148275235914676760091987 106722412853872015140137981)
    ·
      refine ⟨40020904820202005677551743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106722412853872015140137981 40020904820202005677551743)
      ·
        refine ⟨60031357230303008516327615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40020904820202005677551743 60031357230303008516327615)
        ·
          refine ⟨90047035845454512774491423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60031357230303008516327615 90047035845454512774491423)
          ·
            refine ⟨135070553768181769161737135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90047035845454512774491423 135070553768181769161737135)
            ·
              refine ⟨202605830652272653742605703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135070553768181769161737135 202605830652272653742605703)
              ·
                refine ⟨303908745978408980613908555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202605830652272653742605703 303908745978408980613908555)
                ·
                  refine ⟨455863118967613470920862833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303908745978408980613908555 455863118967613470920862833)
                  ·
                    refine ⟨341897339225710103190647125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455863118967613470920862833 341897339225710103190647125)
                    ·
                      refine ⟨1001652361012822567941349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 341897339225710103190647125 1001652361012822567941349)
                      ·
                        rfl

theorem cell23_1950711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1950711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950711 prefixEnd_1950711 := by exact prefixLift 1950711
  have htrace : WordTrace (prefixWord ++ tailWord_1950711) baseStart_1950711 baseEnd_1950711 := by
    simpa [prefixWord, tailWord_1950711, baseEnd_1950711] using wordTrace_append hprefix tailTrace_1950711
  have hstable : (prefixWord ++ tailWord_1950711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950711).length < 2 ^ (prefixWord ++ tailWord_1950711).sum := by decide
  have hdescent : baseEnd_1950711 < baseStart_1950711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950732 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_1950732 : Nat := 118140960795 + 1950732 * 2 ^ 59
def prefixEnd_1950732 : Nat := 4983230072969 + 3 ^ 40 * 1950732 * 2
def baseEnd_1950732 : Nat := 1001663144106566985778753

theorem tailTrace_1950732 : CollatzResearch.WordTrace tailWord_1950732 prefixEnd_1950732 1001663144106566985778753 := by
  unfold tailWord_1950732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574520584419298673303225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47432694112559064897737633 35574520584419298673303225)
  ·
    refine ⟨26680890438314474004977419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35574520584419298673303225 26680890438314474004977419)
    ·
      refine ⟨40021335657471711007466129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26680890438314474004977419 40021335657471711007466129)
      ·
        refine ⟨30016001743103783255599597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40021335657471711007466129 30016001743103783255599597)
        ·
          refine ⟨11256000653663918720849849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30016001743103783255599597 11256000653663918720849849)
          ·
            refine ⟨8442000490247939040637387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11256000653663918720849849 8442000490247939040637387)
            ·
              refine ⟨12663000735371908560956081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442000490247939040637387 12663000735371908560956081)
              ·
                refine ⟨9497250551528931420717061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663000735371908560956081 9497250551528931420717061)
                ·
                  refine ⟨1780734478411674641384449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9497250551528931420717061 1780734478411674641384449)
                  ·
                    refine ⟨1335550858808755981038337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780734478411674641384449 1335550858808755981038337)
                    ·
                      refine ⟨1001663144106566985778753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335550858808755981038337 1001663144106566985778753)
                      ·
                        rfl

theorem cell23_1950732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_1950732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950732 prefixEnd_1950732 := by exact prefixLift 1950732
  have htrace : WordTrace (prefixWord ++ tailWord_1950732) baseStart_1950732 baseEnd_1950732 := by
    simpa [prefixWord, tailWord_1950732, baseEnd_1950732] using wordTrace_append hprefix tailTrace_1950732
  have hstable : (prefixWord ++ tailWord_1950732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950732).length < 2 ^ (prefixWord ++ tailWord_1950732).sum := by decide
  have hdescent : baseEnd_1950732 < baseStart_1950732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950755 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 7]
def baseStart_1950755 : Nat := 118140960795 + 1950755 * 2 ^ 59
def prefixEnd_1950755 : Nat := 4983230072969 + 3 ^ 40 * 1950755 * 2
def baseEnd_1950755 : Nat := 111297217129068932865683

theorem tailTrace_1950755 : CollatzResearch.WordTrace tailWord_1950755 prefixEnd_1950755 111297217129068932865683 := by
  unfold tailWord_1950755
  simp only [CollatzResearch.WordTrace]
  refine ⟨71149880047755272274693719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47433253365170181516462479 71149880047755272274693719)
  ·
    refine ⟨106724820071632908412040579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71149880047755272274693719 106724820071632908412040579)
    ·
      refine ⟨160087230107449362618060869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106724820071632908412040579 160087230107449362618060869)
      ·
        refine ⟨30016355645146755490886413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160087230107449362618060869 30016355645146755490886413)
        ·
          refine ⟨11256133366930033309082405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30016355645146755490886413 11256133366930033309082405)
          ·
            refine ⟨2110525006299381245452951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11256133366930033309082405 2110525006299381245452951)
            ·
              refine ⟨3165787509449071868179427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110525006299381245452951 3165787509449071868179427)
              ·
                refine ⟨4748681264173607802269141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165787509449071868179427 4748681264173607802269141)
                ·
                  refine ⟨111297217129068932865683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4748681264173607802269141 111297217129068932865683)
                  ·
                    rfl

theorem cell23_1950755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 7].length) (baseStart_1950755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950755 prefixEnd_1950755 := by exact prefixLift 1950755
  have htrace : WordTrace (prefixWord ++ tailWord_1950755) baseStart_1950755 baseEnd_1950755 := by
    simpa [prefixWord, tailWord_1950755, baseEnd_1950755] using wordTrace_append hprefix tailTrace_1950755
  have hstable : (prefixWord ++ tailWord_1950755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950755).length < 2 ^ (prefixWord ++ tailWord_1950755).sum := by decide
  have hdescent : baseEnd_1950755 < baseStart_1950755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950768 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_1950768 : Nat := 118140960795 + 1950768 * 2 ^ 59
def prefixEnd_1950768 : Nat := 4983230072969 + 3 ^ 40 * 1950768 * 2
def baseEnd_1950768 : Nat := 333893876470042948309529

theorem tailTrace_1950768 : CollatzResearch.WordTrace tailWord_1950768 prefixEnd_1950768 333893876470042948309529 := by
  unfold tailWord_1950768
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575177098354087747458479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47433569464472116996611305 35575177098354087747458479)
  ·
    refine ⟨53362765647531131621187719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35575177098354087747458479 53362765647531131621187719)
    ·
      refine ⟨80044148471296697431781579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53362765647531131621187719 80044148471296697431781579)
      ·
        refine ⟨120066222706945046147672369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80044148471296697431781579 120066222706945046147672369)
        ·
          refine ⟨90049667030208784610754277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120066222706945046147672369 90049667030208784610754277)
          ·
            refine ⟨16884312568164147114516427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90049667030208784610754277 16884312568164147114516427)
            ·
              refine ⟨25326468852246220671774641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884312568164147114516427 25326468852246220671774641)
              ·
                refine ⟨18994851639184665503830981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25326468852246220671774641 18994851639184665503830981)
                ·
                  refine ⟨3561534682347124781968309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18994851639184665503830981 3561534682347124781968309)
                  ·
                    refine ⟨333893876470042948309529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3561534682347124781968309 333893876470042948309529)
                    ·
                      rfl

theorem cell23_1950768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_1950768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950768 prefixEnd_1950768 := by exact prefixLift 1950768
  have htrace : WordTrace (prefixWord ++ tailWord_1950768) baseStart_1950768 baseEnd_1950768 := by
    simpa [prefixWord, tailWord_1950768, baseEnd_1950768] using wordTrace_append hprefix tailTrace_1950768
  have hstable : (prefixWord ++ tailWord_1950768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950768).length < 2 ^ (prefixWord ++ tailWord_1950768).sum := by decide
  have hdescent : baseEnd_1950768 < baseStart_1950768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950805 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1950805 : Nat := 118140960795 + 1950805 * 2 ^ 59
def prefixEnd_1950805 : Nat := 4983230072969 + 3 ^ 40 * 1950805 * 2
def baseEnd_1950805 : Nat := 1001700628194345200165917

theorem tailTrace_1950805 : CollatzResearch.WordTrace tailWord_1950805 prefixEnd_1950805 1001700628194345200165917 := by
  unfold tailWord_1950805
  simp only [CollatzResearch.WordTrace]
  refine ⟨71151703697574130814013869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47434469131716087209342579 71151703697574130814013869)
  ·
    refine ⟨26681888886590299055255201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71151703697574130814013869 26681888886590299055255201)
    ·
      refine ⟨20011416664942724291441401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26681888886590299055255201 20011416664942724291441401)
      ·
        refine ⟨15008562498707043218581051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20011416664942724291441401 15008562498707043218581051)
        ·
          refine ⟨22512843748060564827871577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15008562498707043218581051 22512843748060564827871577)
          ·
            refine ⟨16884632811045423620903683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22512843748060564827871577 16884632811045423620903683)
            ·
              refine ⟨25326949216568135431355525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884632811045423620903683 25326949216568135431355525)
              ·
                refine ⟨4748802978106525393379161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25326949216568135431355525 4748802978106525393379161)
                ·
                  refine ⟨3561602233579894045034371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4748802978106525393379161 3561602233579894045034371)
                  ·
                    refine ⟨5342403350369841067551557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3561602233579894045034371 5342403350369841067551557)
                    ·
                      refine ⟨1001700628194345200165917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5342403350369841067551557 1001700628194345200165917)
                      ·
                        rfl

theorem cell23_1950805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1950805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950805 prefixEnd_1950805 := by exact prefixLift 1950805
  have htrace : WordTrace (prefixWord ++ tailWord_1950805) baseStart_1950805 baseEnd_1950805 := by
    simpa [prefixWord, tailWord_1950805, baseEnd_1950805] using wordTrace_append hprefix tailTrace_1950805
  have hstable : (prefixWord ++ tailWord_1950805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950805).length < 2 ^ (prefixWord ++ tailWord_1950805).sum := by decide
  have hdescent : baseEnd_1950805 < baseStart_1950805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950806 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1950806 : Nat := 118140960795 + 1950806 * 2 ^ 59
def prefixEnd_1950806 : Nat := 4983230072969 + 3 ^ 40 * 1950806 * 2
def baseEnd_1950806 : Nat := 111300126852777744028157

theorem tailTrace_1950806 : CollatzResearch.WordTrace tailWord_1950806 prefixEnd_1950806 111300126852777744028157 := by
  unfold tailWord_1950806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446983760660656749050017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47434493447047005323200181 4446983760660656749050017)
  ·
    refine ⟨3335237820495492561787513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446983760660656749050017 3335237820495492561787513)
    ·
      refine ⟨2501428365371619421340635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3335237820495492561787513 2501428365371619421340635)
      ·
        refine ⟨3752142548057429132010953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501428365371619421340635 3752142548057429132010953)
        ·
          refine ⟨2814106911043071849008215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3752142548057429132010953 2814106911043071849008215)
          ·
            refine ⟨4221160366564607773512323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814106911043071849008215 4221160366564607773512323)
            ·
              refine ⟨6331740549846911660268485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221160366564607773512323 6331740549846911660268485)
              ·
                refine ⟨1187201353096295936300341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6331740549846911660268485 1187201353096295936300341)
                ·
                  refine ⟨111300126852777744028157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1187201353096295936300341 111300126852777744028157)
                  ·
                    rfl

theorem cell23_1950806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1950806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950806 prefixEnd_1950806 := by exact prefixLift 1950806
  have htrace : WordTrace (prefixWord ++ tailWord_1950806) baseStart_1950806 baseEnd_1950806 := by
    simpa [prefixWord, tailWord_1950806, baseEnd_1950806] using wordTrace_append hprefix tailTrace_1950806
  have hstable : (prefixWord ++ tailWord_1950806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950806).length < 2 ^ (prefixWord ++ tailWord_1950806).sum := by decide
  have hdescent : baseEnd_1950806 < baseStart_1950806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950808 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1950808 : Nat := 118140960795 + 1950808 * 2 ^ 59
def prefixEnd_1950808 : Nat := 4983230072969 + 3 ^ 40 * 1950808 * 2
def baseEnd_1950808 : Nat := 1001702168636308688428403

theorem tailTrace_1950808 : CollatzResearch.WordTrace tailWord_1950808 prefixEnd_1950808 1001702168636308688428403 := by
  unfold tailWord_1950808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575906558281631163186539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47434542077708841550915385 35575906558281631163186539)
  ·
    refine ⟨53363859837422446744779809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35575906558281631163186539 53363859837422446744779809)
    ·
      refine ⟨40022894878066835058584857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53363859837422446744779809 40022894878066835058584857)
      ·
        refine ⟨30017171158550126293938643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40022894878066835058584857 30017171158550126293938643)
        ·
          refine ⟨45025756737825189440907965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017171158550126293938643 45025756737825189440907965)
          ·
            refine ⟨16884658776684446040340487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45025756737825189440907965 16884658776684446040340487)
            ·
              refine ⟨25326988165026669060510731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884658776684446040340487 25326988165026669060510731)
              ·
                refine ⟨37990482247540003590766097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25326988165026669060510731 37990482247540003590766097)
                ·
                  refine ⟨28492861685655002693074573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37990482247540003590766097 28492861685655002693074573)
                  ·
                    refine ⟨10684823132120626009902965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28492861685655002693074573 10684823132120626009902965)
                    ·
                      refine ⟨1001702168636308688428403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10684823132120626009902965 1001702168636308688428403)
                      ·
                        rfl

theorem cell23_1950808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1950808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950808 prefixEnd_1950808 := by exact prefixLift 1950808
  have htrace : WordTrace (prefixWord ++ tailWord_1950808) baseStart_1950808 baseEnd_1950808 := by
    simpa [prefixWord, tailWord_1950808, baseEnd_1950808] using wordTrace_append hprefix tailTrace_1950808
  have hstable : (prefixWord ++ tailWord_1950808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950808).length < 2 ^ (prefixWord ++ tailWord_1950808).sum := by decide
  have hdescent : baseEnd_1950808 < baseStart_1950808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950815 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 3, 4]
def baseStart_1950815 : Nat := 118140960795 + 1950815 * 2 ^ 59
def prefixEnd_1950815 : Nat := 4983230072969 + 3 ^ 40 * 1950815 * 2
def baseEnd_1950815 : Nat := 333901921000296720346957

theorem tailTrace_1950815 : CollatzResearch.WordTrace tailWord_1950815 prefixEnd_1950815 333901921000296720346957 := by
  unfold tailWord_1950815
  simp only [CollatzResearch.WordTrace]
  refine ⟨71152068427537902521877899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47434712285025268347918599 71152068427537902521877899)
  ·
    refine ⟨106728102641306853782816849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71152068427537902521877899 106728102641306853782816849)
    ·
      refine ⟨80046076980980140337112637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106728102641306853782816849 80046076980980140337112637)
      ·
        refine ⟨30017278867867552626417239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80046076980980140337112637 30017278867867552626417239)
        ·
          refine ⟨45025918301801328939625859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017278867867552626417239 45025918301801328939625859)
          ·
            refine ⟨67538877452701993409438789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45025918301801328939625859 67538877452701993409438789)
            ·
              refine ⟨12663539522381623764269773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67538877452701993409438789 12663539522381623764269773)
              ·
                refine ⟨4748827320893108911601165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12663539522381623764269773 4748827320893108911601165)
                ·
                  refine ⟨1780810245334915841850437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748827320893108911601165 1780810245334915841850437)
                  ·
                    refine ⟨333901921000296720346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780810245334915841850437 333901921000296720346957)
                    ·
                      rfl

theorem cell23_1950815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_1950815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950815 prefixEnd_1950815 := by exact prefixLift 1950815
  have htrace : WordTrace (prefixWord ++ tailWord_1950815) baseStart_1950815 baseEnd_1950815 := by
    simpa [prefixWord, tailWord_1950815, baseEnd_1950815] using wordTrace_append hprefix tailTrace_1950815
  have hstable : (prefixWord ++ tailWord_1950815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950815).length < 2 ^ (prefixWord ++ tailWord_1950815).sum := by decide
  have hdescent : baseEnd_1950815 < baseStart_1950815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950849 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1950849 : Nat := 118140960795 + 1950849 * 2 ^ 59
def prefixEnd_1950849 : Nat := 4983230072969 + 3 ^ 40 * 1950849 * 2
def baseEnd_1950849 : Nat := 333907740447714342671905

theorem tailTrace_1950849 : CollatzResearch.WordTrace tailWord_1950849 prefixEnd_1950849 333907740447714342671905 := by
  unfold tailWord_1950849
  simp only [CollatzResearch.WordTrace]
  refine ⟨71153308509414726328615601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47435539006276484219077067 71153308509414726328615601)
  ·
    refine ⟨53364981382061044746461701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71153308509414726328615601 53364981382061044746461701)
    ·
      refine ⟨10005934009136445889961569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53364981382061044746461701 10005934009136445889961569)
      ·
        refine ⟨7504450506852334417471177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10005934009136445889961569 7504450506852334417471177)
        ·
          refine ⟨5628337880139250813103383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504450506852334417471177 5628337880139250813103383)
          ·
            refine ⟨8442506820208876219655075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628337880139250813103383 8442506820208876219655075)
            ·
              refine ⟨12663760230313314329482613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442506820208876219655075 12663760230313314329482613)
              ·
                refine ⟨1187227521591873218388995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12663760230313314329482613 1187227521591873218388995)
                ·
                  refine ⟨1780841282387809827583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187227521591873218388995 1780841282387809827583493)
                  ·
                    refine ⟨333907740447714342671905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780841282387809827583493 333907740447714342671905)
                    ·
                      rfl

theorem cell23_1950849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1950849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950849 prefixEnd_1950849 := by exact prefixLift 1950849
  have htrace : WordTrace (prefixWord ++ tailWord_1950849) baseStart_1950849 baseEnd_1950849 := by
    simpa [prefixWord, tailWord_1950849, baseEnd_1950849] using wordTrace_append hprefix tailTrace_1950849
  have hstable : (prefixWord ++ tailWord_1950849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950849).length < 2 ^ (prefixWord ++ tailWord_1950849).sum := by decide
  have hdescent : baseEnd_1950849 < baseStart_1950849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950862 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_1950862 : Nat := 118140960795 + 1950862 * 2 ^ 59
def prefixEnd_1950862 : Nat := 4983230072969 + 3 ^ 40 * 1950862 * 2
def baseEnd_1950862 : Nat := 111303321843516830794795

theorem tailTrace_1950862 : CollatzResearch.WordTrace tailWord_1950862 prefixEnd_1950862 111303321843516830794795 := by
  unfold tailWord_1950862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894222832295953693604855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47435855105578419699225893 8894222832295953693604855)
  ·
    refine ⟨13341334248443930540407283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894222832295953693604855 13341334248443930540407283)
    ·
      refine ⟨20012001372665895810610925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13341334248443930540407283 20012001372665895810610925)
      ·
        refine ⟨7504500514749710928979097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20012001372665895810610925 7504500514749710928979097)
        ·
          refine ⟨5628375386062283196734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504500514749710928979097 5628375386062283196734323)
          ·
            refine ⟨8442563079093424795101485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628375386062283196734323 8442563079093424795101485)
            ·
              refine ⟨3165961154660034298163057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8442563079093424795101485 3165961154660034298163057)
              ·
                refine ⟨2374470865995025723622293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165961154660034298163057 2374470865995025723622293)
                ·
                  refine ⟨111303321843516830794795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2374470865995025723622293 111303321843516830794795)
                  ·
                    rfl

theorem cell23_1950862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_1950862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950862 prefixEnd_1950862 := by exact prefixLift 1950862
  have htrace : WordTrace (prefixWord ++ tailWord_1950862) baseStart_1950862 baseEnd_1950862 := by
    simpa [prefixWord, tailWord_1950862, baseEnd_1950862] using wordTrace_append hprefix tailTrace_1950862
  have hstable : (prefixWord ++ tailWord_1950862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950862).length < 2 ^ (prefixWord ++ tailWord_1950862).sum := by decide
  have hdescent : baseEnd_1950862 < baseStart_1950862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
