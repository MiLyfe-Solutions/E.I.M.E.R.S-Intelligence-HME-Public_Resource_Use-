import V185TrunkScan23Chunk1390

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8238732 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_8238732 : Nat := 118140960795 + 8238732 * 2 ^ 59
def prefixEnd_8238732 : Nat := 4983230072969 + 3 ^ 40 * 8238732 * 2
def baseEnd_8238732 : Nat := 4230429499577965156860767

theorem tailTrace_8238732 : CollatzResearch.WordTrace tailWord_8238732 prefixEnd_8238732 4230429499577965156860767 := by
  unfold tailWord_8238732
  simp only [CollatzResearch.WordTrace]
  refine ⟨150245621194244251124335225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200327494925659001499113633 150245621194244251124335225)
  ·
    refine ⟨112684215895683188343251419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150245621194244251124335225 112684215895683188343251419)
    ·
      refine ⟨169026323843524782514877129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112684215895683188343251419 169026323843524782514877129)
      ·
        refine ⟨126769742882643586886157847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169026323843524782514877129 126769742882643586886157847)
        ·
          refine ⟨190154614323965380329236771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126769742882643586886157847 190154614323965380329236771)
          ·
            refine ⟨285231921485948070493855157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190154614323965380329236771 285231921485948070493855157)
            ·
              refine ⟨26740492639307631608798921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285231921485948070493855157 26740492639307631608798921)
              ·
                refine ⟨20055369479480723706599191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26740492639307631608798921 20055369479480723706599191)
                ·
                  refine ⟨30083054219221085559898787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20055369479480723706599191 30083054219221085559898787)
                  ·
                    refine ⟨45124581328831628339848181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30083054219221085559898787 45124581328831628339848181)
                    ·
                      refine ⟨4230429499577965156860767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45124581328831628339848181 4230429499577965156860767)
                      ·
                        rfl

theorem cell23_8238732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_8238732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238732 prefixEnd_8238732 := by exact prefixLift 8238732
  have htrace : WordTrace (prefixWord ++ tailWord_8238732) baseStart_8238732 baseEnd_8238732 := by
    simpa [prefixWord, tailWord_8238732, baseEnd_8238732] using wordTrace_append hprefix tailTrace_8238732
  have hstable : (prefixWord ++ tailWord_8238732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238732).length < 2 ^ (prefixWord ++ tailWord_8238732).sum := by decide
  have hdescent : baseEnd_8238732 < baseStart_8238732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238752 : List Nat := [2, 1, 1, 4, 3, 2, 1, 9]
def baseStart_8238752 : Nat := 118140960795 + 8238752 * 2 ^ 59
def prefixEnd_8238752 : Nat := 4983230072969 + 3 ^ 40 * 8238752 * 2
def baseEnd_8238752 : Nat := 156682954414483521430025

theorem tailTrace_8238752 : CollatzResearch.WordTrace tailWord_8238752 prefixEnd_8238752 156682954414483521430025 := by
  unfold tailWord_8238752
  simp only [CollatzResearch.WordTrace]
  refine ⟨150245985924208022832199255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200327981232277363776265673 150245985924208022832199255)
  ·
    refine ⟨225368978886312034248298883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150245985924208022832199255 225368978886312034248298883)
    ·
      refine ⟨338053468329468051372448325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225368978886312034248298883 338053468329468051372448325)
      ·
        refine ⟨63385025311775259632334061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338053468329468051372448325 63385025311775259632334061)
        ·
          refine ⟨23769384491915722362125273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63385025311775259632334061 23769384491915722362125273)
          ·
            refine ⟨17827038368936791771593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23769384491915722362125273 17827038368936791771593955)
            ·
              refine ⟨26740557553405187657390933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17827038368936791771593955 26740557553405187657390933)
              ·
                refine ⟨156682954414483521430025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26740557553405187657390933 156682954414483521430025)
                ·
                  rfl

theorem cell23_8238752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_8238752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238752 prefixEnd_8238752 := by exact prefixLift 8238752
  have htrace : WordTrace (prefixWord ++ tailWord_8238752) baseStart_8238752 baseEnd_8238752 := by
    simpa [prefixWord, tailWord_8238752, baseEnd_8238752] using wordTrace_append hprefix tailTrace_8238752
  have hstable : (prefixWord ++ tailWord_8238752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238752).length < 2 ^ (prefixWord ++ tailWord_8238752).sum := by decide
  have hdescent : baseEnd_8238752 < baseStart_8238752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_8238789 : Nat := 118140960795 + 8238789 * 2 ^ 59
def prefixEnd_8238789 : Nat := 4983230072969 + 3 ^ 40 * 8238789 * 2
def baseEnd_8238789 : Nat := 4230458767975271433848005

theorem tailTrace_8238789 : CollatzResearch.WordTrace tailWord_8238789 prefixEnd_8238789 4230458767975271433848005 := by
  unfold tailWord_8238789
  simp only [CollatzResearch.WordTrace]
  refine ⟨300493321349282000983495421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200328880899521333988996947 300493321349282000983495421)
  ·
    refine ⟨112684995505980750368810783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300493321349282000983495421 112684995505980750368810783)
    ·
      refine ⟨169027493258971125553216175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112684995505980750368810783 169027493258971125553216175)
      ·
        refine ⟨253541239888456688329824263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169027493258971125553216175 253541239888456688329824263)
        ·
          refine ⟨380311859832685032494736395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253541239888456688329824263 380311859832685032494736395)
          ·
            refine ⟨570467789749027548742104593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380311859832685032494736395 570467789749027548742104593)
            ·
              refine ⟨427850842311770661556578445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570467789749027548742104593 427850842311770661556578445)
              ·
                refine ⟨160444065866913998083716917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427850842311770661556578445 160444065866913998083716917)
                ·
                  refine ⟨15041631175023187320348461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160444065866913998083716917 15041631175023187320348461)
                  ·
                    refine ⟨5640611690633695245130673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15041631175023187320348461 5640611690633695245130673)
                    ·
                      refine ⟨4230458767975271433848005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640611690633695245130673 4230458767975271433848005)
                      ·
                        rfl

theorem cell23_8238789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_8238789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238789 prefixEnd_8238789 := by exact prefixLift 8238789
  have htrace : WordTrace (prefixWord ++ tailWord_8238789) baseStart_8238789 baseEnd_8238789 := by
    simpa [prefixWord, tailWord_8238789, baseEnd_8238789] using wordTrace_append hprefix tailTrace_8238789
  have hstable : (prefixWord ++ tailWord_8238789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238789).length < 2 ^ (prefixWord ++ tailWord_8238789).sum := by decide
  have hdescent : baseEnd_8238789 < baseStart_8238789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238790 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_8238790 : Nat := 118140960795 + 8238790 * 2 ^ 59
def prefixEnd_8238790 : Nat := 4983230072969 + 3 ^ 40 * 8238790 * 2
def baseEnd_8238790 : Nat := 1410153093818641976645167

theorem tailTrace_8238790 : CollatzResearch.WordTrace tailWord_8238790 prefixEnd_8238790 1410153093818641976645167 := by
  unfold tailWord_8238790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390417431946199317321307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200328905214852252102854549 9390417431946199317321307)
  ·
    refine ⟨14085626147919298975981961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9390417431946199317321307 14085626147919298975981961)
    ·
      refine ⟨10564219610939474231986471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14085626147919298975981961 10564219610939474231986471)
      ·
        refine ⟨15846329416409211347979707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10564219610939474231986471 15846329416409211347979707)
        ·
          refine ⟨23769494124613817021969561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15846329416409211347979707 23769494124613817021969561)
          ·
            refine ⟨17827120593460362766477171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23769494124613817021969561 17827120593460362766477171)
            ·
              refine ⟨26740680890190544149715757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17827120593460362766477171 26740680890190544149715757)
              ·
                refine ⟨10027755333821454056143409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26740680890190544149715757 10027755333821454056143409)
                ·
                  refine ⟨7520816500366090542107557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10027755333821454056143409 7520816500366090542107557)
                  ·
                    refine ⟨1410153093818641976645167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520816500366090542107557 1410153093818641976645167)
                    ·
                      rfl

theorem cell23_8238790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_8238790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238790 prefixEnd_8238790 := by exact prefixLift 8238790
  have htrace : WordTrace (prefixWord ++ tailWord_8238790) baseStart_8238790 baseEnd_8238790 := by
    simpa [prefixWord, tailWord_8238790, baseEnd_8238790] using wordTrace_append hprefix tailTrace_8238790
  have hstable : (prefixWord ++ tailWord_8238790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238790).length < 2 ^ (prefixWord ++ tailWord_8238790).sum := by decide
  have hdescent : baseEnd_8238790 < baseStart_8238790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238813 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_8238813 : Nat := 118140960795 + 8238813 * 2 ^ 59
def prefixEnd_8238813 : Nat := 4983230072969 + 3 ^ 40 * 8238813 * 2
def baseEnd_8238813 : Nat := 4230471091510979339947895

theorem tailTrace_8238813 : CollatzResearch.WordTrace tailWord_8238813 prefixEnd_8238813 4230471091510979339947895 := by
  unfold tailWord_8238813
  simp only [CollatzResearch.WordTrace]
  refine ⟨300494196701195053082369093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200329464467463368721579395 300494196701195053082369093)
  ·
    refine ⟨56342661881474072452944205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300494196701195053082369093 56342661881474072452944205)
    ·
      refine ⟨21128498205552777169854077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56342661881474072452944205 21128498205552777169854077)
      ·
        refine ⟨7923186827082291438695279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21128498205552777169854077 7923186827082291438695279)
        ·
          refine ⟨11884780240623437158042919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7923186827082291438695279 11884780240623437158042919)
          ·
            refine ⟨17827170360935155737064379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884780240623437158042919 17827170360935155737064379)
            ·
              refine ⟨26740755541402733605596569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17827170360935155737064379 26740755541402733605596569)
              ·
                refine ⟨20055566656052050204197427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26740755541402733605596569 20055566656052050204197427)
                ·
                  refine ⟨30083349984078075306296141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20055566656052050204197427 30083349984078075306296141)
                  ·
                    refine ⟨11281256244029278239861053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30083349984078075306296141 11281256244029278239861053)
                    ·
                      refine ⟨4230471091510979339947895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11281256244029278239861053 4230471091510979339947895)
                      ·
                        rfl

theorem cell23_8238813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_8238813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238813 prefixEnd_8238813 := by exact prefixLift 8238813
  have htrace : WordTrace (prefixWord ++ tailWord_8238813) baseStart_8238813 baseEnd_8238813 := by
    simpa [prefixWord, tailWord_8238813, baseEnd_8238813] using wordTrace_append hprefix tailTrace_8238813
  have hstable : (prefixWord ++ tailWord_8238813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238813).length < 2 ^ (prefixWord ++ tailWord_8238813).sum := by decide
  have hdescent : baseEnd_8238813 < baseStart_8238813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238842 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_8238842 : Nat := 118140960795 + 8238842 * 2 ^ 59
def prefixEnd_8238842 : Nat := 4983230072969 + 3 ^ 40 * 8238842 * 2
def baseEnd_8238842 : Nat := 470053998049995525165029

theorem tailTrace_8238842 : CollatzResearch.WordTrace tailWord_8238842 prefixEnd_8238842 470053998049995525165029 := by
  unfold tailWord_8238842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75123813604522497758793695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200330169612059994023449853 75123813604522497758793695)
  ·
    refine ⟨112685720406783746638190543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75123813604522497758793695 112685720406783746638190543)
    ·
      refine ⟨169028580610175619957285815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112685720406783746638190543 169028580610175619957285815)
      ·
        refine ⟨253542870915263429935928723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169028580610175619957285815 253542870915263429935928723)
        ·
          refine ⟨380314306372895144903893085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253542870915263429935928723 380314306372895144903893085)
          ·
            refine ⟨142617864889835679338959907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380314306372895144903893085 142617864889835679338959907)
            ·
              refine ⟨213926797334753519008439861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142617864889835679338959907 213926797334753519008439861)
              ·
                refine ⟨20055637250133142407041237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213926797334753519008439861 20055637250133142407041237)
                ·
                  refine ⟨470053998049995525165029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20055637250133142407041237 470053998049995525165029)
                  ·
                    rfl

theorem cell23_8238842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_8238842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238842 prefixEnd_8238842 := by exact prefixLift 8238842
  have htrace : WordTrace (prefixWord ++ tailWord_8238842) baseStart_8238842 baseEnd_8238842 := by
    simpa [prefixWord, tailWord_8238842, baseEnd_8238842] using wordTrace_append hprefix tailTrace_8238842
  have hstable : (prefixWord ++ tailWord_8238842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238842).length < 2 ^ (prefixWord ++ tailWord_8238842).sum := by decide
  have hdescent : baseEnd_8238842 < baseStart_8238842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238846 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_8238846 : Nat := 118140960795 + 8238846 * 2 ^ 59
def prefixEnd_8238846 : Nat := 4983230072969 + 3 ^ 40 * 8238846 * 2
def baseEnd_8238846 : Nat := 1410162678790859236945081

theorem tailTrace_8238846 : CollatzResearch.WordTrace tailWord_8238846 prefixEnd_8238846 1410162678790859236945081 := by
  unfold tailWord_8238846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37561925038759437464790049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200330266873383666478880261 37561925038759437464790049)
  ·
    refine ⟨28171443779069578098592537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37561925038759437464790049 28171443779069578098592537)
    ·
      refine ⟨21128582834302183573944403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28171443779069578098592537 21128582834302183573944403)
      ·
        refine ⟨31692874251453275360916605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21128582834302183573944403 31692874251453275360916605)
        ·
          refine ⟨11884827844294978260343727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31692874251453275360916605 11884827844294978260343727)
          ·
            refine ⟨17827241766442467390515591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884827844294978260343727 17827241766442467390515591)
            ·
              refine ⟨26740862649663701085773387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17827241766442467390515591 26740862649663701085773387)
              ·
                refine ⟨40111293974495551628660081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26740862649663701085773387 40111293974495551628660081)
                ·
                  refine ⟨30083470480871663721495061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40111293974495551628660081 30083470480871663721495061)
                  ·
                    refine ⟨1410162678790859236945081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30083470480871663721495061 1410162678790859236945081)
                    ·
                      rfl

theorem cell23_8238846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_8238846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238846 prefixEnd_8238846 := by exact prefixLift 8238846
  have htrace : WordTrace (prefixWord ++ tailWord_8238846) baseStart_8238846 baseEnd_8238846 := by
    simpa [prefixWord, tailWord_8238846, baseEnd_8238846] using wordTrace_append hprefix tailTrace_8238846
  have hstable : (prefixWord ++ tailWord_8238846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238846).length < 2 ^ (prefixWord ++ tailWord_8238846).sum := by decide
  have hdescent : baseEnd_8238846 < baseStart_8238846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238876 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 5]
def baseStart_8238876 : Nat := 118140960795 + 8238876 * 2 ^ 59
def prefixEnd_8238876 : Nat := 4983230072969 + 3 ^ 40 * 8238876 * 2
def baseEnd_8238876 : Nat := 470055937865801399273345

theorem tailTrace_8238876 : CollatzResearch.WordTrace tailWord_8238876 prefixEnd_8238876 470055937865801399273345 := by
  unfold tailWord_8238876
  simp only [CollatzResearch.WordTrace]
  refine ⟨150248247249983407420956241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200330996333311209894608321 150248247249983407420956241)
  ·
    refine ⟨112686185437487555565717181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150248247249983407420956241 112686185437487555565717181)
    ·
      refine ⟨42257319539057833337143943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112686185437487555565717181 42257319539057833337143943)
      ·
        refine ⟨63385979308586750005715915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42257319539057833337143943 63385979308586750005715915)
        ·
          refine ⟨95078968962880125008573873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63385979308586750005715915 95078968962880125008573873)
          ·
            refine ⟨71309226722160093756430405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95078968962880125008573873 71309226722160093756430405)
            ·
              refine ⟨13370480010405017579330701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71309226722160093756430405 13370480010405017579330701)
              ·
                refine ⟨5013930003901881592249013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13370480010405017579330701 5013930003901881592249013)
                ·
                  refine ⟨470055937865801399273345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013930003901881592249013 470055937865801399273345)
                  ·
                    rfl

theorem cell23_8238876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_8238876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238876 prefixEnd_8238876 := by exact prefixLift 8238876
  have htrace : WordTrace (prefixWord ++ tailWord_8238876) baseStart_8238876 baseEnd_8238876 := by
    simpa [prefixWord, tailWord_8238876, baseEnd_8238876] using wordTrace_append hprefix tailTrace_8238876
  have hstable : (prefixWord ++ tailWord_8238876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238876).length < 2 ^ (prefixWord ++ tailWord_8238876).sum := by decide
  have hdescent : baseEnd_8238876 < baseStart_8238876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238949 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 6]
def baseStart_8238949 : Nat := 118140960795 + 8238949 * 2 ^ 59
def prefixEnd_8238949 : Nat := 4983230072969 + 3 ^ 40 * 8238949 * 2
def baseEnd_8238949 : Nat := 470060102764443423094141

theorem tailTrace_8238949 : CollatzResearch.WordTrace tailWord_8238949 prefixEnd_8238949 470060102764443423094141 := by
  unfold tailWord_8238949
  simp only [CollatzResearch.WordTrace]
  refine ⟨300499157028702348309319901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200332771352468232206213267 300499157028702348309319901)
  ·
    refine ⟨112687183885763380615994963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300499157028702348309319901 112687183885763380615994963)
    ·
      refine ⟨169030775828645070923992445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112687183885763380615994963 169030775828645070923992445)
      ·
        refine ⟨63386540935741901596497167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169030775828645070923992445 63386540935741901596497167)
        ·
          refine ⟨95079811403612852394745751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63386540935741901596497167 95079811403612852394745751)
          ·
            refine ⟨142619717105419278592118627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95079811403612852394745751 142619717105419278592118627)
            ·
              refine ⟨213929575658128917888177941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142619717105419278592118627 213929575658128917888177941)
              ·
                refine ⟨10027948858974793026008341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213929575658128917888177941 10027948858974793026008341)
                ·
                  refine ⟨470060102764443423094141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10027948858974793026008341 470060102764443423094141)
                  ·
                    rfl

theorem cell23_8238949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_8238949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238949 prefixEnd_8238949 := by exact prefixLift 8238949
  have htrace : WordTrace (prefixWord ++ tailWord_8238949) baseStart_8238949 baseEnd_8238949 := by
    simpa [prefixWord, tailWord_8238949, baseEnd_8238949] using wordTrace_append hprefix tailTrace_8238949
  have hstable : (prefixWord ++ tailWord_8238949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238949).length < 2 ^ (prefixWord ++ tailWord_8238949).sum := by decide
  have hdescent : baseEnd_8238949 < baseStart_8238949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238976 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_8238976 : Nat := 118140960795 + 8238976 * 2 ^ 59
def prefixEnd_8238976 : Nat := 4983230072969 + 3 ^ 40 * 8238976 * 2
def baseEnd_8238976 : Nat := 4230554788857662202209645

theorem tailTrace_8238976 : CollatzResearch.WordTrace tailWord_8238976 prefixEnd_8238976 4230554788857662202209645 := by
  unfold tailWord_8238976
  simp only [CollatzResearch.WordTrace]
  refine ⟨150250070899802265960276391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200333427866403021280368521 150250070899802265960276391)
  ·
    refine ⟨225375106349703398940414587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150250070899802265960276391 225375106349703398940414587)
    ·
      refine ⟨338062659524555098410621881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225375106349703398940414587 338062659524555098410621881)
      ·
        refine ⟨253546994643416323807966411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338062659524555098410621881 253546994643416323807966411)
        ·
          refine ⟨380320491965124485711949617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253546994643416323807966411 380320491965124485711949617)
          ·
            refine ⟨285240368973843364283962213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380320491965124485711949617 285240368973843364283962213)
            ·
              refine ⟨53482569182595630803242915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285240368973843364283962213 53482569182595630803242915)
              ·
                refine ⟨80223853773893446204864373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53482569182595630803242915 80223853773893446204864373)
                ·
                  refine ⟨7520986291302510581706035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80223853773893446204864373 7520986291302510581706035)
                  ·
                    refine ⟨11281479436953765872559053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7520986291302510581706035 11281479436953765872559053)
                    ·
                      refine ⟨4230554788857662202209645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11281479436953765872559053 4230554788857662202209645)
                      ·
                        rfl

theorem cell23_8238976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_8238976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238976 prefixEnd_8238976 := by exact prefixLift 8238976
  have htrace : WordTrace (prefixWord ++ tailWord_8238976) baseStart_8238976 baseEnd_8238976 := by
    simpa [prefixWord, tailWord_8238976, baseEnd_8238976] using wordTrace_append hprefix tailTrace_8238976
  have hstable : (prefixWord ++ tailWord_8238976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238976).length < 2 ^ (prefixWord ++ tailWord_8238976).sum := by decide
  have hdescent : baseEnd_8238976 < baseStart_8238976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239019 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3]
def baseStart_8239019 : Nat := 118140960795 + 8239019 * 2 ^ 59
def prefixEnd_8239019 : Nat := 4983230072969 + 3 ^ 40 * 8239019 * 2
def baseEnd_8239019 : Nat := 4230576868525805533971947

theorem tailTrace_8239019 : CollatzResearch.WordTrace tailWord_8239019 prefixEnd_8239019 4230576868525805533971947 := by
  unfold tailWord_8239019
  simp only [CollatzResearch.WordTrace]
  refine ⟨300501710138448750264368111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200334473425632500176245407 300501710138448750264368111)
  ·
    refine ⟨450752565207673125396552167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300501710138448750264368111 450752565207673125396552167)
    ·
      refine ⟨676128847811509688094828251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450752565207673125396552167 676128847811509688094828251)
      ·
        refine ⟨1014193271717264532142242377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676128847811509688094828251 1014193271717264532142242377)
        ·
          refine ⟨760644953787948399106681783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014193271717264532142242377 760644953787948399106681783)
          ·
            refine ⟨1140967430681922598660022675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760644953787948399106681783 1140967430681922598660022675)
            ·
              refine ⟨1711451146022883897990034013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140967430681922598660022675 1711451146022883897990034013)
              ·
                refine ⟨641794179758581461746262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711451146022883897990034013 641794179758581461746262755)
                ·
                  refine ⟨962691269637872192619394133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641794179758581461746262755 962691269637872192619394133)
                  ·
                    refine ⟨11281538316068814757258525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 962691269637872192619394133 11281538316068814757258525)
                    ·
                      refine ⟨4230576868525805533971947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11281538316068814757258525 4230576868525805533971947)
                      ·
                        rfl

theorem cell23_8239019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].length) (baseStart_8239019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239019 prefixEnd_8239019 := by exact prefixLift 8239019
  have htrace : WordTrace (prefixWord ++ tailWord_8239019) baseStart_8239019 baseEnd_8239019 := by
    simpa [prefixWord, tailWord_8239019, baseEnd_8239019] using wordTrace_append hprefix tailTrace_8239019
  have hstable : (prefixWord ++ tailWord_8239019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239019).length < 2 ^ (prefixWord ++ tailWord_8239019).sum := by decide
  have hdescent : baseEnd_8239019 < baseStart_8239019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239083 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 3]
def baseStart_8239083 : Nat := 118140960795 + 8239083 * 2 ^ 59
def prefixEnd_8239083 : Nat := 4983230072969 + 3 ^ 40 * 8239083 * 2
def baseEnd_8239083 : Nat := 4230609731287693283571653

theorem tailTrace_8239083 : CollatzResearch.WordTrace tailWord_8239083 prefixEnd_8239083 4230609731287693283571653 := by
  unfold tailWord_8239083
  simp only [CollatzResearch.WordTrace]
  refine ⟨300504044410216889194697903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200336029606811259463131935 300504044410216889194697903)
  ·
    refine ⟨450756066615325333792046855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300504044410216889194697903 450756066615325333792046855)
    ·
      refine ⟨676134099922988000688070283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450756066615325333792046855 676134099922988000688070283)
      ·
        refine ⟨1014201149884482001032105425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676134099922988000688070283 1014201149884482001032105425)
        ·
          refine ⟨760650862413361500774079069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014201149884482001032105425 760650862413361500774079069)
          ·
            refine ⟨285244073405010562790279651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760650862413361500774079069 285244073405010562790279651)
            ·
              refine ⟨427866110107515844185419477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285244073405010562790279651 427866110107515844185419477)
              ·
                refine ⟨10028111955644902598095769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427866110107515844185419477 10028111955644902598095769)
                ·
                  refine ⟨7521083966733676948571827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10028111955644902598095769 7521083966733676948571827)
                  ·
                    refine ⟨11281625950100515422857741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521083966733676948571827 11281625950100515422857741)
                    ·
                      refine ⟨4230609731287693283571653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11281625950100515422857741 4230609731287693283571653)
                      ·
                        rfl

theorem cell23_8239083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 3].length) (baseStart_8239083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239083 prefixEnd_8239083 := by exact prefixLift 8239083
  have htrace : WordTrace (prefixWord ++ tailWord_8239083) baseStart_8239083 baseEnd_8239083 := by
    simpa [prefixWord, tailWord_8239083, baseEnd_8239083] using wordTrace_append hprefix tailTrace_8239083
  have hstable : (prefixWord ++ tailWord_8239083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239083).length < 2 ^ (prefixWord ++ tailWord_8239083).sum := by decide
  have hdescent : baseEnd_8239083 < baseStart_8239083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239099 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 8]
def baseStart_8239099 : Nat := 118140960795 + 8239099 * 2 ^ 59
def prefixEnd_8239099 : Nat := 4983230072969 + 3 ^ 40 * 8239099 * 2
def baseEnd_8239099 : Nat := 1410205982326055073657193

theorem tailTrace_8239099 : CollatzResearch.WordTrace tailWord_8239099 prefixEnd_8239099 1410205982326055073657193 := by
  unfold tailWord_8239099
  simp only [CollatzResearch.WordTrace]
  refine ⟨300504627978158923927280351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200336418652105949284853567 300504627978158923927280351)
  ·
    refine ⟨450756941967238385890920527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300504627978158923927280351 450756941967238385890920527)
    ·
      refine ⟨676135412950857578836380791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450756941967238385890920527 676135412950857578836380791)
      ·
        refine ⟨1014203119426286368254571187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676135412950857578836380791 1014203119426286368254571187)
        ·
          refine ⟨1521304679139429552381856781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014203119426286368254571187 1521304679139429552381856781)
          ·
            refine ⟨570489254677286082143196293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1521304679139429552381856781 570489254677286082143196293)
            ·
              refine ⟨106966735251991140401849305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570489254677286082143196293 106966735251991140401849305)
              ·
                refine ⟨80225051438993355301386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106966735251991140401849305 80225051438993355301386979)
                ·
                  refine ⟨120337577158490032952080469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80225051438993355301386979 120337577158490032952080469)
                  ·
                    refine ⟨1410205982326055073657193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120337577158490032952080469 1410205982326055073657193)
                    ·
                      rfl

theorem cell23_8239099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_8239099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239099 prefixEnd_8239099 := by exact prefixLift 8239099
  have htrace : WordTrace (prefixWord ++ tailWord_8239099) baseStart_8239099 baseEnd_8239099 := by
    simpa [prefixWord, tailWord_8239099, baseEnd_8239099] using wordTrace_append hprefix tailTrace_8239099
  have hstable : (prefixWord ++ tailWord_8239099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239099).length < 2 ^ (prefixWord ++ tailWord_8239099).sum := by decide
  have hdescent : baseEnd_8239099 < baseStart_8239099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239176 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_8239176 : Nat := 118140960795 + 8239176 * 2 ^ 59
def prefixEnd_8239176 : Nat := 4983230072969 + 3 ^ 40 * 8239176 * 2
def baseEnd_8239176 : Nat := 1410219161662853806569575

theorem tailTrace_8239176 : CollatzResearch.WordTrace tailWord_8239176 prefixEnd_8239176 1410219161662853806569575 := by
  unfold tailWord_8239176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150253718199439983038916691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200338290932586644051888921 150253718199439983038916691)
  ·
    refine ⟨225380577299159974558375037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150253718199439983038916691 225380577299159974558375037)
    ·
      refine ⟨84517716487184990459390639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225380577299159974558375037 84517716487184990459390639)
      ·
        refine ⟨126776574730777485689085959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84517716487184990459390639 126776574730777485689085959)
        ·
          refine ⟨190164862096166228533628939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126776574730777485689085959 190164862096166228533628939)
          ·
            refine ⟨285247293144249342800443409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190164862096166228533628939 285247293144249342800443409)
            ·
              refine ⟨213935469858187007100332557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285247293144249342800443409 213935469858187007100332557)
              ·
                refine ⟨80225801196820127662624709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213935469858187007100332557 80225801196820127662624709)
                ·
                  refine ⟨15042337724403773936742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80225801196820127662624709 15042337724403773936742133)
                  ·
                    refine ⟨1410219161662853806569575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15042337724403773936742133 1410219161662853806569575)
                    ·
                      rfl

theorem cell23_8239176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_8239176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239176 prefixEnd_8239176 := by exact prefixLift 8239176
  have htrace : WordTrace (prefixWord ++ tailWord_8239176) baseStart_8239176 baseEnd_8239176 := by
    simpa [prefixWord, tailWord_8239176, baseEnd_8239176] using wordTrace_append hprefix tailTrace_8239176
  have hstable : (prefixWord ++ tailWord_8239176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239176).length < 2 ^ (prefixWord ++ tailWord_8239176).sum := by decide
  have hdescent : baseEnd_8239176 < baseStart_8239176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239180 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 5]
def baseStart_8239180 : Nat := 118140960795 + 8239180 * 2 ^ 59
def prefixEnd_8239180 : Nat := 4983230072969 + 3 ^ 40 * 8239180 * 2
def baseEnd_8239180 : Nat := 470073282101242156006523

theorem tailTrace_8239180 : CollatzResearch.WordTrace tailWord_8239180 prefixEnd_8239180 470073282101242156006523 := by
  unfold tailWord_8239180
  simp only [CollatzResearch.WordTrace]
  refine ⟨150253791145432737380489497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200338388193910316507319329 150253791145432737380489497)
  ·
    refine ⟨112690343359074553035367123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150253791145432737380489497 112690343359074553035367123)
    ·
      refine ⟨169035515038611829553050685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112690343359074553035367123 169035515038611829553050685)
      ·
        refine ⟨63388318139479436082394007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169035515038611829553050685 63388318139479436082394007)
        ·
          refine ⟨95082477209219154123591011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63388318139479436082394007 95082477209219154123591011)
          ·
            refine ⟨142623715813828731185386517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95082477209219154123591011 142623715813828731185386517)
            ·
              refine ⟨6685486678773221774314993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142623715813828731185386517 6685486678773221774314993)
              ·
                refine ⟨5014115009079916330736245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685486678773221774314993 5014115009079916330736245)
                ·
                  refine ⟨470073282101242156006523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014115009079916330736245 470073282101242156006523)
                  ·
                    rfl

theorem cell23_8239180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_8239180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239180 prefixEnd_8239180 := by exact prefixLift 8239180
  have htrace : WordTrace (prefixWord ++ tailWord_8239180) baseStart_8239180 baseEnd_8239180 := by
    simpa [prefixWord, tailWord_8239180, baseEnd_8239180] using wordTrace_append hprefix tailTrace_8239180
  have hstable : (prefixWord ++ tailWord_8239180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239180).length < 2 ^ (prefixWord ++ tailWord_8239180).sum := by decide
  have hdescent : baseEnd_8239180 < baseStart_8239180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239213 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_8239213 : Nat := 118140960795 + 8239213 * 2 ^ 59
def prefixEnd_8239213 : Nat := 4983230072969 + 3 ^ 40 * 8239213 * 2
def baseEnd_8239213 : Nat := 4230676483772777774946055

theorem tailTrace_8239213 : CollatzResearch.WordTrace tailWord_8239213 prefixEnd_8239213 4230676483772777774946055 := by
  unfold tailWord_8239213
  simp only [CollatzResearch.WordTrace]
  refine ⟨300508785899745921396930293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200339190599830614264620195 300508785899745921396930293)
  ·
    refine ⟨28172698678101180130962215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300508785899745921396930293 28172698678101180130962215)
    ·
      refine ⟨42259048017151770196443323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28172698678101180130962215 42259048017151770196443323)
      ·
        refine ⟨63388572025727655294664985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42259048017151770196443323 63388572025727655294664985)
        ·
          refine ⟨47541429019295741470998739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63388572025727655294664985 47541429019295741470998739)
          ·
            refine ⟨71312143528943612206498109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47541429019295741470998739 71312143528943612206498109)
            ·
              refine ⟨26742053823353854577436791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71312143528943612206498109 26742053823353854577436791)
              ·
                refine ⟨40113080735030781866155187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26742053823353854577436791 40113080735030781866155187)
                ·
                  refine ⟨60169621102546172799232781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40113080735030781866155187 60169621102546172799232781)
                  ·
                    refine ⟨22563607913454814799712293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60169621102546172799232781 22563607913454814799712293)
                    ·
                      refine ⟨4230676483772777774946055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22563607913454814799712293 4230676483772777774946055)
                      ·
                        rfl

theorem cell23_8239213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_8239213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239213 prefixEnd_8239213 := by exact prefixLift 8239213
  have htrace : WordTrace (prefixWord ++ tailWord_8239213) baseStart_8239213 baseEnd_8239213 := by
    simpa [prefixWord, tailWord_8239213, baseEnd_8239213] using wordTrace_append hprefix tailTrace_8239213
  have hstable : (prefixWord ++ tailWord_8239213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239213).length < 2 ^ (prefixWord ++ tailWord_8239213).sum := by decide
  have hdescent : baseEnd_8239213 < baseStart_8239213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239226 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_8239226 : Nat := 118140960795 + 8239226 * 2 ^ 59
def prefixEnd_8239226 : Nat := 4983230072969 + 3 ^ 40 * 8239226 * 2
def baseEnd_8239226 : Nat := 4230683159021286224083495

theorem tailTrace_8239226 : CollatzResearch.WordTrace tailWord_8239226 prefixEnd_8239226 4230683159021286224083495 := by
  unfold tailWord_8239226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75127315012174706154288383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200339506699132549744769021 75127315012174706154288383)
  ·
    refine ⟨112690972518262059231432575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75127315012174706154288383 112690972518262059231432575)
    ·
      refine ⟨169036458777393088847148863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112690972518262059231432575 169036458777393088847148863)
      ·
        refine ⟨253554688166089633270723295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169036458777393088847148863 253554688166089633270723295)
        ·
          refine ⟨380332032249134449906084943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253554688166089633270723295 380332032249134449906084943)
          ·
            refine ⟨570498048373701674859127415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380332032249134449906084943 570498048373701674859127415)
            ·
              refine ⟨855747072560552512288691123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570498048373701674859127415 855747072560552512288691123)
              ·
                refine ⟨1283620608840828768433036685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855747072560552512288691123 1283620608840828768433036685)
                ·
                  refine ⟨481357728315310788162388757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1283620608840828768433036685 481357728315310788162388757)
                  ·
                    refine ⟨22563643514780193195111973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 481357728315310788162388757 22563643514780193195111973)
                    ·
                      refine ⟨4230683159021286224083495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22563643514780193195111973 4230683159021286224083495)
                      ·
                        rfl

theorem cell23_8239226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_8239226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239226 prefixEnd_8239226 := by exact prefixLift 8239226
  have htrace : WordTrace (prefixWord ++ tailWord_8239226) baseStart_8239226 baseEnd_8239226 := by
    simpa [prefixWord, tailWord_8239226, baseEnd_8239226] using wordTrace_append hprefix tailTrace_8239226
  have hstable : (prefixWord ++ tailWord_8239226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239226).length < 2 ^ (prefixWord ++ tailWord_8239226).sum := by decide
  have hdescent : baseEnd_8239226 < baseStart_8239226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239240 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_8239240 : Nat := 118140960795 + 8239240 * 2 ^ 59
def prefixEnd_8239240 : Nat := 4983230072969 + 3 ^ 40 * 8239240 * 2
def baseEnd_8239240 : Nat := 1410230115916816389769477

theorem tailTrace_8239240 : CollatzResearch.WordTrace tailWord_8239240 prefixEnd_8239240 1410230115916816389769477 := by
  unfold tailWord_8239240
  simp only [CollatzResearch.WordTrace]
  refine ⟨150254885335324052504081587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200339847113765403338775449 150254885335324052504081587)
  ·
    refine ⟨225382328002986078756122381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150254885335324052504081587 225382328002986078756122381)
    ·
      refine ⟨84518373001119779533545893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225382328002986078756122381 84518373001119779533545893)
      ·
        refine ⟨15847194937709958662539855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84518373001119779533545893 15847194937709958662539855)
        ·
          refine ⟨23770792406564937993809783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15847194937709958662539855 23770792406564937993809783)
          ·
            refine ⟨35656188609847406990714675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23770792406564937993809783 35656188609847406990714675)
            ·
              refine ⟨53484282914771110486072013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35656188609847406990714675 53484282914771110486072013)
              ·
                refine ⟨20056606093039166432277005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53484282914771110486072013 20056606093039166432277005)
                ·
                  refine ⟨7521227284889687412103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20056606093039166432277005 7521227284889687412103877)
                  ·
                    refine ⟨1410230115916816389769477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521227284889687412103877 1410230115916816389769477)
                    ·
                      rfl

theorem cell23_8239240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_8239240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239240 prefixEnd_8239240 := by exact prefixLift 8239240
  have htrace : WordTrace (prefixWord ++ tailWord_8239240) baseStart_8239240 baseEnd_8239240 := by
    simpa [prefixWord, tailWord_8239240, baseEnd_8239240] using wordTrace_append hprefix tailTrace_8239240
  have hstable : (prefixWord ++ tailWord_8239240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239240).length < 2 ^ (prefixWord ++ tailWord_8239240).sum := by decide
  have hdescent : baseEnd_8239240 < baseStart_8239240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239276 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_8239276 : Nat := 118140960795 + 8239276 * 2 ^ 59
def prefixEnd_8239276 : Nat := 4983230072969 + 3 ^ 40 * 8239276 * 2
def baseEnd_8239276 : Nat := 4230708833054011028458265

theorem tailTrace_8239276 : CollatzResearch.WordTrace tailWord_8239276 prefixEnd_8239276 4230708833054011028458265 := by
  unfold tailWord_8239276
  simp only [CollatzResearch.WordTrace]
  refine ⟨150255541849258841578236841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200340722465678455437649121 150255541849258841578236841)
  ·
    refine ⟨112691656386944131183677631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150255541849258841578236841 112691656386944131183677631)
    ·
      refine ⟨169037484580416196775516447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112691656386944131183677631 169037484580416196775516447)
      ·
        refine ⟨253556226870624295163274671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169037484580416196775516447 253556226870624295163274671)
        ·
          refine ⟨380334340305936442744912007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253556226870624295163274671 380334340305936442744912007)
          ·
            refine ⟨570501510458904664117368011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380334340305936442744912007 570501510458904664117368011)
            ·
              refine ⟨855752265688356996176052017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570501510458904664117368011 855752265688356996176052017)
              ·
                refine ⟨641814199266267747132039013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855752265688356996176052017 641814199266267747132039013)
                ·
                  refine ⟨120340162362425202587257315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641814199266267747132039013 120340162362425202587257315)
                  ·
                    refine ⟨180510243543637803880885973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120340162362425202587257315 180510243543637803880885973)
                    ·
                      refine ⟨4230708833054011028458265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180510243543637803880885973 4230708833054011028458265)
                      ·
                        rfl

theorem cell23_8239276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_8239276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239276 prefixEnd_8239276 := by exact prefixLift 8239276
  have htrace : WordTrace (prefixWord ++ tailWord_8239276) baseStart_8239276 baseEnd_8239276 := by
    simpa [prefixWord, tailWord_8239276, baseEnd_8239276] using wordTrace_append hprefix tailTrace_8239276
  have hstable : (prefixWord ++ tailWord_8239276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239276).length < 2 ^ (prefixWord ++ tailWord_8239276).sum := by decide
  have hdescent : baseEnd_8239276 < baseStart_8239276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239290 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_8239290 : Nat := 118140960795 + 8239290 * 2 ^ 59
def prefixEnd_8239290 : Nat := 4983230072969 + 3 ^ 40 * 8239290 * 2
def baseEnd_8239290 : Nat := 4230716021783173973683201

theorem tailTrace_8239290 : CollatzResearch.WordTrace tailWord_8239290 prefixEnd_8239290 4230716021783173973683201 := by
  unfold tailWord_8239290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75127898580116740886870831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200341062880311309031655549 75127898580116740886870831)
  ·
    refine ⟨112691847870175111330306247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75127898580116740886870831 112691847870175111330306247)
    ·
      refine ⟨169037771805262666995459371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112691847870175111330306247 169037771805262666995459371)
      ·
        refine ⟨253556657707894000493189057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169037771805262666995459371 253556657707894000493189057)
        ·
          refine ⟨190167493280920500369891793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253556657707894000493189057 190167493280920500369891793)
          ·
            refine ⟨142625619960690375277418845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190167493280920500369891793 142625619960690375277418845)
            ·
              refine ⟨53484607485258890729032067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142625619960690375277418845 53484607485258890729032067)
              ·
                refine ⟨80226911227888336093548101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53484607485258890729032067 80226911227888336093548101)
                ·
                  refine ⟨15042545855229063017540269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80226911227888336093548101 15042545855229063017540269)
                  ·
                    refine ⟨5640954695710898631577601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15042545855229063017540269 5640954695710898631577601)
                    ·
                      refine ⟨4230716021783173973683201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640954695710898631577601 4230716021783173973683201)
                      ·
                        rfl

theorem cell23_8239290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_8239290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239290 prefixEnd_8239290 := by exact prefixLift 8239290
  have htrace : WordTrace (prefixWord ++ tailWord_8239290) baseStart_8239290 baseEnd_8239290 := by
    simpa [prefixWord, tailWord_8239290, baseEnd_8239290] using wordTrace_append hprefix tailTrace_8239290
  have hstable : (prefixWord ++ tailWord_8239290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239290).length < 2 ^ (prefixWord ++ tailWord_8239290).sum := by decide
  have hdescent : baseEnd_8239290 < baseStart_8239290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239320 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_8239320 : Nat := 118140960795 + 8239320 * 2 ^ 59
def prefixEnd_8239320 : Nat := 4983230072969 + 3 ^ 40 * 8239320 * 2
def baseEnd_8239320 : Nat := 4230731426202808856308063

theorem tailTrace_8239320 : CollatzResearch.WordTrace tailWord_8239320 prefixEnd_8239320 4230731426202808856308063 := by
  unfold tailWord_8239320
  simp only [CollatzResearch.WordTrace]
  refine ⟨150256344255179139335537707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200341792340238852447383609 150256344255179139335537707)
  ·
    refine ⟨225384516382768709003306561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150256344255179139335537707 225384516382768709003306561)
    ·
      refine ⟨169038387287076531752479921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225384516382768709003306561 169038387287076531752479921)
      ·
        refine ⟨126778790465307398814359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169038387287076531752479921 126778790465307398814359941)
        ·
          refine ⟨23771023212245137277692489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126778790465307398814359941 23771023212245137277692489)
          ·
            refine ⟨17828267409183852958269367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23771023212245137277692489 17828267409183852958269367)
            ·
              refine ⟨26742401113775779437404051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17828267409183852958269367 26742401113775779437404051)
              ·
                refine ⟨40113601670663669156106077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26742401113775779437404051 40113601670663669156106077)
                ·
                  refine ⟨15042600626498875933539779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40113601670663669156106077 15042600626498875933539779)
                  ·
                    refine ⟨22563900939748313900309669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15042600626498875933539779 22563900939748313900309669)
                    ·
                      refine ⟨4230731426202808856308063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22563900939748313900309669 4230731426202808856308063)
                      ·
                        rfl

theorem cell23_8239320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_8239320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239320 prefixEnd_8239320 := by exact prefixLift 8239320
  have htrace : WordTrace (prefixWord ++ tailWord_8239320) baseStart_8239320 baseEnd_8239320 := by
    simpa [prefixWord, tailWord_8239320, baseEnd_8239320] using wordTrace_append hprefix tailTrace_8239320
  have hstable : (prefixWord ++ tailWord_8239320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239320).length < 2 ^ (prefixWord ++ tailWord_8239320).sum := by decide
  have hdescent : baseEnd_8239320 < baseStart_8239320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239370 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_8239370 : Nat := 118140960795 + 8239370 * 2 ^ 59
def prefixEnd_8239370 : Nat := 4983230072969 + 3 ^ 40 * 8239370 * 2
def baseEnd_8239370 : Nat := 4230757100235533660682833

theorem tailTrace_8239370 : CollatzResearch.WordTrace tailWord_8239370 prefixEnd_8239370 4230757100235533660682833 := by
  unfold tailWord_8239370
  simp only [CollatzResearch.WordTrace]
  refine ⟨75128628040044284302598891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200343008106784758140263709 75128628040044284302598891)
  ·
    refine ⟨112692942060066426453898337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75128628040044284302598891 112692942060066426453898337)
    ·
      refine ⟨84519706545049819840423753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112692942060066426453898337 84519706545049819840423753)
      ·
        refine ⟨63389779908787364880317815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84519706545049819840423753 63389779908787364880317815)
        ·
          refine ⟨95084669863181047320476723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63389779908787364880317815 95084669863181047320476723)
          ·
            refine ⟨142627004794771570980715085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95084669863181047320476723 142627004794771570980715085)
            ·
              refine ⟨53485126798039339117768157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142627004794771570980715085 53485126798039339117768157)
              ·
                refine ⟨20056922549264752169163059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53485126798039339117768157 20056922549264752169163059)
                ·
                  refine ⟨30085383823897128253744589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20056922549264752169163059 30085383823897128253744589)
                  ·
                    refine ⟨11282018933961423095154221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30085383823897128253744589 11282018933961423095154221)
                    ·
                      refine ⟨4230757100235533660682833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282018933961423095154221 4230757100235533660682833)
                      ·
                        rfl

theorem cell23_8239370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_8239370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239370 prefixEnd_8239370 := by exact prefixLift 8239370
  have htrace : WordTrace (prefixWord ++ tailWord_8239370) baseStart_8239370 baseEnd_8239370 := by
    simpa [prefixWord, tailWord_8239370, baseEnd_8239370] using wordTrace_append hprefix tailTrace_8239370
  have hstable : (prefixWord ++ tailWord_8239370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239370).length < 2 ^ (prefixWord ++ tailWord_8239370).sum := by decide
  have hdescent : baseEnd_8239370 < baseStart_8239370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239427 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 4, 2]
def baseStart_8239427 : Nat := 118140960795 + 8239427 * 2 ^ 59
def prefixEnd_8239427 : Nat := 4983230072969 + 3 ^ 40 * 8239427 * 2
def baseEnd_8239427 : Nat := 4230786368632839937670071

theorem tailTrace_8239427 : CollatzResearch.WordTrace tailWord_8239427 prefixEnd_8239427 4230786368632839937670071 := by
  unfold tailWord_8239427
  simp only [CollatzResearch.WordTrace]
  refine ⟨300516591120970635945220535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200344394080647090630147023 300516591120970635945220535)
  ·
    refine ⟨450774886681455953917830803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300516591120970635945220535 450774886681455953917830803)
    ·
      refine ⟨676162330022183930876746205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450774886681455953917830803 676162330022183930876746205)
      ·
        refine ⟨253560873758318974078779827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676162330022183930876746205 253560873758318974078779827)
        ·
          refine ⟨380341310637478461118169741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253560873758318974078779827 380341310637478461118169741)
          ·
            refine ⟨142627991489054422919313653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380341310637478461118169741 142627991489054422919313653)
            ·
              refine ⟨13371374202098852148685655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142627991489054422919313653 13371374202098852148685655)
              ·
                refine ⟨20057061303148278223028483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371374202098852148685655 20057061303148278223028483)
                ·
                  refine ⟨30085591954722417334542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20057061303148278223028483 30085591954722417334542725)
                  ·
                    refine ⟨5641048491510453250226761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30085591954722417334542725 5641048491510453250226761)
                    ·
                      refine ⟨4230786368632839937670071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641048491510453250226761 4230786368632839937670071)
                      ·
                        rfl

theorem cell23_8239427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_8239427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239427 prefixEnd_8239427 := by exact prefixLift 8239427
  have htrace : WordTrace (prefixWord ++ tailWord_8239427) baseStart_8239427 baseEnd_8239427 := by
    simpa [prefixWord, tailWord_8239427, baseEnd_8239427] using wordTrace_append hprefix tailTrace_8239427
  have hstable : (prefixWord ++ tailWord_8239427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239427).length < 2 ^ (prefixWord ++ tailWord_8239427).sum := by decide
  have hdescent : baseEnd_8239427 < baseStart_8239427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239444 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_8239444 : Nat := 118140960795 + 8239444 * 2 ^ 59
def prefixEnd_8239444 : Nat := 4983230072969 + 3 ^ 40 * 8239444 * 2
def baseEnd_8239444 : Nat := 4230795097803966371157493

theorem tailTrace_8239444 : CollatzResearch.WordTrace tailWord_8239444 prefixEnd_8239444 4230795097803966371157493 := by
  unfold tailWord_8239444
  simp only [CollatzResearch.WordTrace]
  refine ⟨150258605580954523924294693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200344807441272698565726257 150258605580954523924294693)
  ·
    refine ⟨28173488546428973235805255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150258605580954523924294693 28173488546428973235805255)
    ·
      refine ⟨42260232819643459853707883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28173488546428973235805255 42260232819643459853707883)
      ·
        refine ⟨63390349229465189780561825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42260232819643459853707883 63390349229465189780561825)
        ·
          refine ⟨47542761922098892335421369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63390349229465189780561825 47542761922098892335421369)
          ·
            refine ⟨35657071441574169251566027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47542761922098892335421369 35657071441574169251566027)
            ·
              refine ⟨53485607162361253877349041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35657071441574169251566027 53485607162361253877349041)
              ·
                refine ⟨40114205371770940408011781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53485607162361253877349041 40114205371770940408011781)
                ·
                  refine ⟨7521413507207051326502209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40114205371770940408011781 7521413507207051326502209)
                  ·
                    refine ⟨5641060130405288494876657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521413507207051326502209 5641060130405288494876657)
                    ·
                      refine ⟨4230795097803966371157493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641060130405288494876657 4230795097803966371157493)
                      ·
                        rfl

theorem cell23_8239444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_8239444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239444 prefixEnd_8239444 := by exact prefixLift 8239444
  have htrace : WordTrace (prefixWord ++ tailWord_8239444) baseStart_8239444 baseEnd_8239444 := by
    simpa [prefixWord, tailWord_8239444, baseEnd_8239444] using wordTrace_append hprefix tailTrace_8239444
  have hstable : (prefixWord ++ tailWord_8239444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239444).length < 2 ^ (prefixWord ++ tailWord_8239444).sum := by decide
  have hdescent : baseEnd_8239444 < baseStart_8239444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239497 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_8239497 : Nat := 118140960795 + 8239497 * 2 ^ 59
def prefixEnd_8239497 : Nat := 4983230072969 + 3 ^ 40 * 8239497 * 2
def baseEnd_8239497 : Nat := 1410274104092884887931583

theorem tailTrace_8239497 : CollatzResearch.WordTrace tailWord_8239497 prefixEnd_8239497 1410274104092884887931583 := by
  unfold tailWord_8239497
  simp only [CollatzResearch.WordTrace]
  refine ⟨300519144230717037900268745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200346096153811358600179163 300519144230717037900268745)
  ·
    refine ⟨225389358173037778425201559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300519144230717037900268745 225389358173037778425201559)
    ·
      refine ⟨338084037259556667637802339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225389358173037778425201559 338084037259556667637802339)
      ·
        refine ⟨507126055889335001456703509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338084037259556667637802339 507126055889335001456703509)
        ·
          refine ⟨23771533869812578193282977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 507126055889335001456703509 23771533869812578193282977)
          ·
            refine ⟨17828650402359433644962233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23771533869812578193282977 17828650402359433644962233)
            ·
              refine ⟨13371487801769575233721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17828650402359433644962233 13371487801769575233721675)
              ·
                refine ⟨20057231702654362850582513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371487801769575233721675 20057231702654362850582513)
                ·
                  refine ⟨15042923776990772137936885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20057231702654362850582513 15042923776990772137936885)
                  ·
                    refine ⟨1410274104092884887931583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15042923776990772137936885 1410274104092884887931583)
                    ·
                      rfl

theorem cell23_8239497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_8239497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239497 prefixEnd_8239497 := by exact prefixLift 8239497
  have htrace : WordTrace (prefixWord ++ tailWord_8239497) baseStart_8239497 baseEnd_8239497 := by
    simpa [prefixWord, tailWord_8239497, baseEnd_8239497] using wordTrace_append hprefix tailTrace_8239497
  have hstable : (prefixWord ++ tailWord_8239497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239497).length < 2 ^ (prefixWord ++ tailWord_8239497).sum := by decide
  have hdescent : baseEnd_8239497 < baseStart_8239497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239518 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_8239518 : Nat := 118140960795 + 8239518 * 2 ^ 59
def prefixEnd_8239518 : Nat := 4983230072969 + 3 ^ 40 * 8239518 * 2
def baseEnd_8239518 : Nat := 470092566152488786848017

theorem tailTrace_8239518 : CollatzResearch.WordTrace tailWord_8239518 prefixEnd_8239518 470092566152488786848017 := by
  unfold tailWord_8239518
  simp only [CollatzResearch.WordTrace]
  refine ⟨37564988770455119810847901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200346606775760638991188805 37564988770455119810847901)
  ·
    refine ⟨14086870788920669929067963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37564988770455119810847901 14086870788920669929067963)
    ·
      refine ⟨21130306183381004893601945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14086870788920669929067963 21130306183381004893601945)
      ·
        refine ⟨15847729637535753670201459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21130306183381004893601945 15847729637535753670201459)
        ·
          refine ⟨23771594456303630505302189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15847729637535753670201459 23771594456303630505302189)
          ·
            refine ⟨8914347921113861439488321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23771594456303630505302189 8914347921113861439488321)
            ·
              refine ⟨6685760940835396079616241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8914347921113861439488321 6685760940835396079616241)
              ·
                refine ⟨5014320705626547059712181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685760940835396079616241 5014320705626547059712181)
                ·
                  refine ⟨470092566152488786848017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014320705626547059712181 470092566152488786848017)
                  ·
                    rfl

theorem cell23_8239518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_8239518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239518 prefixEnd_8239518 := by exact prefixLift 8239518
  have htrace : WordTrace (prefixWord ++ tailWord_8239518) baseStart_8239518 baseEnd_8239518 := by
    simpa [prefixWord, tailWord_8239518, baseEnd_8239518] using wordTrace_append hprefix tailTrace_8239518
  have hstable : (prefixWord ++ tailWord_8239518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239518).length < 2 ^ (prefixWord ++ tailWord_8239518).sum := by decide
  have hdescent : baseEnd_8239518 < baseStart_8239518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239567 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_8239567 : Nat := 118140960795 + 8239567 * 2 ^ 59
def prefixEnd_8239567 : Nat := 4983230072969 + 3 ^ 40 * 8239567 * 2
def baseEnd_8239567 : Nat := 4230858255924469389919427

theorem tailTrace_8239567 : CollatzResearch.WordTrace tailWord_8239567 prefixEnd_8239567 4230858255924469389919427 := by
  unfold tailWord_8239567
  simp only [CollatzResearch.WordTrace]
  refine ⟨300521697340463439855316955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200347798226975626570211303 300521697340463439855316955)
  ·
    refine ⟨450782546010695159782975433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300521697340463439855316955 450782546010695159782975433)
    ·
      refine ⟨338086909508021369837231575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450782546010695159782975433 338086909508021369837231575)
      ·
        refine ⟨507130364262032054755847363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338086909508021369837231575 507130364262032054755847363)
        ·
          refine ⟨760695546393048082133771045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507130364262032054755847363 760695546393048082133771045)
          ·
            refine ⟨142630414948696515400082071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 760695546393048082133771045 142630414948696515400082071)
            ·
              refine ⟨213945622423044773100123107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142630414948696515400082071 213945622423044773100123107)
              ·
                refine ⟨320918433634567159650184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213945622423044773100123107 320918433634567159650184661)
                ·
                  refine ⟨7521525788310167804301203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320918433634567159650184661 7521525788310167804301203)
                  ·
                    refine ⟨11282288682465251706451805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521525788310167804301203 11282288682465251706451805)
                    ·
                      refine ⟨4230858255924469389919427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282288682465251706451805 4230858255924469389919427)
                      ·
                        rfl

theorem cell23_8239567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_8239567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239567 prefixEnd_8239567 := by exact prefixLift 8239567
  have htrace : WordTrace (prefixWord ++ tailWord_8239567) baseStart_8239567 baseEnd_8239567 := by
    simpa [prefixWord, tailWord_8239567, baseEnd_8239567] using wordTrace_append hprefix tailTrace_8239567
  have hstable : (prefixWord ++ tailWord_8239567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239567).length < 2 ^ (prefixWord ++ tailWord_8239567).sum := by decide
  have hdescent : baseEnd_8239567 < baseStart_8239567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239584 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_8239584 : Nat := 118140960795 + 8239584 * 2 ^ 59
def prefixEnd_8239584 : Nat := 4983230072969 + 3 ^ 40 * 8239584 * 2
def baseEnd_8239584 : Nat := 4230866985095595823406849

theorem tailTrace_8239584 : CollatzResearch.WordTrace tailWord_8239584 prefixEnd_8239584 4230866985095595823406849 := by
  unfold tailWord_8239584
  simp only [CollatzResearch.WordTrace]
  refine ⟨150261158690700925879342903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200348211587601234505790537 150261158690700925879342903)
  ·
    refine ⟨225391738036051388819014355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150261158690700925879342903 225391738036051388819014355)
    ·
      refine ⟨338087607054077083228521533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225391738036051388819014355 338087607054077083228521533)
      ·
        refine ⟨126782852645278906210695575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338087607054077083228521533 126782852645278906210695575)
        ·
          refine ⟨190174278967918359316043363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126782852645278906210695575 190174278967918359316043363)
          ·
            refine ⟨285261418451877538974065045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190174278967918359316043363 285261418451877538974065045)
            ·
              refine ⟨13371628989931759639409299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 285261418451877538974065045 13371628989931759639409299)
              ·
                refine ⟨20057443484897639459113949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371628989931759639409299 20057443484897639459113949)
                ·
                  refine ⟨7521541306836614797167731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20057443484897639459113949 7521541306836614797167731)
                  ·
                    refine ⟨11282311960254922195751597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521541306836614797167731 11282311960254922195751597)
                    ·
                      refine ⟨4230866985095595823406849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282311960254922195751597 4230866985095595823406849)
                      ·
                        rfl

theorem cell23_8239584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_8239584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239584 prefixEnd_8239584 := by exact prefixLift 8239584
  have htrace : WordTrace (prefixWord ++ tailWord_8239584) baseStart_8239584 baseEnd_8239584 := by
    simpa [prefixWord, tailWord_8239584, baseEnd_8239584] using wordTrace_append hprefix tailTrace_8239584
  have hstable : (prefixWord ++ tailWord_8239584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239584).length < 2 ^ (prefixWord ++ tailWord_8239584).sum := by decide
  have hdescent : baseEnd_8239584 < baseStart_8239584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239594 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_8239594 : Nat := 118140960795 + 8239594 * 2 ^ 59
def prefixEnd_8239594 : Nat := 4983230072969 + 3 ^ 40 * 8239594 * 2
def baseEnd_8239594 : Nat := 4230872119902140784281803

theorem tailTrace_8239594 : CollatzResearch.WordTrace tailWord_8239594 prefixEnd_8239594 4230872119902140784281803 := by
  unfold tailWord_8239594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75130670527841405866637459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200348454740910415644366557 75130670527841405866637459)
  ·
    refine ⟨112696005791762108799956189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75130670527841405866637459 112696005791762108799956189)
    ·
      refine ⟨42261002171910790799983571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112696005791762108799956189 42261002171910790799983571)
      ·
        refine ⟨63391503257866186199975357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42261002171910790799983571 63391503257866186199975357)
        ·
          refine ⟨23771813721699819824990759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63391503257866186199975357 23771813721699819824990759)
          ·
            refine ⟨35657720582549729737486139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23771813721699819824990759 35657720582549729737486139)
            ·
              refine ⟨53486580873824594606229209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35657720582549729737486139 53486580873824594606229209)
              ·
                refine ⟨40114935655368445954671907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53486580873824594606229209 40114935655368445954671907)
                ·
                  refine ⟨60172403483052668932007861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40114935655368445954671907 60172403483052668932007861)
                  ·
                    refine ⟨5641162826536187712375737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60172403483052668932007861 5641162826536187712375737)
                    ·
                      refine ⟨4230872119902140784281803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641162826536187712375737 4230872119902140784281803)
                      ·
                        rfl

theorem cell23_8239594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_8239594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239594 prefixEnd_8239594 := by exact prefixLift 8239594
  have htrace : WordTrace (prefixWord ++ tailWord_8239594) baseStart_8239594 baseEnd_8239594 := by
    simpa [prefixWord, tailWord_8239594, baseEnd_8239594] using wordTrace_append hprefix tailTrace_8239594
  have hstable : (prefixWord ++ tailWord_8239594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239594).length < 2 ^ (prefixWord ++ tailWord_8239594).sum := by decide
  have hdescent : baseEnd_8239594 < baseStart_8239594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239627 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_8239627 : Nat := 118140960795 + 8239627 * 2 ^ 59
def prefixEnd_8239627 : Nat := 4983230072969 + 3 ^ 40 * 8239627 * 2
def baseEnd_8239627 : Nat := 4230889064763739155169151

theorem tailTrace_8239627 : CollatzResearch.WordTrace tailWord_8239627 prefixEnd_8239627 4230889064763739155169151 := by
  unfold tailWord_8239627
  simp only [CollatzResearch.WordTrace]
  refine ⟨300523885720246070102501135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200349257146830713401667423 300523885720246070102501135)
  ·
    refine ⟨450785828580369105153751703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300523885720246070102501135 450785828580369105153751703)
    ·
      refine ⟨676178742870553657730627555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450785828580369105153751703 676178742870553657730627555)
      ·
        refine ⟨1014268114305830486595941333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676178742870553657730627555 1014268114305830486595941333)
        ·
          refine ⟨23771908929042902029592375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1014268114305830486595941333 23771908929042902029592375)
          ·
            refine ⟨35657863393564353044388563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23771908929042902029592375 35657863393564353044388563)
            ·
              refine ⟨53486795090346529566582845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35657863393564353044388563 53486795090346529566582845)
              ·
                refine ⟨20057548158879948587468567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53486795090346529566582845 20057548158879948587468567)
                ·
                  refine ⟨30086322238319922881202851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20057548158879948587468567 30086322238319922881202851)
                  ·
                    refine ⟨45129483357479884321804277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30086322238319922881202851 45129483357479884321804277)
                    ·
                      refine ⟨4230889064763739155169151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45129483357479884321804277 4230889064763739155169151)
                      ·
                        rfl

theorem cell23_8239627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_8239627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239627 prefixEnd_8239627 := by exact prefixLift 8239627
  have htrace : WordTrace (prefixWord ++ tailWord_8239627) baseStart_8239627 baseEnd_8239627 := by
    simpa [prefixWord, tailWord_8239627, baseEnd_8239627] using wordTrace_append hprefix tailTrace_8239627
  have hstable : (prefixWord ++ tailWord_8239627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239627).length < 2 ^ (prefixWord ++ tailWord_8239627).sum := by decide
  have hdescent : baseEnd_8239627 < baseStart_8239627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239651 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 2, 4]
def baseStart_8239651 : Nat := 118140960795 + 8239651 * 2 ^ 59
def prefixEnd_8239651 : Nat := 4983230072969 + 3 ^ 40 * 8239651 * 2
def baseEnd_8239651 : Nat := 1410300462766482353756347

theorem tailTrace_8239651 : CollatzResearch.WordTrace tailWord_8239651 prefixEnd_8239651 1410300462766482353756347 := by
  unfold tailWord_8239651
  simp only [CollatzResearch.WordTrace]
  refine ⟨300524761072159122201374807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200349840714772748134249871 300524761072159122201374807)
  ·
    refine ⟨450787141608238683302062211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300524761072159122201374807 450787141608238683302062211)
    ·
      refine ⟨676180712412358024953093317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450787141608238683302062211 676180712412358024953093317)
      ·
        refine ⟨126783883577317129678704997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 676180712412358024953093317 126783883577317129678704997)
        ·
          refine ⟨23771978170746961814757187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126783883577317129678704997 23771978170746961814757187)
          ·
            refine ⟨35657967256120442722135781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23771978170746961814757187 35657967256120442722135781)
            ·
              refine ⟨6685868860522583010400459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35657967256120442722135781 6685868860522583010400459)
              ·
                refine ⟨10028803290783874515600689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685868860522583010400459 10028803290783874515600689)
                ·
                  refine ⟨7521602468087905886700517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10028803290783874515600689 7521602468087905886700517)
                  ·
                    refine ⟨1410300462766482353756347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521602468087905886700517 1410300462766482353756347)
                    ·
                      rfl

theorem cell23_8239651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 4].length) (baseStart_8239651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239651 prefixEnd_8239651 := by exact prefixLift 8239651
  have htrace : WordTrace (prefixWord ++ tailWord_8239651) baseStart_8239651 baseEnd_8239651 := by
    simpa [prefixWord, tailWord_8239651, baseEnd_8239651] using wordTrace_append hprefix tailTrace_8239651
  have hstable : (prefixWord ++ tailWord_8239651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239651).length < 2 ^ (prefixWord ++ tailWord_8239651).sum := by decide
  have hdescent : baseEnd_8239651 < baseStart_8239651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239655 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 1, 5]
def baseStart_8239655 : Nat := 118140960795 + 8239655 * 2 ^ 59
def prefixEnd_8239655 : Nat := 4983230072969 + 3 ^ 40 * 8239655 * 2
def baseEnd_8239655 : Nat := 1410301147407355015206341

theorem tailTrace_8239655 : CollatzResearch.WordTrace tailWord_8239655 prefixEnd_8239655 1410301147407355015206341 := by
  unfold tailWord_8239655
  simp only [CollatzResearch.WordTrace]
  refine ⟨300524906964144630884520419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200349937976096420589680279 300524906964144630884520419)
  ·
    refine ⟨450787360446216946326780629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300524906964144630884520419 450787360446216946326780629)
    ·
      refine ⟨10565328760458209679533921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 450787360446216946326780629 10565328760458209679533921)
      ·
        refine ⟨7923996570343657259650441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10565328760458209679533921 7923996570343657259650441)
        ·
          refine ⟨5942997427757742944737831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7923996570343657259650441 5942997427757742944737831)
          ·
            refine ⟨8914496141636614417106747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942997427757742944737831 8914496141636614417106747)
            ·
              refine ⟨13371744212454921625660121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914496141636614417106747 13371744212454921625660121)
              ·
                refine ⟨10028808159341191219245091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13371744212454921625660121 10028808159341191219245091)
                ·
                  refine ⟨15043212239011786828867637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10028808159341191219245091 15043212239011786828867637)
                  ·
                    refine ⟨1410301147407355015206341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15043212239011786828867637 1410301147407355015206341)
                    ·
                      rfl

theorem cell23_8239655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_8239655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239655 prefixEnd_8239655 := by exact prefixLift 8239655
  have htrace : WordTrace (prefixWord ++ tailWord_8239655) baseStart_8239655 baseEnd_8239655 := by
    simpa [prefixWord, tailWord_8239655, baseEnd_8239655] using wordTrace_append hprefix tailTrace_8239655
  have hstable : (prefixWord ++ tailWord_8239655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239655).length < 2 ^ (prefixWord ++ tailWord_8239655).sum := by decide
  have hdescent : baseEnd_8239655 < baseStart_8239655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239674 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_8239674 : Nat := 118140960795 + 8239674 * 2 ^ 59
def prefixEnd_8239674 : Nat := 4983230072969 + 3 ^ 40 * 8239674 * 2
def baseEnd_8239674 : Nat := 4230913198354500471281435

theorem tailTrace_8239674 : CollatzResearch.WordTrace tailWord_8239674 prefixEnd_8239674 4230913198354500471281435 := by
  unfold tailWord_8239674
  simp only [CollatzResearch.WordTrace]
  refine ⟨75131399987768949282365519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200350399967383864752974717 75131399987768949282365519)
  ·
    refine ⟨112697099981653423923548279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75131399987768949282365519 112697099981653423923548279)
    ·
      refine ⟨169045649972480135885322419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112697099981653423923548279 169045649972480135885322419)
      ·
        refine ⟨253568474958720203827983629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169045649972480135885322419 253568474958720203827983629)
        ·
          refine ⟨95088178109520076435493861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253568474958720203827983629 95088178109520076435493861)
          ·
            refine ⟨17829033395535014331655099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95088178109520076435493861 17829033395535014331655099)
            ·
              refine ⟨26743550093302521497482649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829033395535014331655099 26743550093302521497482649)
              ·
                refine ⟨20057662569976891123111987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26743550093302521497482649 20057662569976891123111987)
                ·
                  refine ⟨30086493854965336684667981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20057662569976891123111987 30086493854965336684667981)
                  ·
                    refine ⟨11282435195612001256750493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30086493854965336684667981 11282435195612001256750493)
                    ·
                      refine ⟨4230913198354500471281435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282435195612001256750493 4230913198354500471281435)
                      ·
                        rfl

theorem cell23_8239674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_8239674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239674 prefixEnd_8239674 := by exact prefixLift 8239674
  have htrace : WordTrace (prefixWord ++ tailWord_8239674) baseStart_8239674 baseEnd_8239674 := by
    simpa [prefixWord, tailWord_8239674, baseEnd_8239674] using wordTrace_append hprefix tailTrace_8239674
  have hstable : (prefixWord ++ tailWord_8239674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239674).length < 2 ^ (prefixWord ++ tailWord_8239674).sum := by decide
  have hdescent : baseEnd_8239674 < baseStart_8239674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239678 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_8239678 : Nat := 118140960795 + 8239678 * 2 ^ 59
def prefixEnd_8239678 : Nat := 4983230072969 + 3 ^ 40 * 8239678 * 2
def baseEnd_8239678 : Nat := 4230915252277118455631417

theorem tailTrace_8239678 : CollatzResearch.WordTrace tailWord_8239678 prefixEnd_8239678 4230915252277118455631417 := by
  unfold tailWord_8239678
  simp only [CollatzResearch.WordTrace]
  refine ⟨37565718230382663226575961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200350497228707537208405125 37565718230382663226575961)
  ·
    refine ⟨28174288672786997419931971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37565718230382663226575961 28174288672786997419931971)
    ·
      refine ⟨42261433009180496129897957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28174288672786997419931971 42261433009180496129897957)
      ·
        refine ⟨7924018689221343024355867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42261433009180496129897957 7924018689221343024355867)
        ·
          refine ⟨11886028033832014536533801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924018689221343024355867 11886028033832014536533801)
          ·
            refine ⟨8914521025374010902400351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11886028033832014536533801 8914521025374010902400351)
            ·
              refine ⟨13371781538061016353600527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914521025374010902400351 13371781538061016353600527)
              ·
                refine ⟨20057672307091524530400791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371781538061016353600527 20057672307091524530400791)
                ·
                  refine ⟨30086508460637286795601187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20057672307091524530400791 30086508460637286795601187)
                  ·
                    refine ⟨45129762690955930193401781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30086508460637286795601187 45129762690955930193401781)
                    ·
                      refine ⟨4230915252277118455631417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45129762690955930193401781 4230915252277118455631417)
                      ·
                        rfl

theorem cell23_8239678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_8239678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239678 prefixEnd_8239678 := by exact prefixLift 8239678
  have htrace : WordTrace (prefixWord ++ tailWord_8239678) baseStart_8239678 baseEnd_8239678 := by
    simpa [prefixWord, tailWord_8239678, baseEnd_8239678] using wordTrace_append hprefix tailTrace_8239678
  have hstable : (prefixWord ++ tailWord_8239678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239678).length < 2 ^ (prefixWord ++ tailWord_8239678).sum := by decide
  have hdescent : baseEnd_8239678 < baseStart_8239678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239697 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_8239697 : Nat := 118140960795 + 8239697 * 2 ^ 59
def prefixEnd_8239697 : Nat := 4983230072969 + 3 ^ 40 * 8239697 * 2
def baseEnd_8239697 : Nat := 4230925008409553881293829

theorem tailTrace_8239697 : CollatzResearch.WordTrace tailWord_8239697 prefixEnd_8239697 4230925008409553881293829 := by
  unfold tailWord_8239697
  simp only [CollatzResearch.WordTrace]
  refine ⟨300526438829992472057549345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200350959219994981371699563 300526438829992472057549345)
  ·
    refine ⟨225394829122494354043162009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300526438829992472057549345 225394829122494354043162009)
    ·
      refine ⟨169046121841870765532371507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225394829122494354043162009 169046121841870765532371507)
      ·
        refine ⟨253569182762806148298557261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169046121841870765532371507 253569182762806148298557261)
        ·
          refine ⟨95088443536052305611958973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253569182762806148298557261 95088443536052305611958973)
          ·
            refine ⟨35658166326019614604484615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95088443536052305611958973 35658166326019614604484615)
            ·
              refine ⟨53487249489029421906726923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35658166326019614604484615 53487249489029421906726923)
              ·
                refine ⟨80230874233544132860090385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53487249489029421906726923 80230874233544132860090385)
                ·
                  refine ⟨60173155675158099645067789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80230874233544132860090385 60173155675158099645067789)
                  ·
                    refine ⟨22564933378184287366900421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60173155675158099645067789 22564933378184287366900421)
                    ·
                      refine ⟨4230925008409553881293829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22564933378184287366900421 4230925008409553881293829)
                      ·
                        rfl

theorem cell23_8239697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_8239697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239697 prefixEnd_8239697 := by exact prefixLift 8239697
  have htrace : WordTrace (prefixWord ++ tailWord_8239697) baseStart_8239697 baseEnd_8239697 := by
    simpa [prefixWord, tailWord_8239697, baseEnd_8239697] using wordTrace_append hprefix tailTrace_8239697
  have hstable : (prefixWord ++ tailWord_8239697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239697).length < 2 ^ (prefixWord ++ tailWord_8239697).sum := by decide
  have hdescent : baseEnd_8239697 < baseStart_8239697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239748 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_8239748 : Nat := 118140960795 + 8239748 * 2 ^ 59
def prefixEnd_8239748 : Nat := 4983230072969 + 3 ^ 40 * 8239748 * 2
def baseEnd_8239748 : Nat := 4230951195922933181756095

theorem tailTrace_8239748 : CollatzResearch.WordTrace tailWord_8239748 prefixEnd_8239748 4230951195922933181756095 := by
  unfold tailWord_8239748
  simp only [CollatzResearch.WordTrace]
  refine ⟨150264149476403853883827949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200352199301871805178437265 150264149476403853883827949)
  ·
    refine ⟨56349056053651445206435481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150264149476403853883827949 56349056053651445206435481)
    ·
      refine ⟨42261792040238583904826611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56349056053651445206435481 42261792040238583904826611)
      ·
        refine ⟨63392688060357875857239917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42261792040238583904826611 63392688060357875857239917)
        ·
          refine ⟨23772258022634203446464969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63392688060357875857239917 23772258022634203446464969)
          ·
            refine ⟨17829193516975652584848727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23772258022634203446464969 17829193516975652584848727)
            ·
              refine ⟨26743790275463478877273091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829193516975652584848727 26743790275463478877273091)
              ·
                refine ⟨40115685413195218315909637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26743790275463478877273091 40115685413195218315909637)
                ·
                  refine ⟨7521691014974103434233057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40115685413195218315909637 7521691014974103434233057)
                  ·
                    refine ⟨5641268261230577575674793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521691014974103434233057 5641268261230577575674793)
                    ·
                      refine ⟨4230951195922933181756095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641268261230577575674793 4230951195922933181756095)
                      ·
                        rfl

theorem cell23_8239748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_8239748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239748 prefixEnd_8239748 := by exact prefixLift 8239748
  have htrace : WordTrace (prefixWord ++ tailWord_8239748) baseStart_8239748 baseEnd_8239748 := by
    simpa [prefixWord, tailWord_8239748, baseEnd_8239748] using wordTrace_append hprefix tailTrace_8239748
  have hstable : (prefixWord ++ tailWord_8239748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239748).length < 2 ^ (prefixWord ++ tailWord_8239748).sum := by decide
  have hdescent : baseEnd_8239748 < baseStart_8239748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239767 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 7]
def baseStart_8239767 : Nat := 118140960795 + 8239767 * 2 ^ 59
def prefixEnd_8239767 : Nat := 4983230072969 + 3 ^ 40 * 8239767 * 2
def baseEnd_8239767 : Nat := 1410320317351789535806169

theorem tailTrace_8239767 : CollatzResearch.WordTrace tailWord_8239767 prefixEnd_8239767 1410320317351789535806169 := by
  unfold tailWord_8239767
  simp only [CollatzResearch.WordTrace]
  refine ⟨300528991939738874012597555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200352661293159249341731703 300528991939738874012597555)
  ·
    refine ⟨450793487909608311018896333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300528991939738874012597555 450793487909608311018896333)
    ·
      refine ⟨169047557966103116632086125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450793487909608311018896333 169047557966103116632086125)
      ·
        refine ⟨63392834237288668737032297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169047557966103116632086125 63392834237288668737032297)
        ·
          refine ⟨47544625677966501552774223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63392834237288668737032297 47544625677966501552774223)
          ·
            refine ⟨71316938516949752329161335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47544625677966501552774223 71316938516949752329161335)
            ·
              refine ⟨106975407775424628493742003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71316938516949752329161335 106975407775424628493742003)
              ·
                refine ⟨160463111663136942740613005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106975407775424628493742003 160463111663136942740613005)
                ·
                  refine ⟨60173666873676353527729877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160463111663136942740613005 60173666873676353527729877)
                  ·
                    refine ⟨1410320317351789535806169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60173666873676353527729877 1410320317351789535806169)
                    ·
                      rfl

theorem cell23_8239767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_8239767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239767 prefixEnd_8239767 := by exact prefixLift 8239767
  have htrace : WordTrace (prefixWord ++ tailWord_8239767) baseStart_8239767 baseEnd_8239767 := by
    simpa [prefixWord, tailWord_8239767, baseEnd_8239767] using wordTrace_append hprefix tailTrace_8239767
  have hstable : (prefixWord ++ tailWord_8239767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239767).length < 2 ^ (prefixWord ++ tailWord_8239767).sum := by decide
  have hdescent : baseEnd_8239767 < baseStart_8239767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239841 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_8239841 : Nat := 118140960795 + 8239841 * 2 ^ 59
def prefixEnd_8239841 : Nat := 4983230072969 + 3 ^ 40 * 8239841 * 2
def baseEnd_8239841 : Nat := 4230998949623801317893167

theorem tailTrace_8239841 : CollatzResearch.WordTrace tailWord_8239841 prefixEnd_8239841 4230998949623801317893167 := by
  unfold tailWord_8239841
  simp only [CollatzResearch.WordTrace]
  refine ⟨300531690941470784650791377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200354460627647189767194251 300531690941470784650791377)
  ·
    refine ⟨225398768206103088488093533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300531690941470784650791377 225398768206103088488093533)
    ·
      refine ⟨84524538077288658183035075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225398768206103088488093533 84524538077288658183035075)
      ·
        refine ⟨126786807115932987274552613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84524538077288658183035075 126786807115932987274552613)
        ·
          refine ⟨23772526334237435113978615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126786807115932987274552613 23772526334237435113978615)
          ·
            refine ⟨35658789501356152670967923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772526334237435113978615 35658789501356152670967923)
            ·
              refine ⟨53488184252034229006451885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35658789501356152670967923 53488184252034229006451885)
              ·
                refine ⟨20058069094512835877419457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53488184252034229006451885 20058069094512835877419457)
                ·
                  refine ⟨15043551820884626908064593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20058069094512835877419457 15043551820884626908064593)
                  ·
                    refine ⟨11282663865663470181048445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15043551820884626908064593 11282663865663470181048445)
                    ·
                      refine ⟨4230998949623801317893167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282663865663470181048445 4230998949623801317893167)
                      ·
                        rfl

theorem cell23_8239841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_8239841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239841 prefixEnd_8239841 := by exact prefixLift 8239841
  have htrace : WordTrace (prefixWord ++ tailWord_8239841) baseStart_8239841 baseEnd_8239841 := by
    simpa [prefixWord, tailWord_8239841, baseEnd_8239841] using wordTrace_append hprefix tailTrace_8239841
  have hstable : (prefixWord ++ tailWord_8239841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239841).length < 2 ^ (prefixWord ++ tailWord_8239841).sum := by decide
  have hdescent : baseEnd_8239841 < baseStart_8239841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239871 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_8239871 : Nat := 118140960795 + 8239871 * 2 ^ 59
def prefixEnd_8239871 : Nat := 4983230072969 + 3 ^ 40 * 8239871 * 2
def baseEnd_8239871 : Nat := 4231014354043436200518029

theorem tailTrace_8239871 : CollatzResearch.WordTrace tailWord_8239871 prefixEnd_8239871 4231014354043436200518029 := by
  unfold tailWord_8239871
  simp only [CollatzResearch.WordTrace]
  refine ⟨300532785131362099774383467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200355190087574733182922311 300532785131362099774383467)
  ·
    refine ⟨450799177697043149661575201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300532785131362099774383467 450799177697043149661575201)
    ·
      refine ⟨338099383272782362246181401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450799177697043149661575201 338099383272782362246181401)
      ·
        refine ⟨253574537454586771684636051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338099383272782362246181401 253574537454586771684636051)
        ·
          refine ⟨380361806181880157526954077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253574537454586771684636051 380361806181880157526954077)
          ·
            refine ⟨142635677318205059072607779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380361806181880157526954077 142635677318205059072607779)
            ·
              refine ⟨213953515977307588608911669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142635677318205059072607779 213953515977307588608911669)
              ·
                refine ⟨20058142122872586432085469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213953515977307588608911669 20058142122872586432085469)
                ·
                  refine ⟨7521803296077219912032051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20058142122872586432085469 7521803296077219912032051)
                  ·
                    refine ⟨11282704944115829868048077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521803296077219912032051 11282704944115829868048077)
                    ·
                      refine ⟨4231014354043436200518029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282704944115829868048077 4231014354043436200518029)
                      ·
                        rfl

theorem cell23_8239871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_8239871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239871 prefixEnd_8239871 := by exact prefixLift 8239871
  have htrace : WordTrace (prefixWord ++ tailWord_8239871) baseStart_8239871 baseEnd_8239871 := by
    simpa [prefixWord, tailWord_8239871, baseEnd_8239871] using wordTrace_append hprefix tailTrace_8239871
  have hstable : (prefixWord ++ tailWord_8239871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239871).length < 2 ^ (prefixWord ++ tailWord_8239871).sum := by decide
  have hdescent : baseEnd_8239871 < baseStart_8239871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239881 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 4, 3, 2]
def baseStart_8239881 : Nat := 118140960795 + 8239881 * 2 ^ 59
def prefixEnd_8239881 : Nat := 4983230072969 + 3 ^ 40 * 8239881 * 2
def baseEnd_8239881 : Nat := 4231019488849981161392983

theorem tailTrace_8239881 : CollatzResearch.WordTrace tailWord_8239881 prefixEnd_8239881 4231019488849981161392983 := by
  unfold tailWord_8239881
  simp only [CollatzResearch.WordTrace]
  refine ⟨300533149861325871482247497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200355433240883914321498331 300533149861325871482247497)
  ·
    refine ⟨225399862395994403611685623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300533149861325871482247497 225399862395994403611685623)
    ·
      refine ⟨338099793593991605417528435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225399862395994403611685623 338099793593991605417528435)
      ·
        refine ⟨507149690390987408126292653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338099793593991605417528435 507149690390987408126292653)
        ·
          refine ⟨190181133896620278047359745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507149690390987408126292653 190181133896620278047359745)
          ·
            refine ⟨142635850422465208535519809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190181133896620278047359745 142635850422465208535519809)
            ·
              refine ⟨106976887816848906401639857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142635850422465208535519809 106976887816848906401639857)
              ·
                refine ⟨80232665862636679801229893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106976887816848906401639857 80232665862636679801229893)
                ·
                  refine ⟨15043624849244377462730605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80232665862636679801229893 15043624849244377462730605)
                  ·
                    refine ⟨5641359318466641548523977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15043624849244377462730605 5641359318466641548523977)
                    ·
                      refine ⟨4231019488849981161392983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641359318466641548523977 4231019488849981161392983)
                      ·
                        rfl

theorem cell23_8239881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3, 2].length) (baseStart_8239881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239881 prefixEnd_8239881 := by exact prefixLift 8239881
  have htrace : WordTrace (prefixWord ++ tailWord_8239881) baseStart_8239881 baseEnd_8239881 := by
    simpa [prefixWord, tailWord_8239881, baseEnd_8239881] using wordTrace_append hprefix tailTrace_8239881
  have hstable : (prefixWord ++ tailWord_8239881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239881).length < 2 ^ (prefixWord ++ tailWord_8239881).sum := by decide
  have hdescent : baseEnd_8239881 < baseStart_8239881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239905 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_8239905 : Nat := 118140960795 + 8239905 * 2 ^ 59
def prefixEnd_8239905 : Nat := 4983230072969 + 3 ^ 40 * 8239905 * 2
def baseEnd_8239905 : Nat := 4231031812385689067492873

theorem tailTrace_8239905 : CollatzResearch.WordTrace tailWord_8239905 prefixEnd_8239905 4231031812385689067492873 := by
  unfold tailWord_8239905
  simp only [CollatzResearch.WordTrace]
  refine ⟨300534025213238923581121169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200356016808825949054080779 300534025213238923581121169)
  ·
    refine ⟨225400518909929192685840877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300534025213238923581121169 225400518909929192685840877)
    ·
      refine ⟨84525194591223447257190329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225400518909929192685840877 84525194591223447257190329)
      ·
        refine ⟨63393895943417585442892747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84525194591223447257190329 63393895943417585442892747)
        ·
          refine ⟨95090843915126378164339121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63393895943417585442892747 95090843915126378164339121)
          ·
            refine ⟨71318132936344783623254341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95090843915126378164339121 71318132936344783623254341)
            ·
              refine ⟨13372149925564646929360189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71318132936344783623254341 13372149925564646929360189)
              ·
                refine ⟨5014556222086742598510071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13372149925564646929360189 5014556222086742598510071)
                ·
                  refine ⟨7521834333130113897765107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014556222086742598510071 7521834333130113897765107)
                  ·
                    refine ⟨11282751499695170846647661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521834333130113897765107 11282751499695170846647661)
                    ·
                      refine ⟨4231031812385689067492873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282751499695170846647661 4231031812385689067492873)
                      ·
                        rfl

theorem cell23_8239905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_8239905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239905 prefixEnd_8239905 := by exact prefixLift 8239905
  have htrace : WordTrace (prefixWord ++ tailWord_8239905) baseStart_8239905 baseEnd_8239905 := by
    simpa [prefixWord, tailWord_8239905, baseEnd_8239905] using wordTrace_append hprefix tailTrace_8239905
  have hstable : (prefixWord ++ tailWord_8239905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239905).length < 2 ^ (prefixWord ++ tailWord_8239905).sum := by decide
  have hdescent : baseEnd_8239905 < baseStart_8239905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239908 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_8239908 : Nat := 118140960795 + 8239908 * 2 ^ 59
def prefixEnd_8239908 : Nat := 4983230072969 + 3 ^ 40 * 8239908 * 2
def baseEnd_8239908 : Nat := 1410344450942550851918453

theorem tailTrace_8239908 : CollatzResearch.WordTrace tailWord_8239908 prefixEnd_8239908 1410344450942550851918453 := by
  unfold tailWord_8239908
  simp only [CollatzResearch.WordTrace]
  refine ⟨150267067316114027546740189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200356089754818703395653585 150267067316114027546740189)
  ·
    refine ⟨56350150243542760330027571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150267067316114027546740189 56350150243542760330027571)
    ·
      refine ⟨84525225365314140495041357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56350150243542760330027571 84525225365314140495041357)
      ·
        refine ⟨31696959511992802685640509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84525225365314140495041357 31696959511992802685640509)
        ·
          refine ⟨11886359816997301007115191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31696959511992802685640509 11886359816997301007115191)
          ·
            refine ⟨17829539725495951510672787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886359816997301007115191 17829539725495951510672787)
            ·
              refine ⟨26744309588243927266009181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829539725495951510672787 26744309588243927266009181)
              ·
                refine ⟨10029116095591472724753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26744309588243927266009181 10029116095591472724753443)
                ·
                  refine ⟨15043674143387209087130165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029116095591472724753443 15043674143387209087130165)
                  ·
                    refine ⟨1410344450942550851918453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15043674143387209087130165 1410344450942550851918453)
                    ·
                      rfl

theorem cell23_8239908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_8239908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239908 prefixEnd_8239908 := by exact prefixLift 8239908
  have htrace : WordTrace (prefixWord ++ tailWord_8239908) baseStart_8239908 baseEnd_8239908 := by
    simpa [prefixWord, tailWord_8239908, baseEnd_8239908] using wordTrace_append hprefix tailTrace_8239908
  have hstable : (prefixWord ++ tailWord_8239908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239908).length < 2 ^ (prefixWord ++ tailWord_8239908).sum := by decide
  have hdescent : baseEnd_8239908 < baseStart_8239908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239921 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_8239921 : Nat := 118140960795 + 8239921 * 2 ^ 59
def prefixEnd_8239921 : Nat := 4983230072969 + 3 ^ 40 * 8239921 * 2
def baseEnd_8239921 : Nat := 1410346676025387001630933

theorem tailTrace_8239921 : CollatzResearch.WordTrace tailWord_8239921 prefixEnd_8239921 1410346676025387001630933 := by
  unfold tailWord_8239921
  simp only [CollatzResearch.WordTrace]
  refine ⟨300534608781180958313703617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200356405854120638875802411 300534608781180958313703617)
  ·
    refine ⟨225400956585885718735277713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300534608781180958313703617 225400956585885718735277713)
    ·
      refine ⟨169050717439414289051458285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225400956585885718735277713 169050717439414289051458285)
      ·
        refine ⟨63394019039780358394296857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169050717439414289051458285 63394019039780358394296857)
        ·
          refine ⟨47545514279835268795722643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63394019039780358394296857 47545514279835268795722643)
          ·
            refine ⟨71318271419752903193583965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47545514279835268795722643 71318271419752903193583965)
            ·
              refine ⟨26744351782407338697593987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71318271419752903193583965 26744351782407338697593987)
              ·
                refine ⟨40116527673611008046390981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26744351782407338697593987 40116527673611008046390981)
                ·
                  refine ⟨7521848938802064008698309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40116527673611008046390981 7521848938802064008698309)
                  ·
                    refine ⟨1410346676025387001630933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7521848938802064008698309 1410346676025387001630933)
                    ·
                      rfl

theorem cell23_8239921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_8239921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239921 prefixEnd_8239921 := by exact prefixLift 8239921
  have htrace : WordTrace (prefixWord ++ tailWord_8239921) baseStart_8239921 baseEnd_8239921 := by
    simpa [prefixWord, tailWord_8239921, baseEnd_8239921] using wordTrace_append hprefix tailTrace_8239921
  have hstable : (prefixWord ++ tailWord_8239921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239921).length < 2 ^ (prefixWord ++ tailWord_8239921).sum := by decide
  have hdescent : baseEnd_8239921 < baseStart_8239921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239942 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_8239942 : Nat := 118140960795 + 8239942 * 2 ^ 59
def prefixEnd_8239942 : Nat := 4983230072969 + 3 ^ 40 * 8239942 * 2
def baseEnd_8239942 : Nat := 1410350270389968474243401

theorem tailTrace_8239942 : CollatzResearch.WordTrace tailWord_8239942 prefixEnd_8239942 1410350270389968474243401 := by
  unfold tailWord_8239942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391730459815777465631815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200356916476069919266812053 9391730459815777465631815)
  ·
    refine ⟨14087595689723666198447723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9391730459815777465631815 14087595689723666198447723)
    ·
      refine ⟨21131393534585499297671585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087595689723666198447723 21131393534585499297671585)
      ·
        refine ⟨15848545150939124473253689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21131393534585499297671585 15848545150939124473253689)
        ·
          refine ⟨11886408863204343354940267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15848545150939124473253689 11886408863204343354940267)
          ·
            refine ⟨17829613294806515032410401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886408863204343354940267 17829613294806515032410401)
            ·
              refine ⟨13372209971104886274307801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17829613294806515032410401 13372209971104886274307801)
              ·
                refine ⟨10029157478328664705730851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372209971104886274307801 10029157478328664705730851)
                ·
                  refine ⟨15043736217492997058596277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029157478328664705730851 15043736217492997058596277)
                  ·
                    refine ⟨1410350270389968474243401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15043736217492997058596277 1410350270389968474243401)
                    ·
                      rfl

theorem cell23_8239942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_8239942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239942 prefixEnd_8239942 := by exact prefixLift 8239942
  have htrace : WordTrace (prefixWord ++ tailWord_8239942) baseStart_8239942 baseEnd_8239942 := by
    simpa [prefixWord, tailWord_8239942, baseEnd_8239942] using wordTrace_append hprefix tailTrace_8239942
  have hstable : (prefixWord ++ tailWord_8239942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239942).length < 2 ^ (prefixWord ++ tailWord_8239942).sum := by decide
  have hdescent : baseEnd_8239942 < baseStart_8239942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239948 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_8239948 : Nat := 118140960795 + 8239948 * 2 ^ 59
def prefixEnd_8239948 : Nat := 4983230072969 + 3 ^ 40 * 8239948 * 2
def baseEnd_8239948 : Nat := 4231053892053832399255175

theorem tailTrace_8239948 : CollatzResearch.WordTrace tailWord_8239948 prefixEnd_8239948 4231053892053832399255175 := by
  unfold tailWord_8239948
  simp only [CollatzResearch.WordTrace]
  refine ⟨150267796776041570962468249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200357062368055427949957665 150267796776041570962468249)
  ·
    refine ⟨112700847582031178221851187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150267796776041570962468249 112700847582031178221851187)
    ·
      refine ⟨169051271373046767332776781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112700847582031178221851187 169051271373046767332776781)
      ·
        refine ⟨63394226764892537749791293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169051271373046767332776781 63394226764892537749791293)
        ·
          refine ⟨23772835036834701656171735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63394226764892537749791293 23772835036834701656171735)
          ·
            refine ⟨35659252555252052484257603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23772835036834701656171735 35659252555252052484257603)
            ·
              refine ⟨53488878832878078726386405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35659252555252052484257603 53488878832878078726386405)
              ·
                refine ⟨10029164781164639761197451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53488878832878078726386405 10029164781164639761197451)
                ·
                  refine ⟨15043747171746959641796177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029164781164639761197451 15043747171746959641796177)
                  ·
                    refine ⟨11282810378810219731347133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15043747171746959641796177 11282810378810219731347133)
                    ·
                      refine ⟨4231053892053832399255175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282810378810219731347133 4231053892053832399255175)
                      ·
                        rfl

theorem cell23_8239948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_8239948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239948 prefixEnd_8239948 := by exact prefixLift 8239948
  have htrace : WordTrace (prefixWord ++ tailWord_8239948) baseStart_8239948 baseEnd_8239948 := by
    simpa [prefixWord, tailWord_8239948, baseEnd_8239948] using wordTrace_append hprefix tailTrace_8239948
  have hstable : (prefixWord ++ tailWord_8239948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239948).length < 2 ^ (prefixWord ++ tailWord_8239948).sum := by decide
  have hdescent : baseEnd_8239948 < baseStart_8239948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239962 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_8239962 : Nat := 118140960795 + 8239962 * 2 ^ 59
def prefixEnd_8239962 : Nat := 4983230072969 + 3 ^ 40 * 8239962 * 2
def baseEnd_8239962 : Nat := 4231061080782995344480111

theorem tailTrace_8239962 : CollatzResearch.WordTrace tailWord_8239962 prefixEnd_8239962 4231061080782995344480111 := by
  unfold tailWord_8239962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75134026043508105578986535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200357402782688281543964093 75134026043508105578986535)
  ·
    refine ⟨112701039065262158368479803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75134026043508105578986535 112701039065262158368479803)
    ·
      refine ⟨169051558597893237552719705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112701039065262158368479803 169051558597893237552719705)
      ·
        refine ⟨126788668948419928164539779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169051558597893237552719705 126788668948419928164539779)
        ·
          refine ⟨190183003422629892246809669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126788668948419928164539779 190183003422629892246809669)
          ·
            refine ⟨35659313141743104796276813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190183003422629892246809669 35659313141743104796276813)
            ·
              refine ⟨13372242428153664298603805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35659313141743104796276813 13372242428153664298603805)
              ·
                refine ⟨5014590910557624111976427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13372242428153664298603805 5014590910557624111976427)
                ·
                  refine ⟨7521886365836436167964641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014590910557624111976427 7521886365836436167964641)
                  ·
                    refine ⟨5641414774377327125973481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521886365836436167964641 5641414774377327125973481)
                    ·
                      refine ⟨4231061080782995344480111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641414774377327125973481 4231061080782995344480111)
                      ·
                        rfl

theorem cell23_8239962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_8239962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239962 prefixEnd_8239962 := by exact prefixLift 8239962
  have htrace : WordTrace (prefixWord ++ tailWord_8239962) baseStart_8239962 baseEnd_8239962 := by
    simpa [prefixWord, tailWord_8239962, baseEnd_8239962] using wordTrace_append hprefix tailTrace_8239962
  have hstable : (prefixWord ++ tailWord_8239962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239962).length < 2 ^ (prefixWord ++ tailWord_8239962).sum := by decide
  have hdescent : baseEnd_8239962 < baseStart_8239962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239994 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_8239994 : Nat := 118140960795 + 8239994 * 2 ^ 59
def prefixEnd_8239994 : Nat := 4983230072969 + 3 ^ 40 * 8239994 * 2
def baseEnd_8239994 : Nat := 1410359170721313073093321

theorem tailTrace_8239994 : CollatzResearch.WordTrace tailWord_8239994 prefixEnd_8239994 1410359170721313073093321 := by
  unfold tailWord_8239994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75134317827479122945277759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200358180873277661187407357 75134317827479122945277759)
  ·
    refine ⟨112701476741218684417916639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75134317827479122945277759 112701476741218684417916639)
    ·
      refine ⟨169052215111828026626874959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112701476741218684417916639 169052215111828026626874959)
      ·
        refine ⟨253578322667742039940312439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169052215111828026626874959 253578322667742039940312439)
        ·
          refine ⟨380367484001613059910468659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253578322667742039940312439 380367484001613059910468659)
          ·
            refine ⟨570551226002419589865702989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380367484001613059910468659 570551226002419589865702989)
            ·
              refine ⟨213956709750907346199638621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570551226002419589865702989 213956709750907346199638621)
              ·
                refine ⟨80233766156590254824864483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213956709750907346199638621 80233766156590254824864483)
                ·
                  refine ⟨120350649234885382237296725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80233766156590254824864483 120350649234885382237296725)
                  ·
                    refine ⟨1410359170721313073093321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120350649234885382237296725 1410359170721313073093321)
                    ·
                      rfl

theorem cell23_8239994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_8239994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239994 prefixEnd_8239994 := by exact prefixLift 8239994
  have htrace : WordTrace (prefixWord ++ tailWord_8239994) baseStart_8239994 baseEnd_8239994 := by
    simpa [prefixWord, tailWord_8239994, baseEnd_8239994] using wordTrace_append hprefix tailTrace_8239994
  have hstable : (prefixWord ++ tailWord_8239994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239994).length < 2 ^ (prefixWord ++ tailWord_8239994).sum := by decide
  have hdescent : baseEnd_8239994 < baseStart_8239994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8239995 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 2, 1, 3]
def baseStart_8239995 : Nat := 118140960795 + 8239995 * 2 ^ 59
def prefixEnd_8239995 : Nat := 4983230072969 + 3 ^ 40 * 8239995 * 2
def baseEnd_8239995 : Nat := 4231078025644593715367459

theorem tailTrace_8239995 : CollatzResearch.WordTrace tailWord_8239995 prefixEnd_8239995 4231078025644593715367459 := by
  unfold tailWord_8239995
  simp only [CollatzResearch.WordTrace]
  refine ⟨300537307782912868951897439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200358205188608579301264959 300537307782912868951897439)
  ·
    refine ⟨450805961674369303427846159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300537307782912868951897439 450805961674369303427846159)
    ·
      refine ⟨676208942511553955141769239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450805961674369303427846159 676208942511553955141769239)
      ·
        refine ⟨1014313413767330932712653859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676208942511553955141769239 1014313413767330932712653859)
        ·
          refine ⟨1521470120650996399068980789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014313413767330932712653859 1521470120650996399068980789)
          ·
            refine ⟨142637823811030912412716949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1521470120650996399068980789 142637823811030912412716949)
            ·
              refine ⟨6686147991142074019346107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142637823811030912412716949 6686147991142074019346107)
              ·
                refine ⟨10029221986713111029019161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686147991142074019346107 10029221986713111029019161)
                ·
                  refine ⟨7521916490034833271764371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029221986713111029019161 7521916490034833271764371)
                  ·
                    refine ⟨11282874735052249907646557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521916490034833271764371 11282874735052249907646557)
                    ·
                      refine ⟨4231078025644593715367459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11282874735052249907646557 4231078025644593715367459)
                      ·
                        rfl

theorem cell23_8239995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 1, 3].length) (baseStart_8239995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8239995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8239995 prefixEnd_8239995 := by exact prefixLift 8239995
  have htrace : WordTrace (prefixWord ++ tailWord_8239995) baseStart_8239995 baseEnd_8239995 := by
    simpa [prefixWord, tailWord_8239995, baseEnd_8239995] using wordTrace_append hprefix tailTrace_8239995
  have hstable : (prefixWord ++ tailWord_8239995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8239995).length < 2 ^ (prefixWord ++ tailWord_8239995).sum := by decide
  have hdescent : baseEnd_8239995 < baseStart_8239995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8239995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240005 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_8240005 : Nat := 118140960795 + 8240005 * 2 ^ 59
def prefixEnd_8240005 : Nat := 4983230072969 + 3 ^ 40 * 8240005 * 2
def baseEnd_8240005 : Nat := 4231083160451138676242413

theorem tailTrace_8240005 : CollatzResearch.WordTrace tailWord_8240005 prefixEnd_8240005 4231083160451138676242413 := by
  unfold tailWord_8240005
  simp only [CollatzResearch.WordTrace]
  refine ⟨300537672512876640659761469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200358448341917760439840979 300537672512876640659761469)
  ·
    refine ⟨112701627192328740247410551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300537672512876640659761469 112701627192328740247410551)
    ·
      refine ⟨169052440788493110371115827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112701627192328740247410551 169052440788493110371115827)
      ·
        refine ⟨253578661182739665556673741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169052440788493110371115827 253578661182739665556673741)
        ·
          refine ⟨95091997943527374583752653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253578661182739665556673741 95091997943527374583752653)
          ·
            refine ⟨35659499228822765468907245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95091997943527374583752653 35659499228822765468907245)
            ·
              refine ⟨13372312210808537050840217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35659499228822765468907245 13372312210808537050840217)
              ·
                refine ⟨10029234158106402788130163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372312210808537050840217 10029234158106402788130163)
                ·
                  refine ⟨15043851237159604182195245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029234158106402788130163 15043851237159604182195245)
                  ·
                    refine ⟨5641444213934851568323217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15043851237159604182195245 5641444213934851568323217)
                    ·
                      refine ⟨4231083160451138676242413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641444213934851568323217 4231083160451138676242413)
                      ·
                        rfl

theorem cell23_8240005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_8240005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240005 prefixEnd_8240005 := by exact prefixLift 8240005
  have htrace : WordTrace (prefixWord ++ tailWord_8240005) baseStart_8240005 baseEnd_8240005 := by
    simpa [prefixWord, tailWord_8240005, baseEnd_8240005] using wordTrace_append hprefix tailTrace_8240005
  have hstable : (prefixWord ++ tailWord_8240005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240005).length < 2 ^ (prefixWord ++ tailWord_8240005).sum := by decide
  have hdescent : baseEnd_8240005 < baseStart_8240005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240021 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_8240021 : Nat := 118140960795 + 8240021 * 2 ^ 59
def prefixEnd_8240021 : Nat := 4983230072969 + 3 ^ 40 * 8240021 * 2
def baseEnd_8240021 : Nat := 4231091376141610613642339

theorem tailTrace_8240021 : CollatzResearch.WordTrace tailWord_8240021 prefixEnd_8240021 4231091376141610613642339 := by
  unfold tailWord_8240021
  simp only [CollatzResearch.WordTrace]
  refine ⟨300538256080818675392343917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200358837387212450261562611 300538256080818675392343917)
  ·
    refine ⟨112701846030307003272128969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300538256080818675392343917 112701846030307003272128969)
    ·
      refine ⟨84526384522730252454096727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112701846030307003272128969 84526384522730252454096727)
      ·
        refine ⟨126789576784095378681145091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84526384522730252454096727 126789576784095378681145091)
        ·
          refine ⟨190184365176143068021717637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126789576784095378681145091 190184365176143068021717637)
          ·
            refine ⟨35659568470526825254072057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190184365176143068021717637 35659568470526825254072057)
            ·
              refine ⟨26744676352895118940554043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35659568470526825254072057 26744676352895118940554043)
              ·
                refine ⟨40117014529342678410831065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26744676352895118940554043 40117014529342678410831065)
                ·
                  refine ⟨30087760897007008808123299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40117014529342678410831065 30087760897007008808123299)
                  ·
                    refine ⟨45131641345510513212184949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30087760897007008808123299 45131641345510513212184949)
                    ·
                      refine ⟨4231091376141610613642339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45131641345510513212184949 4231091376141610613642339)
                      ·
                        rfl

theorem cell23_8240021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_8240021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240021 prefixEnd_8240021 := by exact prefixLift 8240021
  have htrace : WordTrace (prefixWord ++ tailWord_8240021) baseStart_8240021 baseEnd_8240021 := by
    simpa [prefixWord, tailWord_8240021, baseEnd_8240021] using wordTrace_append hprefix tailTrace_8240021
  have hstable : (prefixWord ++ tailWord_8240021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240021).length < 2 ^ (prefixWord ++ tailWord_8240021).sum := by decide
  have hdescent : baseEnd_8240021 < baseStart_8240021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240035 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 2, 2, 2]
def baseStart_8240035 : Nat := 118140960795 + 8240035 * 2 ^ 59
def prefixEnd_8240035 : Nat := 4983230072969 + 3 ^ 40 * 8240035 * 2
def baseEnd_8240035 : Nat := 4231098564870773558867275

theorem tailTrace_8240035 : CollatzResearch.WordTrace tailWord_8240035 prefixEnd_8240035 4231098564870773558867275 := by
  unfold tailWord_8240035
  simp only [CollatzResearch.WordTrace]
  refine ⟨300538766702767955783353559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200359177801845303855569039 300538766702767955783353559)
  ·
    refine ⟨450808150054151933675030339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300538766702767955783353559 450808150054151933675030339)
    ·
      refine ⟨676212225081227900512545509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450808150054151933675030339 676212225081227900512545509)
      ·
        refine ⟨126789792202730231346102283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 676212225081227900512545509 126789792202730231346102283)
        ·
          refine ⟨190184688304095347019153425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126789792202730231346102283 190184688304095347019153425)
          ·
            refine ⟨142638516228071510264365069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190184688304095347019153425 142638516228071510264365069)
            ·
              refine ⟨53489443585526816349136901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142638516228071510264365069 53489443585526816349136901)
              ·
                refine ⟨10029270672286278065463169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53489443585526816349136901 10029270672286278065463169)
                ·
                  refine ⟨7521953004214708549097377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029270672286278065463169 7521953004214708549097377)
                  ·
                    refine ⟨5641464753161031411823033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521953004214708549097377 5641464753161031411823033)
                    ·
                      refine ⟨4231098564870773558867275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641464753161031411823033 4231098564870773558867275)
                      ·
                        rfl

theorem cell23_8240035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_8240035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240035 prefixEnd_8240035 := by exact prefixLift 8240035
  have htrace : WordTrace (prefixWord ++ tailWord_8240035) baseStart_8240035 baseEnd_8240035 := by
    simpa [prefixWord, tailWord_8240035, baseEnd_8240035] using wordTrace_append hprefix tailTrace_8240035
  have hstable : (prefixWord ++ tailWord_8240035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240035).length < 2 ^ (prefixWord ++ tailWord_8240035).sum := by decide
  have hdescent : baseEnd_8240035 < baseStart_8240035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240045 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_8240045 : Nat := 118140960795 + 8240045 * 2 ^ 59
def prefixEnd_8240045 : Nat := 4983230072969 + 3 ^ 40 * 8240045 * 2
def baseEnd_8240045 : Nat := 1410367899892439506580743

theorem tailTrace_8240045 : CollatzResearch.WordTrace tailWord_8240045 prefixEnd_8240045 1410367899892439506580743 := by
  unfold tailWord_8240045
  simp only [CollatzResearch.WordTrace]
  refine ⟨300539131432731727491217589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200359420955154484994145059 300539131432731727491217589)
  ·
    refine ⟨28175543571818599452301649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300539131432731727491217589 28175543571818599452301649)
    ·
      refine ⟨21131657678863949589226237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28175543571818599452301649 21131657678863949589226237)
      ·
        refine ⟨7924371629573981095959839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21131657678863949589226237 7924371629573981095959839)
        ·
          refine ⟨11886557444360971643939759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924371629573981095959839 11886557444360971643939759)
          ·
            refine ⟨17829836166541457465909639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886557444360971643939759 17829836166541457465909639)
            ·
              refine ⟨26744754249812186198864459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829836166541457465909639 26744754249812186198864459)
              ·
                refine ⟨40117131374718279298296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26744754249812186198864459 40117131374718279298296689)
                ·
                  refine ⟨30087848531038709473722517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40117131374718279298296689 30087848531038709473722517)
                  ·
                    refine ⟨1410367899892439506580743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30087848531038709473722517 1410367899892439506580743)
                    ·
                      rfl

theorem cell23_8240045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_8240045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240045 prefixEnd_8240045 := by exact prefixLift 8240045
  have htrace : WordTrace (prefixWord ++ tailWord_8240045) baseStart_8240045 baseEnd_8240045 := by
    simpa [prefixWord, tailWord_8240045, baseEnd_8240045] using wordTrace_append hprefix tailTrace_8240045
  have hstable : (prefixWord ++ tailWord_8240045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240045).length < 2 ^ (prefixWord ++ tailWord_8240045).sum := by decide
  have hdescent : baseEnd_8240045 < baseStart_8240045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240052 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_8240052 : Nat := 118140960795 + 8240052 * 2 ^ 59
def prefixEnd_8240052 : Nat := 4983230072969 + 3 ^ 40 * 8240052 * 2
def baseEnd_8240052 : Nat := 4231107294041899992354697

theorem tailTrace_8240052 : CollatzResearch.WordTrace tailWord_8240052 prefixEnd_8240052 4231107294041899992354697 := by
  unfold tailWord_8240052
  simp only [CollatzResearch.WordTrace]
  refine ⟨150269693371853183843361205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200359591162470911791148273 150269693371853183843361205)
  ·
    refine ⟨14087783753611235985315113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150269693371853183843361205 14087783753611235985315113)
    ·
      refine ⟨10565837815208426988986335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14087783753611235985315113 10565837815208426988986335)
      ·
        refine ⟨15848756722812640483479503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10565837815208426988986335 15848756722812640483479503)
        ·
          refine ⟨23773135084218960725219255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15848756722812640483479503 23773135084218960725219255)
          ·
            refine ⟨35659702626328441087828883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23773135084218960725219255 35659702626328441087828883)
            ·
              refine ⟨53489553939492661631743325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35659702626328441087828883 53489553939492661631743325)
              ·
                refine ⟨20058582727309748111903747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53489553939492661631743325 20058582727309748111903747)
                ·
                  refine ⟨30087874090964622167855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20058582727309748111903747 30087874090964622167855621)
                  ·
                    refine ⟨5641476392055866656472929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30087874090964622167855621 5641476392055866656472929)
                    ·
                      refine ⟨4231107294041899992354697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641476392055866656472929 4231107294041899992354697)
                      ·
                        rfl

theorem cell23_8240052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_8240052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240052 prefixEnd_8240052 := by exact prefixLift 8240052
  have htrace : WordTrace (prefixWord ++ tailWord_8240052) baseStart_8240052 baseEnd_8240052 := by
    simpa [prefixWord, tailWord_8240052, baseEnd_8240052] using wordTrace_append hprefix tailTrace_8240052
  have hstable : (prefixWord ++ tailWord_8240052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240052).length < 2 ^ (prefixWord ++ tailWord_8240052).sum := by decide
  have hdescent : baseEnd_8240052 < baseStart_8240052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240086 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_8240086 : Nat := 118140960795 + 8240086 * 2 ^ 59
def prefixEnd_8240086 : Nat := 4983230072969 + 3 ^ 40 * 8240086 * 2
def baseEnd_8240086 : Nat := 4231124752384152859329541

theorem tailTrace_8240086 : CollatzResearch.WordTrace tailWord_8240086 prefixEnd_8240086 4231124752384152859329541 := by
  unfold tailWord_8240086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783789176598949468341257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200360417883722127662306741 18783789176598949468341257)
  ·
    refine ⟨14087841882449212101255943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18783789176598949468341257 14087841882449212101255943)
    ·
      refine ⟨21131762823673818151883915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087841882449212101255943 21131762823673818151883915)
      ·
        refine ⟨31697644235510727227825873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21131762823673818151883915 31697644235510727227825873)
        ·
          refine ⟨23773233176633045420869405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31697644235510727227825873 23773233176633045420869405)
          ·
            refine ⟨8914962441237392032826027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23773233176633045420869405 8914962441237392032826027)
            ·
              refine ⟨13372443661856088049239041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914962441237392032826027 13372443661856088049239041)
              ·
                refine ⟨10029332746392066036929281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13372443661856088049239041 10029332746392066036929281)
                ·
                  refine ⟨7521999559794049527696961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029332746392066036929281 7521999559794049527696961)
                  ·
                    refine ⟨5641499669845537145772721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521999559794049527696961 5641499669845537145772721)
                    ·
                      refine ⟨4231124752384152859329541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641499669845537145772721 4231124752384152859329541)
                      ·
                        rfl

theorem cell23_8240086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_8240086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240086 prefixEnd_8240086 := by exact prefixLift 8240086
  have htrace : WordTrace (prefixWord ++ tailWord_8240086) baseStart_8240086 baseEnd_8240086 := by
    simpa [prefixWord, tailWord_8240086, baseEnd_8240086] using wordTrace_append hprefix tailTrace_8240086
  have hstable : (prefixWord ++ tailWord_8240086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240086).length < 2 ^ (prefixWord ++ tailWord_8240086).sum := by decide
  have hdescent : baseEnd_8240086 < baseStart_8240086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240121 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_8240121 : Nat := 118140960795 + 8240121 * 2 ^ 59
def prefixEnd_8240121 : Nat := 4983230072969 + 3 ^ 40 * 8240121 * 2
def baseEnd_8240121 : Nat := 4231142724207060222391879

theorem tailTrace_8240121 : CollatzResearch.WordTrace tailWord_8240121 prefixEnd_8240121 4231142724207060222391879 := by
  unfold tailWord_8240121
  simp only [CollatzResearch.WordTrace]
  refine ⟨300541903380456392470984217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200361268920304261647322811 300541903380456392470984217)
  ·
    refine ⟨225406427535342294353238163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300541903380456392470984217 225406427535342294353238163)
    ·
      refine ⟨338109641303013441529857245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225406427535342294353238163 338109641303013441529857245)
      ·
        refine ⟨126791115488630040573696467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338109641303013441529857245 126791115488630040573696467)
        ·
          refine ⟨190186673232945060860544701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126791115488630040573696467 190186673232945060860544701)
          ·
            refine ⟨71320002462354397822704263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190186673232945060860544701 71320002462354397822704263)
            ·
              refine ⟨106980003693531596734056395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71320002462354397822704263 106980003693531596734056395)
              ·
                refine ⟨160470005540297395101084593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106980003693531596734056395 160470005540297395101084593)
                ·
                  refine ⟨120352504155223046325813445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160470005540297395101084593 120352504155223046325813445)
                  ·
                    refine ⟨22566094529104321186090021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120352504155223046325813445 22566094529104321186090021)
                    ·
                      refine ⟨4231142724207060222391879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22566094529104321186090021 4231142724207060222391879)
                      ·
                        rfl

theorem cell23_8240121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_8240121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240121 prefixEnd_8240121 := by exact prefixLift 8240121
  have htrace : WordTrace (prefixWord ++ tailWord_8240121) baseStart_8240121 baseEnd_8240121 := by
    simpa [prefixWord, tailWord_8240121, baseEnd_8240121] using wordTrace_append hprefix tailTrace_8240121
  have hstable : (prefixWord ++ tailWord_8240121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240121).length < 2 ^ (prefixWord ++ tailWord_8240121).sum := by decide
  have hdescent : baseEnd_8240121 < baseStart_8240121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240178 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_8240178 : Nat := 118140960795 + 8240178 * 2 ^ 59
def prefixEnd_8240178 : Nat := 4983230072969 + 3 ^ 40 * 8240178 * 2
def baseEnd_8240178 : Nat := 1410390664201455499793039

theorem tailTrace_8240178 : CollatzResearch.WordTrace tailWord_8240178 prefixEnd_8240178 1410390664201455499793039 := by
  unfold tailWord_8240178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75135995585312472801452297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200362654894166594137206125 75135995585312472801452297)
  ·
    refine ⟨56351996688984354601089223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75135995585312472801452297 56351996688984354601089223)
    ·
      refine ⟨84527995033476531901633835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56351996688984354601089223 84527995033476531901633835)
      ·
        refine ⟨126791992550214797852450753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84527995033476531901633835 126791992550214797852450753)
        ·
          refine ⟨95093994412661098389338065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126791992550214797852450753 95093994412661098389338065)
          ·
            refine ⟨71320495809495823792003549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95093994412661098389338065 71320495809495823792003549)
            ·
              refine ⟨26745185928560933922001331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71320495809495823792003549 26745185928560933922001331)
              ·
                refine ⟨40117778892841400883001997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26745185928560933922001331 40117778892841400883001997)
                ·
                  refine ⟨15044167084815525331125749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40117778892841400883001997 15044167084815525331125749)
                  ·
                    refine ⟨1410390664201455499793039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15044167084815525331125749 1410390664201455499793039)
                    ·
                      rfl

theorem cell23_8240178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_8240178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240178 prefixEnd_8240178 := by exact prefixLift 8240178
  have htrace : WordTrace (prefixWord ++ tailWord_8240178) baseStart_8240178 baseEnd_8240178 := by
    simpa [prefixWord, tailWord_8240178, baseEnd_8240178] using wordTrace_append hprefix tailTrace_8240178
  have hstable : (prefixWord ++ tailWord_8240178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240178).length < 2 ^ (prefixWord ++ tailWord_8240178).sum := by decide
  have hdescent : baseEnd_8240178 < baseStart_8240178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240192 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 1, 1, 3]
def baseStart_8240192 : Nat := 118140960795 + 8240192 * 2 ^ 59
def prefixEnd_8240192 : Nat := 4983230072969 + 3 ^ 40 * 8240192 * 2
def baseEnd_8240192 : Nat := 4231179181333529444604053

theorem tailTrace_8240192 : CollatzResearch.WordTrace tailWord_8240192 prefixEnd_8240192 4231179181333529444604053 := by
  unfold tailWord_8240192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150272246481599585798409415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200362995308799447731212553 150272246481599585798409415)
  ·
    refine ⟨225408369722399378697614123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150272246481599585798409415 225408369722399378697614123)
    ·
      refine ⟨338112554583599068046421185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225408369722399378697614123 338112554583599068046421185)
      ·
        refine ⟨253584415937699301034815889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338112554583599068046421185 253584415937699301034815889)
        ·
          refine ⟨190188311953274475776111917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253584415937699301034815889 190188311953274475776111917)
          ·
            refine ⟨71320616982477928416041969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190188311953274475776111917 71320616982477928416041969)
            ·
              refine ⟨53490462736858446312031477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71320616982477928416041969 53490462736858446312031477)
              ·
                refine ⟨5014730881580479341752951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53490462736858446312031477 5014730881580479341752951)
                ·
                  refine ⟨7522096322370719012629427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014730881580479341752951 7522096322370719012629427)
                  ·
                    refine ⟨11283144483556078518944141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522096322370719012629427 11283144483556078518944141)
                    ·
                      refine ⟨4231179181333529444604053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11283144483556078518944141 4231179181333529444604053)
                      ·
                        rfl

theorem cell23_8240192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_8240192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240192 prefixEnd_8240192 := by exact prefixLift 8240192
  have htrace : WordTrace (prefixWord ++ tailWord_8240192) baseStart_8240192 baseEnd_8240192 := by
    simpa [prefixWord, tailWord_8240192, baseEnd_8240192] using wordTrace_append hprefix tailTrace_8240192
  have hstable : (prefixWord ++ tailWord_8240192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240192).length < 2 ^ (prefixWord ++ tailWord_8240192).sum := by decide
  have hdescent : baseEnd_8240192 < baseStart_8240192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240195 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 1, 5]
def baseStart_8240195 : Nat := 118140960795 + 8240195 * 2 ^ 59
def prefixEnd_8240195 : Nat := 4983230072969 + 3 ^ 40 * 8240195 * 2
def baseEnd_8240195 : Nat := 1410393573925164310955513

theorem tailTrace_8240195 : CollatzResearch.WordTrace tailWord_8240195 prefixEnd_8240195 1410393573925164310955513 := by
  unfold tailWord_8240195
  simp only [CollatzResearch.WordTrace]
  refine ⟨300544602382188303109178039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200363068254792202072785359 300544602382188303109178039)
  ·
    refine ⟨450816903573282454663767059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300544602382188303109178039 450816903573282454663767059)
    ·
      refine ⟨676225355359923681995650589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450816903573282454663767059 676225355359923681995650589)
      ·
        refine ⟨253584508259971380748368971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676225355359923681995650589 253584508259971380748368971)
        ·
          refine ⟨380376762389957071122553457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253584508259971380748368971 380376762389957071122553457)
          ·
            refine ⟨285282571792467803341915093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380376762389957071122553457 285282571792467803341915093)
            ·
              refine ⟨6686310276385964140826135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285282571792467803341915093 6686310276385964140826135)
              ·
                refine ⟨10029465414578946211239203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686310276385964140826135 10029465414578946211239203)
                ·
                  refine ⟨15044198121868419316858805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029465414578946211239203 15044198121868419316858805)
                  ·
                    refine ⟨1410393573925164310955513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15044198121868419316858805 1410393573925164310955513)
                    ·
                      rfl

theorem cell23_8240195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 5].length) (baseStart_8240195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240195 prefixEnd_8240195 := by exact prefixLift 8240195
  have htrace : WordTrace (prefixWord ++ tailWord_8240195) baseStart_8240195 baseEnd_8240195 := by
    simpa [prefixWord, tailWord_8240195, baseEnd_8240195] using wordTrace_append hprefix tailTrace_8240195
  have hstable : (prefixWord ++ tailWord_8240195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240195).length < 2 ^ (prefixWord ++ tailWord_8240195).sum := by decide
  have hdescent : baseEnd_8240195 < baseStart_8240195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240208 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_8240208 : Nat := 118140960795 + 8240208 * 2 ^ 59
def prefixEnd_8240208 : Nat := 4983230072969 + 3 ^ 40 * 8240208 * 2
def baseEnd_8240208 : Nat := 1410395799008000460667993

theorem tailTrace_8240208 : CollatzResearch.WordTrace tailWord_8240208 prefixEnd_8240208 1410395799008000460667993 := by
  unfold tailWord_8240208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150272538265570603164700639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200363384354094137552934185 150272538265570603164700639)
  ·
    refine ⟨225408807398355904747050959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150272538265570603164700639 225408807398355904747050959)
    ·
      refine ⟨338113211097533857120576439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225408807398355904747050959 338113211097533857120576439)
      ·
        refine ⟨507169816646300785680864659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338113211097533857120576439 507169816646300785680864659)
        ·
          refine ⟨760754724969451178521296989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507169816646300785680864659 760754724969451178521296989)
          ·
            refine ⟨285283021863544191945486371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760754724969451178521296989 285283021863544191945486371)
            ·
              refine ⟨427924532795316287918229557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285283021863544191945486371 427924532795316287918229557)
              ·
                refine ⟨40117924949560901992334021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427924532795316287918229557 40117924949560901992334021)
                ·
                  refine ⟨7522110928042669123562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40117924949560901992334021 7522110928042669123562629)
                  ·
                    refine ⟨1410395799008000460667993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7522110928042669123562629 1410395799008000460667993)
                    ·
                      rfl

theorem cell23_8240208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_8240208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240208 prefixEnd_8240208 := by exact prefixLift 8240208
  have htrace : WordTrace (prefixWord ++ tailWord_8240208) baseStart_8240208 baseEnd_8240208 := by
    simpa [prefixWord, tailWord_8240208, baseEnd_8240208] using wordTrace_append hprefix tailTrace_8240208
  have hstable : (prefixWord ++ tailWord_8240208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240208).length < 2 ^ (prefixWord ++ tailWord_8240208).sum := by decide
  have hdescent : baseEnd_8240208 < baseStart_8240208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240209 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_8240209 : Nat := 118140960795 + 8240209 * 2 ^ 59
def prefixEnd_8240209 : Nat := 4983230072969 + 3 ^ 40 * 8240209 * 2
def baseEnd_8240209 : Nat := 4231187910504655878091475

theorem tailTrace_8240209 : CollatzResearch.WordTrace tailWord_8240209 prefixEnd_8240209 4231187910504655878091475 := by
  unfold tailWord_8240209
  simp only [CollatzResearch.WordTrace]
  refine ⟨300545113004137583500187681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200363408669425055666791787 300545113004137583500187681)
  ·
    refine ⟨225408834753103187625140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300545113004137583500187681 225408834753103187625140761)
    ·
      refine ⟨169056626064827390718855571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225408834753103187625140761 169056626064827390718855571)
      ·
        refine ⟨253584939097241086078283357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169056626064827390718855571 253584939097241086078283357)
        ·
          refine ⟨95094352161465407279356259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253584939097241086078283357 95094352161465407279356259)
          ·
            refine ⟨142641528242198110919034389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95094352161465407279356259 142641528242198110919034389)
            ·
              refine ⟨6686321636353036449329737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142641528242198110919034389 6686321636353036449329737)
              ·
                refine ⟨5014741227264777336997303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686321636353036449329737 5014741227264777336997303)
                ·
                  refine ⟨7522111840897166005495955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014741227264777336997303 7522111840897166005495955)
                  ·
                    refine ⟨11283167761345749008243933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522111840897166005495955 11283167761345749008243933)
                    ·
                      refine ⟨4231187910504655878091475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11283167761345749008243933 4231187910504655878091475)
                      ·
                        rfl

theorem cell23_8240209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_8240209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240209 prefixEnd_8240209 := by exact prefixLift 8240209
  have htrace : WordTrace (prefixWord ++ tailWord_8240209) baseStart_8240209 baseEnd_8240209 := by
    simpa [prefixWord, tailWord_8240209, baseEnd_8240209] using wordTrace_append hprefix tailTrace_8240209
  have hstable : (prefixWord ++ tailWord_8240209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240209).length < 2 ^ (prefixWord ++ tailWord_8240209).sum := by decide
  have hdescent : baseEnd_8240209 < baseStart_8240209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240225 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_8240225 : Nat := 118140960795 + 8240225 * 2 ^ 59
def prefixEnd_8240225 : Nat := 4983230072969 + 3 ^ 40 * 8240225 * 2
def baseEnd_8240225 : Nat := 1410398708731709271830467

theorem tailTrace_8240225 : CollatzResearch.WordTrace tailWord_8240225 prefixEnd_8240225 1410398708731709271830467 := by
  unfold tailWord_8240225
  simp only [CollatzResearch.WordTrace]
  refine ⟨300545696572079618232770129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200363797714719745488513419 300545696572079618232770129)
  ·
    refine ⟨225409272429059713674577597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300545696572079618232770129 225409272429059713674577597)
    ·
      refine ⟨84528477160897392627966599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225409272429059713674577597 84528477160897392627966599)
      ·
        refine ⟨126792715741346088941949899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84528477160897392627966599 126792715741346088941949899)
        ·
          refine ⟨190189073612019133412924849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126792715741346088941949899 190189073612019133412924849)
          ·
            refine ⟨142641805209014350059693637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190189073612019133412924849 142641805209014350059693637)
            ·
              refine ⟨26745338476690190636192557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142641805209014350059693637 26745338476690190636192557)
              ·
                refine ⟨10029501928758821488572209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26745338476690190636192557 10029501928758821488572209)
                ·
                  refine ⟨7522126446569116116429157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029501928758821488572209 7522126446569116116429157)
                  ·
                    refine ⟨1410398708731709271830467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7522126446569116116429157 1410398708731709271830467)
                    ·
                      rfl

theorem cell23_8240225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_8240225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240225 prefixEnd_8240225 := by exact prefixLift 8240225
  have htrace : WordTrace (prefixWord ++ tailWord_8240225) baseStart_8240225 baseEnd_8240225 := by
    simpa [prefixWord, tailWord_8240225, baseEnd_8240225] using wordTrace_append hprefix tailTrace_8240225
  have hstable : (prefixWord ++ tailWord_8240225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240225).length < 2 ^ (prefixWord ++ tailWord_8240225).sum := by decide
  have hdescent : baseEnd_8240225 < baseStart_8240225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240249 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 1, 1, 4]
def baseStart_8240249 : Nat := 118140960795 + 8240249 * 2 ^ 59
def prefixEnd_8240249 : Nat := 4983230072969 + 3 ^ 40 * 8240249 * 2
def baseEnd_8240249 : Nat := 4231208449730835721591291

theorem tailTrace_8240249 : CollatzResearch.WordTrace tailWord_8240249 prefixEnd_8240249 4231208449730835721591291 := by
  unfold tailWord_8240249
  simp only [CollatzResearch.WordTrace]
  refine ⟨300546571923992670331643801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200364381282661780221095867 300546571923992670331643801)
  ·
    refine ⟨225409928942994502748732851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300546571923992670331643801 225409928942994502748732851)
    ·
      refine ⟨338114893414491754123099277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225409928942994502748732851 338114893414491754123099277)
      ·
        refine ⟨126793085030434407796162229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338114893414491754123099277 126793085030434407796162229)
        ·
          refine ⟨11886851721603225730890209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126793085030434407796162229 11886851721603225730890209)
          ·
            refine ⟨8915138791202419298167657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11886851721603225730890209 8915138791202419298167657)
            ·
              refine ⟨6686354093401814473625743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8915138791202419298167657 6686354093401814473625743)
              ·
                refine ⟨10029531140102721710438615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686354093401814473625743 10029531140102721710438615)
                ·
                  refine ⟨15044296710154082565657923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029531140102721710438615 15044296710154082565657923)
                  ·
                    refine ⟨22566445065231123848486885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15044296710154082565657923 22566445065231123848486885)
                    ·
                      refine ⟨4231208449730835721591291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22566445065231123848486885 4231208449730835721591291)
                      ·
                        rfl

theorem cell23_8240249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_8240249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240249 prefixEnd_8240249 := by exact prefixLift 8240249
  have htrace : WordTrace (prefixWord ++ tailWord_8240249) baseStart_8240249 baseEnd_8240249 := by
    simpa [prefixWord, tailWord_8240249, baseEnd_8240249] using wordTrace_append hprefix tailTrace_8240249
  have hstable : (prefixWord ++ tailWord_8240249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240249).length < 2 ^ (prefixWord ++ tailWord_8240249).sum := by decide
  have hdescent : baseEnd_8240249 < baseStart_8240249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240275 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 5, 3, 2]
def baseStart_8240275 : Nat := 118140960795 + 8240275 * 2 ^ 59
def prefixEnd_8240275 : Nat := 4983230072969 + 3 ^ 40 * 8240275 * 2
def baseEnd_8240275 : Nat := 4231221800227852619866171

theorem tailTrace_8240275 : CollatzResearch.WordTrace tailWord_8240275 prefixEnd_8240275 4231221800227852619866171 := by
  unfold tailWord_8240275
  simp only [CollatzResearch.WordTrace]
  refine ⟨300547520221898476772090279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200365013481265651181393519 300547520221898476772090279)
  ·
    refine ⟨450821280332847715158135419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300547520221898476772090279 450821280332847715158135419)
    ·
      refine ⟨676231920499271572737203129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450821280332847715158135419 676231920499271572737203129)
      ·
        refine ⟨507173940374453679552902347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676231920499271572737203129 507173940374453679552902347)
        ·
          refine ⟨760760910561680519329353521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507173940374453679552902347 760760910561680519329353521)
          ·
            refine ⟨570570682921260389497015141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760760910561680519329353521 570570682921260389497015141)
            ·
              refine ⟨106982003047736323030690339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570570682921260389497015141 106982003047736323030690339)
              ·
                refine ⟨160473004571604484546035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106982003047736323030690339 160473004571604484546035509)
                ·
                  refine ⟨15044344178587920426190829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160473004571604484546035509 15044344178587920426190829)
                  ·
                    refine ⟨5641629066970470159821561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15044344178587920426190829 5641629066970470159821561)
                    ·
                      refine ⟨4231221800227852619866171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641629066970470159821561 4231221800227852619866171)
                      ·
                        rfl

theorem cell23_8240275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3, 2].length) (baseStart_8240275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240275 prefixEnd_8240275 := by exact prefixLift 8240275
  have htrace : WordTrace (prefixWord ++ tailWord_8240275) baseStart_8240275 baseEnd_8240275 := by
    simpa [prefixWord, tailWord_8240275, baseEnd_8240275] using wordTrace_append hprefix tailTrace_8240275
  have hstable : (prefixWord ++ tailWord_8240275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240275).length < 2 ^ (prefixWord ++ tailWord_8240275).sum := by decide
  have hdescent : baseEnd_8240275 < baseStart_8240275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240282 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_8240282 : Nat := 118140960795 + 8240282 * 2 ^ 59
def prefixEnd_8240282 : Nat := 4983230072969 + 3 ^ 40 * 8240282 * 2
def baseEnd_8240282 : Nat := 4231225394592434092478639

theorem tailTrace_8240282 : CollatzResearch.WordTrace tailWord_8240282 prefixEnd_8240282 4231225394592434092478639 := by
  unfold tailWord_8240282
  simp only [CollatzResearch.WordTrace]
  refine ⟨75136943883218279241898775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200365183688582077978396733 75136943883218279241898775)
  ·
    refine ⟨112705415824827418862848163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75136943883218279241898775 112705415824827418862848163)
    ·
      refine ⟨169058123737241128294272245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112705415824827418862848163 169058123737241128294272245)
      ·
        refine ⟨15849199100366355777588023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169058123737241128294272245 15849199100366355777588023)
        ·
          refine ⟨23773798650549533666382035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15849199100366355777588023 23773798650549533666382035)
          ·
            refine ⟨35660697975824300499573053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23773798650549533666382035 35660697975824300499573053)
            ·
              refine ⟨13372761740934112687339895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35660697975824300499573053 13372761740934112687339895)
              ·
                refine ⟨20059142611401169031009843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13372761740934112687339895 20059142611401169031009843)
                ·
                  refine ⟨30088713917101753546514765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20059142611401169031009843 30088713917101753546514765)
                  ·
                    refine ⟨11283267718913157579943037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30088713917101753546514765 11283267718913157579943037)
                    ·
                      refine ⟨4231225394592434092478639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11283267718913157579943037 4231225394592434092478639)
                      ·
                        rfl

theorem cell23_8240282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_8240282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240282 prefixEnd_8240282 := by exact prefixLift 8240282
  have htrace : WordTrace (prefixWord ++ tailWord_8240282) baseStart_8240282 baseEnd_8240282 := by
    simpa [prefixWord, tailWord_8240282, baseEnd_8240282] using wordTrace_append hprefix tailTrace_8240282
  have hstable : (prefixWord ++ tailWord_8240282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240282).length < 2 ^ (prefixWord ++ tailWord_8240282).sum := by decide
  have hdescent : baseEnd_8240282 < baseStart_8240282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240295 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_8240295 : Nat := 118140960795 + 8240295 * 2 ^ 59
def prefixEnd_8240295 : Nat := 4983230072969 + 3 ^ 40 * 8240295 * 2
def baseEnd_8240295 : Nat := 4231232069840942541616079

theorem tailTrace_8240295 : CollatzResearch.WordTrace tailWord_8240295 prefixEnd_8240295 4231232069840942541616079 := by
  unfold tailWord_8240295
  simp only [CollatzResearch.WordTrace]
  refine ⟨300548249681826020187818339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200365499787884013458545559 300548249681826020187818339)
  ·
    refine ⟨450822374522739030281727509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300548249681826020187818339 450822374522739030281727509)
    ·
      refine ⟨21132298805753392044455977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 450822374522739030281727509 21132298805753392044455977)
      ·
        refine ⟨15849224104315044033341983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21132298805753392044455977 15849224104315044033341983)
        ·
          refine ⟨23773836156472566050012975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15849224104315044033341983 23773836156472566050012975)
          ·
            refine ⟨35660754234708849075019463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23773836156472566050012975 35660754234708849075019463)
            ·
              refine ⟨53491131352063273612529195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35660754234708849075019463 53491131352063273612529195)
              ·
                refine ⟨80236697028094910418793793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53491131352063273612529195 80236697028094910418793793)
                ·
                  refine ⟨60177522771071182814095345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80236697028094910418793793 60177522771071182814095345)
                  ·
                    refine ⟨45133142078303387110571509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60177522771071182814095345 45133142078303387110571509)
                    ·
                      refine ⟨4231232069840942541616079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45133142078303387110571509 4231232069840942541616079)
                      ·
                        rfl

theorem cell23_8240295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_8240295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240295 prefixEnd_8240295 := by exact prefixLift 8240295
  have htrace : WordTrace (prefixWord ++ tailWord_8240295) baseStart_8240295 baseEnd_8240295 := by
    simpa [prefixWord, tailWord_8240295, baseEnd_8240295] using wordTrace_append hprefix tailTrace_8240295
  have hstable : (prefixWord ++ tailWord_8240295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240295).length < 2 ^ (prefixWord ++ tailWord_8240295).sum := by decide
  have hdescent : baseEnd_8240295 < baseStart_8240295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240333 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_8240333 : Nat := 118140960795 + 8240333 * 2 ^ 59
def prefixEnd_8240333 : Nat := 4983230072969 + 3 ^ 40 * 8240333 * 2
def baseEnd_8240333 : Nat := 4231251582105813392940905

theorem tailTrace_8240333 : CollatzResearch.WordTrace tailWord_8240333 prefixEnd_8240333 4231251582105813392940905 := by
  unfold tailWord_8240333
  simp only [CollatzResearch.WordTrace]
  refine ⟨300549635655688352677701653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200366423770458901785134435 300549635655688352677701653)
  ·
    refine ⟨14088264171360391531767265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300549635655688352677701653 14088264171360391531767265)
    ·
      refine ⟨10566198128520293648825449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14088264171360391531767265 10566198128520293648825449)
      ·
        refine ⟨7924648596390220236619087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10566198128520293648825449 7924648596390220236619087)
        ·
          refine ⟨11886972894585330354928631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924648596390220236619087 11886972894585330354928631)
          ·
            refine ⟨17830459341877995532392947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886972894585330354928631 17830459341877995532392947)
            ·
              refine ⟨26745689012816993298589421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17830459341877995532392947 26745689012816993298589421)
              ·
                refine ⟨10029633379806372486971033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26745689012816993298589421 10029633379806372486971033)
                ·
                  refine ⟨7522225034854779365228275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029633379806372486971033 7522225034854779365228275)
                  ·
                    refine ⟨11283337552282169047842413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522225034854779365228275 11283337552282169047842413)
                    ·
                      refine ⟨4231251582105813392940905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11283337552282169047842413 4231251582105813392940905)
                      ·
                        rfl

theorem cell23_8240333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_8240333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240333 prefixEnd_8240333 := by exact prefixLift 8240333
  have htrace : WordTrace (prefixWord ++ tailWord_8240333) baseStart_8240333 baseEnd_8240333 := by
    simpa [prefixWord, tailWord_8240333, baseEnd_8240333] using wordTrace_append hprefix tailTrace_8240333
  have hstable : (prefixWord ++ tailWord_8240333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240333).length < 2 ^ (prefixWord ++ tailWord_8240333).sum := by decide
  have hdescent : baseEnd_8240333 < baseStart_8240333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240385 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_8240385 : Nat := 118140960795 + 8240385 * 2 ^ 59
def prefixEnd_8240385 : Nat := 4983230072969 + 3 ^ 40 * 8240385 * 2
def baseEnd_8240385 : Nat := 4231278283099847189490665

theorem tailTrace_8240385 : CollatzResearch.WordTrace tailWord_8240385 prefixEnd_8240385 4231278283099847189490665 := by
  unfold tailWord_8240385
  simp only [CollatzResearch.WordTrace]
  refine ⟨300551532251499965558594609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200367688167666643705729739 300551532251499965558594609)
  ·
    refine ⟨225413649188624974168945957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300551532251499965558594609 225413649188624974168945957)
    ·
      refine ⟨42265059222867182656677367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225413649188624974168945957 42265059222867182656677367)
      ·
        refine ⟨63397588834300773985016051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42265059222867182656677367 63397588834300773985016051)
        ·
          refine ⟨95096383251451160977524077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63397588834300773985016051 95096383251451160977524077)
          ·
            refine ⟨35661143719294185366571529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95096383251451160977524077 35661143719294185366571529)
            ·
              refine ⟨26745857789470639024928647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35661143719294185366571529 26745857789470639024928647)
              ·
                refine ⟨40118786684205958537392971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26745857789470639024928647 40118786684205958537392971)
                ·
                  refine ⟨60178180026308937806089457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40118786684205958537392971 60178180026308937806089457)
                  ·
                    refine ⟨45133635019731703354567093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60178180026308937806089457 45133635019731703354567093)
                    ·
                      refine ⟨4231278283099847189490665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45133635019731703354567093 4231278283099847189490665)
                      ·
                        rfl

theorem cell23_8240385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_8240385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240385 prefixEnd_8240385 := by exact prefixLift 8240385
  have htrace : WordTrace (prefixWord ++ tailWord_8240385) baseStart_8240385 baseEnd_8240385 := by
    simpa [prefixWord, tailWord_8240385, baseEnd_8240385] using wordTrace_append hprefix tailTrace_8240385
  have hstable : (prefixWord ++ tailWord_8240385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240385).length < 2 ^ (prefixWord ++ tailWord_8240385).sum := by decide
  have hdescent : baseEnd_8240385 < baseStart_8240385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240412 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_8240412 : Nat := 118140960795 + 8240412 * 2 ^ 59
def prefixEnd_8240412 : Nat := 4983230072969 + 3 ^ 40 * 8240412 * 2
def baseEnd_8240412 : Nat := 4231292147077518583853041

theorem tailTrace_8240412 : CollatzResearch.WordTrace tailWord_8240412 prefixEnd_8240412 4231292147077518583853041 := by
  unfold tailWord_8240412
  simp only [CollatzResearch.WordTrace]
  refine ⟨150276258511201074584913745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200368344681601432779884993 150276258511201074584913745)
  ·
    refine ⟨112707193883400805938685309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150276258511201074584913745 112707193883400805938685309)
    ·
      refine ⟨42265197706275302227006991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112707193883400805938685309 42265197706275302227006991)
      ·
        refine ⟨63397796559412953340510487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42265197706275302227006991 63397796559412953340510487)
        ·
          refine ⟨95096694839119430010765731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63397796559412953340510487 95096694839119430010765731)
          ·
            refine ⟨142645042258679145016148597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95096694839119430010765731 142645042258679145016148597)
            ·
              refine ⟨13372972711751169845263931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142645042258679145016148597 13372972711751169845263931)
              ·
                refine ⟨20059459067626754767895897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13372972711751169845263931 20059459067626754767895897)
                ·
                  refine ⟨15044594300720066075921923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20059459067626754767895897 15044594300720066075921923)
                  ·
                    refine ⟨22566891451080099113882885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15044594300720066075921923 22566891451080099113882885)
                    ·
                      refine ⟨4231292147077518583853041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22566891451080099113882885 4231292147077518583853041)
                      ·
                        rfl

theorem cell23_8240412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_8240412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240412 prefixEnd_8240412 := by exact prefixLift 8240412
  have htrace : WordTrace (prefixWord ++ tailWord_8240412) baseStart_8240412 baseEnd_8240412 := by
    simpa [prefixWord, tailWord_8240412, baseEnd_8240412] using wordTrace_append hprefix tailTrace_8240412
  have hstable : (prefixWord ++ tailWord_8240412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240412).length < 2 ^ (prefixWord ++ tailWord_8240412).sum := by decide
  have hdescent : baseEnd_8240412 < baseStart_8240412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240435 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 8]
def baseStart_8240435 : Nat := 118140960795 + 8240435 * 2 ^ 59
def prefixEnd_8240435 : Nat := 4983230072969 + 3 ^ 40 * 8240435 * 2
def baseEnd_8240435 : Nat := 470144884125841332651715

theorem tailTrace_8240435 : CollatzResearch.WordTrace tailWord_8240435 prefixEnd_8240435 470144884125841332651715 := by
  unfold tailWord_8240435
  simp only [CollatzResearch.WordTrace]
  refine ⟨300553355901318824097914759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200368903934212549398609839 300553355901318824097914759)
  ·
    refine ⟨450830033851978236146872139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300553355901318824097914759 450830033851978236146872139)
    ·
      refine ⟨676245050777967354220308209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450830033851978236146872139 676245050777967354220308209)
      ·
        refine ⟨507183788083475515665231157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676245050777967354220308209 507183788083475515665231157)
        ·
          refine ⟨47548480132825829593615421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 507183788083475515665231157 47548480132825829593615421)
          ·
            refine ⟨17830680049809686097605783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47548480132825829593615421 17830680049809686097605783)
            ·
              refine ⟨26746020074714529146408675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17830680049809686097605783 26746020074714529146408675)
              ·
                refine ⟨40119030112071793719613013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26746020074714529146408675 40119030112071793719613013)
                ·
                  refine ⟨470144884125841332651715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40119030112071793719613013 470144884125841332651715)
                  ·
                    rfl

theorem cell23_8240435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 8].length) (baseStart_8240435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240435 prefixEnd_8240435 := by exact prefixLift 8240435
  have htrace : WordTrace (prefixWord ++ tailWord_8240435) baseStart_8240435 baseEnd_8240435 := by
    simpa [prefixWord, tailWord_8240435, baseEnd_8240435] using wordTrace_append hprefix tailTrace_8240435
  have hstable : (prefixWord ++ tailWord_8240435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240435).length < 2 ^ (prefixWord ++ tailWord_8240435).sum := by decide
  have hdescent : baseEnd_8240435 < baseStart_8240435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240472 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_8240472 : Nat := 118140960795 + 8240472 * 2 ^ 59
def prefixEnd_8240472 : Nat := 4983230072969 + 3 ^ 40 * 8240472 * 2
def baseEnd_8240472 : Nat := 4231322955916788349102765

theorem tailTrace_8240472 : CollatzResearch.WordTrace tailWord_8240472 prefixEnd_8240472 4231322955916788349102765 := by
  unfold tailWord_8240472
  simp only [CollatzResearch.WordTrace]
  refine ⟨150277352701092389708505835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200369803601456519611341113 150277352701092389708505835)
  ·
    refine ⟨225416029051638584562758753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150277352701092389708505835 225416029051638584562758753)
    ·
      refine ⟨169062021788728938422069065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225416029051638584562758753 169062021788728938422069065)
      ·
        refine ⟨126796516341546703816551799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169062021788728938422069065 126796516341546703816551799)
        ·
          refine ⟨190194774512320055724827699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126796516341546703816551799 190194774512320055724827699)
          ·
            refine ⟨285292161768480083587241549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190194774512320055724827699 285292161768480083587241549)
            ·
              refine ⟨106984560663180031345215581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285292161768480083587241549 106984560663180031345215581)
              ·
                refine ⟨40119210248692511754455843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106984560663180031345215581 40119210248692511754455843)
                ·
                  refine ⟨60178815373038767631683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40119210248692511754455843 60178815373038767631683765)
                  ·
                    refine ⟨5641763941222384465470353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60178815373038767631683765 5641763941222384465470353)
                    ·
                      refine ⟨4231322955916788349102765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641763941222384465470353 4231322955916788349102765)
                      ·
                        rfl

theorem cell23_8240472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_8240472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240472 prefixEnd_8240472 := by exact prefixLift 8240472
  have htrace : WordTrace (prefixWord ++ tailWord_8240472) baseStart_8240472 baseEnd_8240472 := by
    simpa [prefixWord, tailWord_8240472, baseEnd_8240472] using wordTrace_append hprefix tailTrace_8240472
  have hstable : (prefixWord ++ tailWord_8240472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240472).length < 2 ^ (prefixWord ++ tailWord_8240472).sum := by decide
  have hdescent : baseEnd_8240472 < baseStart_8240472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240519 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_8240519 : Nat := 118140960795 + 8240519 * 2 ^ 59
def prefixEnd_8240519 : Nat := 4983230072969 + 3 ^ 40 * 8240519 * 2
def baseEnd_8240519 : Nat := 4231347089507549665215049

theorem tailTrace_8240519 : CollatzResearch.WordTrace tailWord_8240519 prefixEnd_8240519 4231347089507549665215049 := by
  unfold tailWord_8240519
  simp only [CollatzResearch.WordTrace]
  refine ⟨300556419633014506443972611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200370946422009670962648407 300556419633014506443972611)
  ·
    refine ⟨450834629449521759665958917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300556419633014506443972611 450834629449521759665958917)
    ·
      refine ⟨84531493021785329937367297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450834629449521759665958917 84531493021785329937367297)
      ·
        refine ⟨63398619766338997453025473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84531493021785329937367297 63398619766338997453025473)
        ·
          refine ⟨47548964824754248089769105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63398619766338997453025473 47548964824754248089769105)
          ·
            refine ⟨35661723618565686067326829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47548964824754248089769105 35661723618565686067326829)
            ·
              refine ⟨13373146356962132275247561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35661723618565686067326829 13373146356962132275247561)
              ·
                refine ⟨10029859767721599206435671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13373146356962132275247561 10029859767721599206435671)
                ·
                  refine ⟨15044789651582398809653507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10029859767721599206435671 15044789651582398809653507)
                  ·
                    refine ⟨22567184477373598214480261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15044789651582398809653507 22567184477373598214480261)
                    ·
                      refine ⟨4231347089507549665215049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22567184477373598214480261 4231347089507549665215049)
                      ·
                        rfl

theorem cell23_8240519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_8240519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240519 prefixEnd_8240519 := by exact prefixLift 8240519
  have htrace : WordTrace (prefixWord ++ tailWord_8240519) baseStart_8240519 baseEnd_8240519 := by
    simpa [prefixWord, tailWord_8240519, baseEnd_8240519] using wordTrace_append hprefix tailTrace_8240519
  have hstable : (prefixWord ++ tailWord_8240519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240519).length < 2 ^ (prefixWord ++ tailWord_8240519).sum := by decide
  have hdescent : baseEnd_8240519 < baseStart_8240519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240542 : List Nat := [4, 3, 1, 2, 13]
def baseStart_8240542 : Nat := 118140960795 + 8240542 * 2 ^ 59
def prefixEnd_8240542 : Nat := 4983230072969 + 3 ^ 40 * 8240542 * 2
def baseEnd_8240542 : Nat := 5804333195559126303467

theorem tailTrace_8240542 : CollatzResearch.WordTrace tailWord_8240542 prefixEnd_8240542 5804333195559126303467 := by
  unfold tailWord_8240542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37569657313991397671507485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200371505674620787581373253 37569657313991397671507485)
  ·
    refine ⟨14088621492746774126815307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37569657313991397671507485 14088621492746774126815307)
    ·
      refine ⟨21132932239120161190222961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14088621492746774126815307 21132932239120161190222961)
      ·
        refine ⟨15849699179340120892667221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21132932239120161190222961 15849699179340120892667221)
        ·
          refine ⟨5804333195559126303467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15849699179340120892667221 5804333195559126303467)
          ·
            rfl

theorem cell23_8240542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 13].length) (baseStart_8240542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240542 prefixEnd_8240542 := by exact prefixLift 8240542
  have htrace : WordTrace (prefixWord ++ tailWord_8240542) baseStart_8240542 baseEnd_8240542 := by
    simpa [prefixWord, tailWord_8240542, baseEnd_8240542] using wordTrace_append hprefix tailTrace_8240542
  have hstable : (prefixWord ++ tailWord_8240542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240542).length < 2 ^ (prefixWord ++ tailWord_8240542).sum := by decide
  have hdescent : baseEnd_8240542 < baseStart_8240542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240546 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_8240546 : Nat := 118140960795 + 8240546 * 2 ^ 59
def prefixEnd_8240546 : Nat := 4983230072969 + 3 ^ 40 * 8240546 * 2
def baseEnd_8240546 : Nat := 1410453651161740353192475

theorem tailTrace_8240546 : CollatzResearch.WordTrace tailWord_8240546 prefixEnd_8240546 1410453651161740353192475 := by
  unfold tailWord_8240546
  simp only [CollatzResearch.WordTrace]
  refine ⟨75139351100979172513801373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200371602935944460036803661 75139351100979172513801373)
  ·
    refine ⟨28177256662867189692675515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75139351100979172513801373 28177256662867189692675515)
    ·
      refine ⟨42265884994300784539013273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28177256662867189692675515 42265884994300784539013273)
      ·
        refine ⟨31699413745725588404259955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42265884994300784539013273 31699413745725588404259955)
        ·
          refine ⟨47549120618588382606389933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31699413745725588404259955 47549120618588382606389933)
          ·
            refine ⟨17830920231970643477396225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47549120618588382606389933 17830920231970643477396225)
            ·
              refine ⟨13373190173977982608047169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17830920231970643477396225 13373190173977982608047169)
              ·
                refine ⟨10029892630483486956035377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13373190173977982608047169 10029892630483486956035377)
                ·
                  refine ⟨7522419472862615217026533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029892630483486956035377 7522419472862615217026533)
                  ·
                    refine ⟨1410453651161740353192475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7522419472862615217026533 1410453651161740353192475)
                    ·
                      rfl

theorem cell23_8240546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_8240546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240546 prefixEnd_8240546 := by exact prefixLift 8240546
  have htrace : WordTrace (prefixWord ++ tailWord_8240546) baseStart_8240546 baseEnd_8240546 := by
    simpa [prefixWord, tailWord_8240546, baseEnd_8240546] using wordTrace_append hprefix tailTrace_8240546
  have hstable : (prefixWord ++ tailWord_8240546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240546).length < 2 ^ (prefixWord ++ tailWord_8240546).sum := by decide
  have hdescent : baseEnd_8240546 < baseStart_8240546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240579 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 3, 3, 2]
def baseStart_8240579 : Nat := 118140960795 + 8240579 * 2 ^ 59
def prefixEnd_8240579 : Nat := 4983230072969 + 3 ^ 40 * 8240579 * 2
def baseEnd_8240579 : Nat := 4231377898346819430464773

theorem tailTrace_8240579 : CollatzResearch.WordTrace tailWord_8240579 prefixEnd_8240579 4231377898346819430464773 := by
  unfold tailWord_8240579
  simp only [CollatzResearch.WordTrace]
  refine ⟨300558608012797136691156791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200372405341864757794104527 300558608012797136691156791)
  ·
    refine ⟨450837912019195705036735187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300558608012797136691156791 450837912019195705036735187)
    ·
      refine ⟨676256868028793557555102781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450837912019195705036735187 676256868028793557555102781)
      ·
        refine ⟨253596325510797584083163543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676256868028793557555102781 253596325510797584083163543)
        ·
          refine ⟨380394488266196376124745315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253596325510797584083163543 380394488266196376124745315)
          ·
            refine ⟨570591732399294564187117973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380394488266196376124745315 570591732399294564187117973)
            ·
              refine ⟨26746487456216932696271155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 570591732399294564187117973 26746487456216932696271155)
              ·
                refine ⟨40119731184325399044406733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26746487456216932696271155 40119731184325399044406733)
                ·
                  refine ⟨15044899194122024641652525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40119731184325399044406733 15044899194122024641652525)
                  ·
                    refine ⟨5641837197795759240619697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15044899194122024641652525 5641837197795759240619697)
                    ·
                      refine ⟨4231377898346819430464773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5641837197795759240619697 4231377898346819430464773)
                      ·
                        rfl

theorem cell23_8240579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_8240579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240579 prefixEnd_8240579 := by exact prefixLift 8240579
  have htrace : WordTrace (prefixWord ++ tailWord_8240579) baseStart_8240579 baseEnd_8240579 := by
    simpa [prefixWord, tailWord_8240579, baseEnd_8240579] using wordTrace_append hprefix tailTrace_8240579
  have hstable : (prefixWord ++ tailWord_8240579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240579).length < 2 ^ (prefixWord ++ tailWord_8240579).sum := by decide
  have hdescent : baseEnd_8240579 < baseStart_8240579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240585 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_8240585 : Nat := 118140960795 + 8240585 * 2 ^ 59
def prefixEnd_8240585 : Nat := 4983230072969 + 3 ^ 40 * 8240585 * 2
def baseEnd_8240585 : Nat := 1410460326410248802329915

theorem tailTrace_8240585 : CollatzResearch.WordTrace tailWord_8240585 prefixEnd_8240585 1410460326410248802329915 := by
  unfold tailWord_8240585
  simp only [CollatzResearch.WordTrace]
  refine ⟨300558826850775399715875209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200372551233850266477250139 300558826850775399715875209)
  ·
    refine ⟨225419120138081549786906407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300558826850775399715875209 225419120138081549786906407)
    ·
      refine ⟨338128680207122324680359611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225419120138081549786906407 338128680207122324680359611)
      ·
        refine ⟨507193020310683487020539417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338128680207122324680359611 507193020310683487020539417)
        ·
          refine ⟨380394765233012615265404563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507193020310683487020539417 380394765233012615265404563)
          ·
            refine ⟨570592147849518922898106845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380394765233012615265404563 570592147849518922898106845)
            ·
              refine ⟨213972055443569596086790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570592147849518922898106845 213972055443569596086790067)
              ·
                refine ⟨320958083165354394130185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213972055443569596086790067 320958083165354394130185101)
                ·
                  refine ⟨120359281187007897798819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320958083165354394130185101 120359281187007897798819413)
                  ·
                    refine ⟨1410460326410248802329915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120359281187007897798819413 1410460326410248802329915)
                    ·
                      rfl

theorem cell23_8240585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_8240585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240585 prefixEnd_8240585 := by exact prefixLift 8240585
  have htrace : WordTrace (prefixWord ++ tailWord_8240585) baseStart_8240585 baseEnd_8240585 := by
    simpa [prefixWord, tailWord_8240585, baseEnd_8240585] using wordTrace_append hprefix tailTrace_8240585
  have hstable : (prefixWord ++ tailWord_8240585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240585).length < 2 ^ (prefixWord ++ tailWord_8240585).sum := by decide
  have hdescent : baseEnd_8240585 < baseStart_8240585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240602 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_8240602 : Nat := 118140960795 + 8240602 * 2 ^ 59
def prefixEnd_8240602 : Nat := 4983230072969 + 3 ^ 40 * 8240602 * 2
def baseEnd_8240602 : Nat := 1410463236133957613492389

theorem tailTrace_8240602 : CollatzResearch.WordTrace tailWord_8240602 prefixEnd_8240602 1410463236133957613492389 := by
  unfold tailWord_8240602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75139861722928452904811015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200372964594475874412829373 75139861722928452904811015)
  ·
    refine ⟨112709792584392679357216523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75139861722928452904811015 112709792584392679357216523)
    ·
      refine ⟨169064688876589019035824785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112709792584392679357216523 169064688876589019035824785)
      ·
        refine ⟨126798516657441764276868589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169064688876589019035824785 126798516657441764276868589)
        ·
          refine ⟨47549443746540661603825721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126798516657441764276868589 47549443746540661603825721)
          ·
            refine ⟨35662082809905496202869291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47549443746540661603825721 35662082809905496202869291)
            ·
              refine ⟨53493124214858244304303937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35662082809905496202869291 53493124214858244304303937)
              ·
                refine ⟨40119843161143683228227953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53493124214858244304303937 40119843161143683228227953)
                ·
                  refine ⟨30089882370857762421170965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40119843161143683228227953 30089882370857762421170965)
                  ·
                    refine ⟨1410463236133957613492389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30089882370857762421170965 1410463236133957613492389)
                    ·
                      rfl

theorem cell23_8240602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_8240602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240602 prefixEnd_8240602 := by exact prefixLift 8240602
  have htrace : WordTrace (prefixWord ++ tailWord_8240602) baseStart_8240602 baseEnd_8240602 := by
    simpa [prefixWord, tailWord_8240602, baseEnd_8240602] using wordTrace_append hprefix tailTrace_8240602
  have hstable : (prefixWord ++ tailWord_8240602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240602).length < 2 ^ (prefixWord ++ tailWord_8240602).sum := by decide
  have hdescent : baseEnd_8240602 < baseStart_8240602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_8240612 : Nat := 118140960795 + 8240612 * 2 ^ 59
def prefixEnd_8240612 : Nat := 4983230072969 + 3 ^ 40 * 8240612 * 2
def baseEnd_8240612 : Nat := 4231394843208417801352121

theorem tailTrace_8240612 : CollatzResearch.WordTrace tailWord_8240612 prefixEnd_8240612 4231394843208417801352121 := by
  unfold tailWord_8240612
  simp only [CollatzResearch.WordTrace]
  refine ⟨150279905810838791663554045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200373207747785055551405393 150279905810838791663554045)
  ·
    refine ⟨56354964679064546873832767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150279905810838791663554045 56354964679064546873832767)
    ·
      refine ⟨84532447018596820310749151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56354964679064546873832767 84532447018596820310749151)
      ·
        refine ⟨126798670527895230466123727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84532447018596820310749151 126798670527895230466123727)
        ·
          refine ⟨190198005791842845699185591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126798670527895230466123727 190198005791842845699185591)
          ·
            refine ⟨285297008687764268548778387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190198005791842845699185591 285297008687764268548778387)
            ·
              refine ⟨427945513031646402823167581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285297008687764268548778387 427945513031646402823167581)
              ·
                refine ⟨160479567386867401058687843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427945513031646402823167581 160479567386867401058687843)
                ·
                  refine ⟨240719351080301101588031765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160479567386867401058687843 240719351080301101588031765)
                  ·
                    refine ⟨11283719581889114136938989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 240719351080301101588031765 11283719581889114136938989)
                    ·
                      refine ⟨4231394843208417801352121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11283719581889114136938989 4231394843208417801352121)
                      ·
                        rfl

theorem cell23_8240612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_8240612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240612 prefixEnd_8240612 := by exact prefixLift 8240612
  have htrace : WordTrace (prefixWord ++ tailWord_8240612) baseStart_8240612 baseEnd_8240612 := by
    simpa [prefixWord, tailWord_8240612, baseEnd_8240612] using wordTrace_append hprefix tailTrace_8240612
  have hstable : (prefixWord ++ tailWord_8240612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240612).length < 2 ^ (prefixWord ++ tailWord_8240612).sum := by decide
  have hdescent : baseEnd_8240612 < baseStart_8240612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240632 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 7]
def baseStart_8240632 : Nat := 118140960795 + 8240632 * 2 ^ 59
def prefixEnd_8240632 : Nat := 4983230072969 + 3 ^ 40 * 8240632 * 2
def baseEnd_8240632 : Nat := 470156123646834191455781

theorem tailTrace_8240632 : CollatzResearch.WordTrace tailWord_8240632 prefixEnd_8240632 470156123646834191455781 := by
  unfold tailWord_8240632
  simp only [CollatzResearch.WordTrace]
  refine ⟨150280270540802563371418075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200373694054403417828557433 150280270540802563371418075)
  ·
    refine ⟨225420405811203845057127113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150280270540802563371418075 225420405811203845057127113)
    ·
      refine ⟨169065304358402883792845335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225420405811203845057127113 169065304358402883792845335)
      ·
        refine ⟨253597956537604325689268003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169065304358402883792845335 253597956537604325689268003)
        ·
          refine ⟨380396934806406488533902005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253597956537604325689268003 380396934806406488533902005)
          ·
            refine ⟨35662212638100608300053313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380396934806406488533902005 35662212638100608300053313)
            ·
              refine ⟨26746659478575456225039985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35662212638100608300053313 26746659478575456225039985)
              ·
                refine ⟨20059994608931592168779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26746659478575456225039985 20059994608931592168779989)
                ·
                  refine ⟨470156123646834191455781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20059994608931592168779989 470156123646834191455781)
                  ·
                    rfl

theorem cell23_8240632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_8240632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240632 prefixEnd_8240632 := by exact prefixLift 8240632
  have htrace : WordTrace (prefixWord ++ tailWord_8240632) baseStart_8240632 baseEnd_8240632 := by
    simpa [prefixWord, tailWord_8240632, baseEnd_8240632] using wordTrace_append hprefix tailTrace_8240632
  have hstable : (prefixWord ++ tailWord_8240632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240632).length < 2 ^ (prefixWord ++ tailWord_8240632).sum := by decide
  have hdescent : baseEnd_8240632 < baseStart_8240632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240717 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 5]
def baseStart_8240717 : Nat := 118140960795 + 8240717 * 2 ^ 59
def prefixEnd_8240717 : Nat := 4983230072969 + 3 ^ 40 * 8240717 * 2
def baseEnd_8240717 : Nat := 470160973186348876726571

theorem tailTrace_8240717 : CollatzResearch.WordTrace tailWord_8240717 prefixEnd_8240717 470160973186348876726571 := by
  unfold tailWord_8240717
  simp only [CollatzResearch.WordTrace]
  refine ⟨300563641286297186259680405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200375760857531457506453603 300563641286297186259680405)
  ·
    refine ⟨14088920685295180605922519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300563641286297186259680405 14088920685295180605922519)
    ·
      refine ⟨21133381027942770908883779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14088920685295180605922519 21133381027942770908883779)
      ·
        refine ⟨31700071541914156363325669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21133381027942770908883779 31700071541914156363325669)
        ·
          refine ⟨5943763414108904318123563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31700071541914156363325669 5943763414108904318123563)
          ·
            refine ⟨8915645121163356477185345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943763414108904318123563 8915645121163356477185345)
            ·
              refine ⟨6686733840872517357889009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8915645121163356477185345 6686733840872517357889009)
              ·
                refine ⟨5015050380654388018416757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686733840872517357889009 5015050380654388018416757)
                ·
                  refine ⟨470160973186348876726571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5015050380654388018416757 470160973186348876726571)
                  ·
                    rfl

theorem cell23_8240717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_8240717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240717 prefixEnd_8240717 := by exact prefixLift 8240717
  have htrace : WordTrace (prefixWord ++ tailWord_8240717) baseStart_8240717 baseEnd_8240717 := by
    simpa [prefixWord, tailWord_8240717, baseEnd_8240717] using wordTrace_append hprefix tailTrace_8240717
  have hstable : (prefixWord ++ tailWord_8240717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240717).length < 2 ^ (prefixWord ++ tailWord_8240717).sum := by decide
  have hdescent : baseEnd_8240717 < baseStart_8240717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240739 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 6]
def baseStart_8240739 : Nat := 118140960795 + 8240739 * 2 ^ 59
def prefixEnd_8240739 : Nat := 4983230072969 + 3 ^ 40 * 8240739 * 2
def baseEnd_8240739 : Nat := 470162228361282089384893

theorem tailTrace_8240739 : CollatzResearch.WordTrace tailWord_8240739 prefixEnd_8240739 470162228361282089384893 := by
  unfold tailWord_8240739
  simp only [CollatzResearch.WordTrace]
  refine ⟨300564443692217484016981271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200376295794811656011320847 300564443692217484016981271)
  ·
    refine ⟨450846665538326226025471907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300564443692217484016981271 450846665538326226025471907)
    ·
      refine ⟨676269998307489339038207861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450846665538326226025471907 676269998307489339038207861)
      ·
        refine ⟨63400312341327125534831987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 676269998307489339038207861 63400312341327125534831987)
        ·
          refine ⟨95100468511990688302247981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63400312341327125534831987 95100468511990688302247981)
          ·
            refine ⟨35662675691996508113342993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95100468511990688302247981 35662675691996508113342993)
            ·
              refine ⟨26747006768997381085007245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35662675691996508113342993 26747006768997381085007245)
              ·
                refine ⟨10030127538374017906877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26747006768997381085007245 10030127538374017906877717)
                ·
                  refine ⟨470162228361282089384893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10030127538374017906877717 470162228361282089384893)
                  ·
                    rfl

theorem cell23_8240739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 6].length) (baseStart_8240739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240739 prefixEnd_8240739 := by exact prefixLift 8240739
  have htrace : WordTrace (prefixWord ++ tailWord_8240739) baseStart_8240739 baseEnd_8240739 := by
    simpa [prefixWord, tailWord_8240739, baseEnd_8240739] using wordTrace_append hprefix tailTrace_8240739
  have hstable : (prefixWord ++ tailWord_8240739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240739).length < 2 ^ (prefixWord ++ tailWord_8240739).sum := by decide
  have hdescent : baseEnd_8240739 < baseStart_8240739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240750 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_8240750 : Nat := 118140960795 + 8240750 * 2 ^ 59
def prefixEnd_8240750 : Nat := 4983230072969 + 3 ^ 40 * 8240750 * 2
def baseEnd_8240750 : Nat := 4231465703538738261426487

theorem tailTrace_8240750 : CollatzResearch.WordTrace tailWord_8240750 prefixEnd_8240750 4231465703538738261426487 := by
  unfold tailWord_8240750
  simp only [CollatzResearch.WordTrace]
  refine ⟨37570605611897204111953963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200376563263451755263754469 37570605611897204111953963)
  ·
    refine ⟨56355908417845806167930945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37570605611897204111953963 56355908417845806167930945)
    ·
      refine ⟨42266931313384354625948209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56355908417845806167930945 42266931313384354625948209)
      ·
        refine ⟨31700198485038265969461157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42266931313384354625948209 31700198485038265969461157)
        ·
          refine ⟨5943787215944674869273967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31700198485038265969461157 5943787215944674869273967)
          ·
            refine ⟨8915680823917012303910951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943787215944674869273967 8915680823917012303910951)
            ·
              refine ⟨13373521235875518455866427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915680823917012303910951 13373521235875518455866427)
              ·
                refine ⟨20060281853813277683799641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13373521235875518455866427 20060281853813277683799641)
                ·
                  refine ⟨15045211390359958262849731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20060281853813277683799641 15045211390359958262849731)
                  ·
                    refine ⟨22567817085539937394274597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15045211390359958262849731 22567817085539937394274597)
                    ·
                      refine ⟨4231465703538738261426487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22567817085539937394274597 4231465703538738261426487)
                      ·
                        rfl

theorem cell23_8240750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_8240750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240750 prefixEnd_8240750 := by exact prefixLift 8240750
  have htrace : WordTrace (prefixWord ++ tailWord_8240750) baseStart_8240750 baseEnd_8240750 := by
    simpa [prefixWord, tailWord_8240750, baseEnd_8240750] using wordTrace_append hprefix tailTrace_8240750
  have hstable : (prefixWord ++ tailWord_8240750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240750).length < 2 ^ (prefixWord ++ tailWord_8240750).sum := by decide
  have hdescent : baseEnd_8240750 < baseStart_8240750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240789 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_8240789 : Nat := 118140960795 + 8240789 * 2 ^ 59
def prefixEnd_8240789 : Nat := 4983230072969 + 3 ^ 40 * 8240789 * 2
def baseEnd_8240789 : Nat := 4231485729284263608838807

theorem tailTrace_8240789 : CollatzResearch.WordTrace tailWord_8240789 prefixEnd_8240789 4231485729284263608838807 := by
  unfold tailWord_8240789
  simp only [CollatzResearch.WordTrace]
  refine ⟨300566267342036342556301421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200377511561357561704200947 300566267342036342556301421)
  ·
    refine ⟨112712350253263628458613033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300566267342036342556301421 112712350253263628458613033)
    ·
      refine ⟨84534262689947721343959775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112712350253263628458613033 84534262689947721343959775)
      ·
        refine ⟨126801394034921582015939663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84534262689947721343959775 126801394034921582015939663)
        ·
          refine ⟨190202091052382373023909495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126801394034921582015939663 190202091052382373023909495)
          ·
            refine ⟨285303136578573559535864243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190202091052382373023909495 285303136578573559535864243)
            ·
              refine ⟨427954704867860339303796365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285303136578573559535864243 427954704867860339303796365)
              ·
                refine ⟨160483014325447627238923637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427954704867860339303796365 160483014325447627238923637)
                ·
                  refine ⟨15045282593010715053649091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160483014325447627238923637 15045282593010715053649091)
                  ·
                    refine ⟨22567923889516072580473637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15045282593010715053649091 22567923889516072580473637)
                    ·
                      refine ⟨4231485729284263608838807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22567923889516072580473637 4231485729284263608838807)
                      ·
                        rfl

theorem cell23_8240789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_8240789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240789 prefixEnd_8240789 := by exact prefixLift 8240789
  have htrace : WordTrace (prefixWord ++ tailWord_8240789) baseStart_8240789 baseEnd_8240789 := by
    simpa [prefixWord, tailWord_8240789, baseEnd_8240789] using wordTrace_append hprefix tailTrace_8240789
  have hstable : (prefixWord ++ tailWord_8240789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240789).length < 2 ^ (prefixWord ++ tailWord_8240789).sum := by decide
  have hdescent : baseEnd_8240789 < baseStart_8240789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240819 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_8240819 : Nat := 118140960795 + 8240819 * 2 ^ 59
def prefixEnd_8240819 : Nat := 4983230072969 + 3 ^ 40 * 8240819 * 2
def baseEnd_8240819 : Nat := 4231501133703898491463669

theorem tailTrace_8240819 : CollatzResearch.WordTrace tailWord_8240819 prefixEnd_8240819 4231501133703898491463669 := by
  unfold tailWord_8240819
  simp only [CollatzResearch.WordTrace]
  refine ⟨300567361531927657679893511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200378241021285105119929007 300567361531927657679893511)
  ·
    refine ⟨450851042297891486519840267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300567361531927657679893511 450851042297891486519840267)
    ·
      refine ⟨676276563446837229779760401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450851042297891486519840267 676276563446837229779760401)
      ·
        refine ⟨507207422585127922334820301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676276563446837229779760401 507207422585127922334820301)
        ·
          refine ⟨190202783469422970875557613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507207422585127922334820301 190202783469422970875557613)
          ·
            refine ⟨71326043801033614078334105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190202783469422970875557613 71326043801033614078334105)
            ·
              refine ⟨53494532850775210558750579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71326043801033614078334105 53494532850775210558750579)
              ·
                refine ⟨80241799276162815838125869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53494532850775210558750579 80241799276162815838125869)
                ·
                  refine ⟨30090674728561055939297201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80241799276162815838125869 30090674728561055939297201)
                  ·
                    refine ⟨22568006046420791954472901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30090674728561055939297201 22568006046420791954472901)
                    ·
                      refine ⟨4231501133703898491463669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22568006046420791954472901 4231501133703898491463669)
                      ·
                        rfl

theorem cell23_8240819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_8240819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240819 prefixEnd_8240819 := by exact prefixLift 8240819
  have htrace : WordTrace (prefixWord ++ tailWord_8240819) baseStart_8240819 baseEnd_8240819 := by
    simpa [prefixWord, tailWord_8240819, baseEnd_8240819] using wordTrace_append hprefix tailTrace_8240819
  have hstable : (prefixWord ++ tailWord_8240819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240819).length < 2 ^ (prefixWord ++ tailWord_8240819).sum := by decide
  have hdescent : baseEnd_8240819 < baseStart_8240819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240826 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_8240826 : Nat := 118140960795 + 8240826 * 2 ^ 59
def prefixEnd_8240826 : Nat := 4983230072969 + 3 ^ 40 * 8240826 * 2
def baseEnd_8240826 : Nat := 4231504728068479964076137

theorem tailTrace_8240826 : CollatzResearch.WordTrace tailWord_8240826 prefixEnd_8240826 4231504728068479964076137 := by
  unfold tailWord_8240826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75141904210725574468849583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200378411228601531916932221 75141904210725574468849583)
  ·
    refine ⟨112712856316088361703274375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75141904210725574468849583 112712856316088361703274375)
    ·
      refine ⟨169069284474132542554911563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112712856316088361703274375 169069284474132542554911563)
      ·
        refine ⟨253603926711198813832367345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169069284474132542554911563 253603926711198813832367345)
        ·
          refine ⟨190202945033399110374275509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253603926711198813832367345 190202945033399110374275509)
          ·
            refine ⟨17831526096881166597588329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190202945033399110374275509 17831526096881166597588329)
            ·
              refine ⟨13373644572660874948191247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17831526096881166597588329 13373644572660874948191247)
              ·
                refine ⟨20060466858991312422286871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13373644572660874948191247 20060466858991312422286871)
                ·
                  refine ⟨30090700288486968633430307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20060466858991312422286871 30090700288486968633430307)
                  ·
                    refine ⟨45136050432730452950145461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30090700288486968633430307 45136050432730452950145461)
                    ·
                      refine ⟨4231504728068479964076137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45136050432730452950145461 4231504728068479964076137)
                      ·
                        rfl

theorem cell23_8240826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_8240826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240826 prefixEnd_8240826 := by exact prefixLift 8240826
  have htrace : WordTrace (prefixWord ++ tailWord_8240826) baseStart_8240826 baseEnd_8240826 := by
    simpa [prefixWord, tailWord_8240826, baseEnd_8240826] using wordTrace_append hprefix tailTrace_8240826
  have hstable : (prefixWord ++ tailWord_8240826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240826).length < 2 ^ (prefixWord ++ tailWord_8240826).sum := by decide
  have hdescent : baseEnd_8240826 < baseStart_8240826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240850 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_8240850 : Nat := 118140960795 + 8240850 * 2 ^ 59
def prefixEnd_8240850 : Nat := 4983230072969 + 3 ^ 40 * 8240850 * 2
def baseEnd_8240850 : Nat := 1410505683868062623392009

theorem tailTrace_8240850 : CollatzResearch.WordTrace tailWord_8240850 prefixEnd_8240850 1410505683868062623392009 := by
  unfold tailWord_8240850
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142123048703837493568001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200378994796543566649514669 75142123048703837493568001)
  ·
    refine ⟨56356592286527878120176001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75142123048703837493568001 56356592286527878120176001)
    ·
      refine ⟨42267444214895908590132001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56356592286527878120176001 42267444214895908590132001)
      ·
        refine ⟨31700583161171931442599001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42267444214895908590132001 31700583161171931442599001)
        ·
          refine ⟨23775437370878948581949251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31700583161171931442599001 23775437370878948581949251)
          ·
            refine ⟨35663156056318422872923877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23775437370878948581949251 35663156056318422872923877)
            ·
              refine ⟨6686841760559704288673227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35663156056318422872923877 6686841760559704288673227)
              ·
                refine ⟨10030262640839556433009841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686841760559704288673227 10030262640839556433009841)
                ·
                  refine ⟨7522696980629667324757381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10030262640839556433009841 7522696980629667324757381)
                  ·
                    refine ⟨1410505683868062623392009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7522696980629667324757381 1410505683868062623392009)
                    ·
                      rfl

theorem cell23_8240850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_8240850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240850 prefixEnd_8240850 := by exact prefixLift 8240850
  have htrace : WordTrace (prefixWord ++ tailWord_8240850) baseStart_8240850 baseEnd_8240850 := by
    simpa [prefixWord, tailWord_8240850, baseEnd_8240850] using wordTrace_append hprefix tailTrace_8240850
  have hstable : (prefixWord ++ tailWord_8240850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240850).length < 2 ^ (prefixWord ++ tailWord_8240850).sum := by decide
  have hdescent : baseEnd_8240850 < baseStart_8240850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240854 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_8240854 : Nat := 118140960795 + 8240854 * 2 ^ 59
def prefixEnd_8240854 : Nat := 4983230072969 + 3 ^ 40 * 8240854 * 2
def baseEnd_8240854 : Nat := 1410506368508935284842003

theorem tailTrace_8240854 : CollatzResearch.WordTrace tailWord_8240854 prefixEnd_8240854 1410506368508935284842003 := by
  unfold tailWord_8240854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785539880425053666088601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200379092057867239104945077 18785539880425053666088601)
  ·
    refine ⟨14089154910318790249566451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18785539880425053666088601 14089154910318790249566451)
    ·
      refine ⟨21133732365478185374349677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14089154910318790249566451 21133732365478185374349677)
      ·
        refine ⟨7925149637054319515381129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21133732365478185374349677 7925149637054319515381129)
        ·
          refine ⟨5943862227790739636535847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7925149637054319515381129 5943862227790739636535847)
          ·
            refine ⟨8915793341686109454803771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943862227790739636535847 8915793341686109454803771)
            ·
              refine ⟨13373690012529164182205657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915793341686109454803771 13373690012529164182205657)
              ·
                refine ⟨10030267509396873136654243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13373690012529164182205657 10030267509396873136654243)
                ·
                  refine ⟨15045401264095309704981365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030267509396873136654243 15045401264095309704981365)
                  ·
                    refine ⟨1410506368508935284842003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15045401264095309704981365 1410506368508935284842003)
                    ·
                      rfl

theorem cell23_8240854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_8240854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240854 prefixEnd_8240854 := by exact prefixLift 8240854
  have htrace : WordTrace (prefixWord ++ tailWord_8240854) baseStart_8240854 baseEnd_8240854 := by
    simpa [prefixWord, tailWord_8240854, baseEnd_8240854] using wordTrace_append hprefix tailTrace_8240854
  have hstable : (prefixWord ++ tailWord_8240854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240854).length < 2 ^ (prefixWord ++ tailWord_8240854).sum := by decide
  have hdescent : baseEnd_8240854 < baseStart_8240854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240856 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_8240856 : Nat := 118140960795 + 8240856 * 2 ^ 59
def prefixEnd_8240856 : Nat := 4983230072969 + 3 ^ 40 * 8240856 * 2
def baseEnd_8240856 : Nat := 4231520132488114846700999

theorem tailTrace_8240856 : CollatzResearch.WordTrace tailWord_8240856 prefixEnd_8240856 4231520132488114846700999 := by
  unfold tailWord_8240856
  simp only [CollatzResearch.WordTrace]
  refine ⟨150284355516396806499495211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200379140688529075332660281 150284355516396806499495211)
  ·
    refine ⟨225426533274595209749242817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150284355516396806499495211 225426533274595209749242817)
    ·
      refine ⟨169069899955946407311932113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225426533274595209749242817 169069899955946407311932113)
      ·
        refine ⟨126802424966959805483949085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169069899955946407311932113 126802424966959805483949085)
        ·
          refine ⟨47550909362609927056480907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126802424966959805483949085 47550909362609927056480907)
          ·
            refine ⟨71326364043914890584721361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47550909362609927056480907 71326364043914890584721361)
            ·
              refine ⟨53494773032936167938541021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71326364043914890584721361 53494773032936167938541021)
              ·
                refine ⟨20060539887351062976952883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53494773032936167938541021 20060539887351062976952883)
                ·
                  refine ⟨30090809831026594465429325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20060539887351062976952883 30090809831026594465429325)
                  ·
                    refine ⟨11284053686634972924535997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30090809831026594465429325 11284053686634972924535997)
                    ·
                      refine ⟨4231520132488114846700999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11284053686634972924535997 4231520132488114846700999)
                      ·
                        rfl

theorem cell23_8240856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_8240856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240856 prefixEnd_8240856 := by exact prefixLift 8240856
  have htrace : WordTrace (prefixWord ++ tailWord_8240856) baseStart_8240856 baseEnd_8240856 := by
    simpa [prefixWord, tailWord_8240856, baseEnd_8240856] using wordTrace_append hprefix tailTrace_8240856
  have hstable : (prefixWord ++ tailWord_8240856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240856).length < 2 ^ (prefixWord ++ tailWord_8240856).sum := by decide
  have hdescent : baseEnd_8240856 < baseStart_8240856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240860 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_8240860 : Nat := 118140960795 + 8240860 * 2 ^ 59
def prefixEnd_8240860 : Nat := 4983230072969 + 3 ^ 40 * 8240860 * 2
def baseEnd_8240860 : Nat := 4231522186410732831050981

theorem tailTrace_8240860 : CollatzResearch.WordTrace tailWord_8240860 prefixEnd_8240860 4231522186410732831050981 := by
  unfold tailWord_8240860
  simp only [CollatzResearch.WordTrace]
  refine ⟨150284428462389560841068017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200379237949852747788090689 150284428462389560841068017)
  ·
    refine ⟨112713321346792170630801013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150284428462389560841068017 112713321346792170630801013)
    ·
      refine ⟨10566873876261765996637595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112713321346792170630801013 10566873876261765996637595)
      ·
        refine ⟨15850310814392648994956393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566873876261765996637595 15850310814392648994956393)
        ·
          refine ⟨11887733110794486746217295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850310814392648994956393 11887733110794486746217295)
          ·
            refine ⟨17831599666191730119325943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887733110794486746217295 17831599666191730119325943)
            ·
              refine ⟨26747399499287595178988915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17831599666191730119325943 26747399499287595178988915)
              ·
                refine ⟨40121099248931392768483373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26747399499287595178988915 40121099248931392768483373)
                ·
                  refine ⟨15045412218349272288181265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40121099248931392768483373 15045412218349272288181265)
                  ·
                    refine ⟨11284059163761954216135949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15045412218349272288181265 11284059163761954216135949)
                    ·
                      refine ⟨4231522186410732831050981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11284059163761954216135949 4231522186410732831050981)
                      ·
                        rfl

theorem cell23_8240860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_8240860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240860 prefixEnd_8240860 := by exact prefixLift 8240860
  have htrace : WordTrace (prefixWord ++ tailWord_8240860) baseStart_8240860 baseEnd_8240860 := by
    simpa [prefixWord, tailWord_8240860, baseEnd_8240860] using wordTrace_append hprefix tailTrace_8240860
  have hstable : (prefixWord ++ tailWord_8240860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240860).length < 2 ^ (prefixWord ++ tailWord_8240860).sum := by decide
  have hdescent : baseEnd_8240860 < baseStart_8240860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240883 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 1, 3, 2]
def baseStart_8240883 : Nat := 118140960795 + 8240883 * 2 ^ 59
def prefixEnd_8240883 : Nat := 4983230072969 + 3 ^ 40 * 8240883 * 2
def baseEnd_8240883 : Nat := 4231533996465786241063375

theorem tailTrace_8240883 : CollatzResearch.WordTrace tailWord_8240883 prefixEnd_8240883 4231533996465786241063375 := by
  unfold tailWord_8240883
  simp only [CollatzResearch.WordTrace]
  refine ⟨300569695803695796610223303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200379797202463864406815535 300569695803695796610223303)
  ·
    refine ⟨450854543705543694915334955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300569695803695796610223303 450854543705543694915334955)
    ·
      refine ⟨676281815558315542373002433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450854543705543694915334955 676281815558315542373002433)
      ·
        refine ⟨507211361668736656779751825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676281815558315542373002433 507211361668736656779751825)
        ·
          refine ⟨380408521251552492584813869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507211361668736656779751825 380408521251552492584813869)
          ·
            refine ⟨142653195469332184719305201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380408521251552492584813869 142653195469332184719305201)
            ·
              refine ⟨106989896601999138539478901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142653195469332184719305201 106989896601999138539478901)
              ·
                refine ⟨10030302806437419238076147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106989896601999138539478901 10030302806437419238076147)
                ·
                  refine ⟨15045454209656128857114221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030302806437419238076147 15045454209656128857114221)
                  ·
                    refine ⟨5642045328621048321417833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15045454209656128857114221 5642045328621048321417833)
                    ·
                      refine ⟨4231533996465786241063375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642045328621048321417833 4231533996465786241063375)
                      ·
                        rfl

theorem cell23_8240883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3, 2].length) (baseStart_8240883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240883 prefixEnd_8240883 := by exact prefixLift 8240883
  have htrace : WordTrace (prefixWord ++ tailWord_8240883) baseStart_8240883 baseEnd_8240883 := by
    simpa [prefixWord, tailWord_8240883, baseEnd_8240883] using wordTrace_append hprefix tailTrace_8240883
  have hstable : (prefixWord ++ tailWord_8240883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240883).length < 2 ^ (prefixWord ++ tailWord_8240883).sum := by decide
  have hdescent : baseEnd_8240883 < baseStart_8240883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240899 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_8240899 : Nat := 118140960795 + 8240899 * 2 ^ 59
def prefixEnd_8240899 : Nat := 4983230072969 + 3 ^ 40 * 8240899 * 2
def baseEnd_8240899 : Nat := 4231542212156258178463301

theorem tailTrace_8240899 : CollatzResearch.WordTrace tailWord_8240899 prefixEnd_8240899 4231542212156258178463301 := by
  unfold tailWord_8240899
  simp only [CollatzResearch.WordTrace]
  refine ⟨300570279371637831342805751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200380186247758554228537167 300570279371637831342805751)
  ·
    refine ⟨450855419057456747014208627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300570279371637831342805751 450855419057456747014208627)
    ·
      refine ⟨676283128586185120521312941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450855419057456747014208627 676283128586185120521312941)
      ·
        refine ⟨253606173219819420195492353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676283128586185120521312941 253606173219819420195492353)
        ·
          refine ⟨190204629914864565146619265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253606173219819420195492353 190204629914864565146619265)
          ·
            refine ⟨142653472436148423859964449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190204629914864565146619265 142653472436148423859964449)
            ·
              refine ⟨106990104327111317894973337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142653472436148423859964449 106990104327111317894973337)
              ·
                refine ⟨80242578245333488421230003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106990104327111317894973337 80242578245333488421230003)
                ·
                  refine ⟨120363867368000232631845005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80242578245333488421230003 120363867368000232631845005)
                  ·
                    refine ⟨45136450263000087236941877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120363867368000232631845005 45136450263000087236941877)
                    ·
                      refine ⟨4231542212156258178463301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45136450263000087236941877 4231542212156258178463301)
                      ·
                        rfl

theorem cell23_8240899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_8240899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240899 prefixEnd_8240899 := by exact prefixLift 8240899
  have htrace : WordTrace (prefixWord ++ tailWord_8240899) baseStart_8240899 baseEnd_8240899 := by
    simpa [prefixWord, tailWord_8240899, baseEnd_8240899] using wordTrace_append hprefix tailTrace_8240899
  have hstable : (prefixWord ++ tailWord_8240899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240899).length < 2 ^ (prefixWord ++ tailWord_8240899).sum := by decide
  have hdescent : baseEnd_8240899 < baseStart_8240899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240906 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_8240906 : Nat := 118140960795 + 8240906 * 2 ^ 59
def prefixEnd_8240906 : Nat := 4983230072969 + 3 ^ 40 * 8240906 * 2
def baseEnd_8240906 : Nat := 1410515268840279883691923

theorem tailTrace_8240906 : CollatzResearch.WordTrace tailWord_8240906 prefixEnd_8240906 1410515268840279883691923 := by
  unfold tailWord_8240906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142633670653117884577643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200380356455074981025540381 75142633670653117884577643)
  ·
    refine ⟨112713950505979676826866465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75142633670653117884577643 112713950505979676826866465)
    ·
      refine ⟨84535462879484757620149849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112713950505979676826866465 84535462879484757620149849)
      ·
        refine ⟨63401597159613568215112387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84535462879484757620149849 63401597159613568215112387)
        ·
          refine ⟨95102395739420352322668581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63401597159613568215112387 95102395739420352322668581)
          ·
            refine ⟨17831699201141316060500359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95102395739420352322668581 17831699201141316060500359)
            ·
              refine ⟨26747548801711974090750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17831699201141316060500359 26747548801711974090750539)
              ·
                refine ⟨40121323202567961136125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26747548801711974090750539 40121323202567961136125809)
                ·
                  refine ⟨30090992401925970852094357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40121323202567961136125809 30090992401925970852094357)
                  ·
                    refine ⟨1410515268840279883691923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30090992401925970852094357 1410515268840279883691923)
                    ·
                      rfl

theorem cell23_8240906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_8240906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240906 prefixEnd_8240906 := by exact prefixLift 8240906
  have htrace : WordTrace (prefixWord ++ tailWord_8240906) baseStart_8240906 baseEnd_8240906 := by
    simpa [prefixWord, tailWord_8240906, baseEnd_8240906] using wordTrace_append hprefix tailTrace_8240906
  have hstable : (prefixWord ++ tailWord_8240906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240906).length < 2 ^ (prefixWord ++ tailWord_8240906).sum := by decide
  have hdescent : baseEnd_8240906 < baseStart_8240906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240913 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_8240913 : Nat := 118140960795 + 8240913 * 2 ^ 59
def prefixEnd_8240913 : Nat := 4983230072969 + 3 ^ 40 * 8240913 * 2
def baseEnd_8240913 : Nat := 4231549400885421123688237

theorem tailTrace_8240913 : CollatzResearch.WordTrace tailWord_8240913 prefixEnd_8240913 4231549400885421123688237 := by
  unfold tailWord_8240913
  simp only [CollatzResearch.WordTrace]
  refine ⟨300570789993587111733815393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200380526662391407822543595 300570789993587111733815393)
  ·
    refine ⟨225428092495190333800361545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300570789993587111733815393 225428092495190333800361545)
    ·
      refine ⟨169071069371392750350271159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225428092495190333800361545 169071069371392750350271159)
      ·
        refine ⟨253606604057089125525406739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169071069371392750350271159 253606604057089125525406739)
        ·
          refine ⟨380409906085633688288110109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253606604057089125525406739 380409906085633688288110109)
          ·
            refine ⟨142653714782112633108041291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380409906085633688288110109 142653714782112633108041291)
            ·
              refine ⟨213980572173168949662061937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142653714782112633108041291 213980572173168949662061937)
              ·
                refine ⟨160485429129876712246546453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213980572173168949662061937 160485429129876712246546453)
                ·
                  refine ⟨7522754490462970886556865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160485429129876712246546453 7522754490462970886556865)
                  ·
                    refine ⟨5642065867847228164917649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7522754490462970886556865 5642065867847228164917649)
                    ·
                      refine ⟨4231549400885421123688237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642065867847228164917649 4231549400885421123688237)
                      ·
                        rfl

theorem cell23_8240913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_8240913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240913 prefixEnd_8240913 := by exact prefixLift 8240913
  have htrace : WordTrace (prefixWord ++ tailWord_8240913) baseStart_8240913 baseEnd_8240913 := by
    simpa [prefixWord, tailWord_8240913, baseEnd_8240913] using wordTrace_append hprefix tailTrace_8240913
  have hstable : (prefixWord ++ tailWord_8240913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240913).length < 2 ^ (prefixWord ++ tailWord_8240913).sum := by decide
  have hdescent : baseEnd_8240913 < baseStart_8240913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240930 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_8240930 : Nat := 118140960795 + 8240930 * 2 ^ 59
def prefixEnd_8240930 : Nat := 4983230072969 + 3 ^ 40 * 8240930 * 2
def baseEnd_8240930 : Nat := 4231558130056547557175659

theorem tailTrace_8240930 : CollatzResearch.WordTrace tailWord_8240930 prefixEnd_8240930 4231558130056547557175659 := by
  unfold tailWord_8240930
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142852508631380909296061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200380940023017015758122829 75142852508631380909296061)
  ·
    refine ⟨28178569690736767840986023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75142852508631380909296061 28178569690736767840986023)
    ·
      refine ⟨42267854536105151761479035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28178569690736767840986023 42267854536105151761479035)
      ·
        refine ⟨63401781804157727642218553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42267854536105151761479035 63401781804157727642218553)
        ·
          refine ⟨47551336353118295731663915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63401781804157727642218553 47551336353118295731663915)
          ·
            refine ⟨71327004529677443597495873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47551336353118295731663915 71327004529677443597495873)
            ·
              refine ⟨53495253397258082698121905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71327004529677443597495873 53495253397258082698121905)
              ·
                refine ⟨40121440047943562023591429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53495253397258082698121905 40121440047943562023591429)
                ·
                  refine ⟨7522770008989417879423393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40121440047943562023591429 7522770008989417879423393)
                  ·
                    refine ⟨5642077506742063409567545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7522770008989417879423393 5642077506742063409567545)
                    ·
                      refine ⟨4231558130056547557175659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642077506742063409567545 4231558130056547557175659)
                      ·
                        rfl

theorem cell23_8240930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_8240930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240930 prefixEnd_8240930 := by exact prefixLift 8240930
  have htrace : WordTrace (prefixWord ++ tailWord_8240930) baseStart_8240930 baseEnd_8240930 := by
    simpa [prefixWord, tailWord_8240930, baseEnd_8240930] using wordTrace_append hprefix tailTrace_8240930
  have hstable : (prefixWord ++ tailWord_8240930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240930).length < 2 ^ (prefixWord ++ tailWord_8240930).sum := by decide
  have hdescent : baseEnd_8240930 < baseStart_8240930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240986 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_8240986 : Nat := 118140960795 + 8240986 * 2 ^ 59
def prefixEnd_8240986 : Nat := 4983230072969 + 3 ^ 40 * 8240986 * 2
def baseEnd_8240986 : Nat := 4231586884973199338075401

theorem tailTrace_8240986 : CollatzResearch.WordTrace tailWord_8240986 prefixEnd_8240986 4231586884973199338075401 := by
  unfold tailWord_8240986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75143363130580661300305703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200382301681548430134148541 75143363130580661300305703)
  ·
    refine ⟨112715044695870991950458555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75143363130580661300305703 112715044695870991950458555)
    ·
      refine ⟨169072567043806487925687833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112715044695870991950458555 169072567043806487925687833)
      ·
        refine ⟨126804425282854865944265875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169072567043806487925687833 126804425282854865944265875)
        ·
          refine ⟨190206637924282298916398813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126804425282854865944265875 190206637924282298916398813)
          ·
            refine ⟨71327489221605862093649555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190206637924282298916398813 71327489221605862093649555)
            ·
              refine ⟨106991233832408793140474333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71327489221605862093649555 106991233832408793140474333)
              ·
                refine ⟨40121712687153297427677875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106991233832408793140474333 40121712687153297427677875)
                ·
                  refine ⟨60182569030729946141516813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40121712687153297427677875 60182569030729946141516813)
                  ·
                    refine ⟨22568463386523729803068805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60182569030729946141516813 22568463386523729803068805)
                    ·
                      refine ⟨4231586884973199338075401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22568463386523729803068805 4231586884973199338075401)
                      ·
                        rfl

theorem cell23_8240986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_8240986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8240986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8240986 prefixEnd_8240986 := by exact prefixLift 8240986
  have htrace : WordTrace (prefixWord ++ tailWord_8240986) baseStart_8240986 baseEnd_8240986 := by
    simpa [prefixWord, tailWord_8240986, baseEnd_8240986] using wordTrace_append hprefix tailTrace_8240986
  have hstable : (prefixWord ++ tailWord_8240986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240986).length < 2 ^ (prefixWord ++ tailWord_8240986).sum := by decide
  have hdescent : baseEnd_8240986 < baseStart_8240986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241073 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_8241073 : Nat := 118140960795 + 8241073 * 2 ^ 59
def prefixEnd_8241073 : Nat := 4983230072969 + 3 ^ 40 * 8241073 * 2
def baseEnd_8241073 : Nat := 1410543852596713499229167

theorem tailTrace_8241073 : CollatzResearch.WordTrace tailWord_8241073 prefixEnd_8241073 1410543852596713499229167 := by
  unfold tailWord_8241073
  simp only [CollatzResearch.WordTrace]
  refine ⟨300576625673007459059639873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200384417115338306039759915 300576625673007459059639873)
  ·
    refine ⟨225432469254755594294729905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300576625673007459059639873 225432469254755594294729905)
    ·
      refine ⟨169074351941066695721047429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225432469254755594294729905 169074351941066695721047429)
      ·
        refine ⟨31701440988950005447696393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169074351941066695721047429 31701440988950005447696393)
        ·
          refine ⟨23776080741712504085772295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31701440988950005447696393 23776080741712504085772295)
          ·
            refine ⟨35664121112568756128658443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23776080741712504085772295 35664121112568756128658443)
            ·
              refine ⟨53496181668853134192987665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35664121112568756128658443 53496181668853134192987665)
              ·
                refine ⟨40122136251639850644740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53496181668853134192987665 40122136251639850644740749)
                ·
                  refine ⟨15045801094364943991777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40122136251639850644740749 15045801094364943991777781)
                  ·
                    refine ⟨1410543852596713499229167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15045801094364943991777781 1410543852596713499229167)
                    ·
                      rfl

theorem cell23_8241073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_8241073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241073 prefixEnd_8241073 := by exact prefixLift 8241073
  have htrace : WordTrace (prefixWord ++ tailWord_8241073) baseStart_8241073 baseEnd_8241073 := by
    simpa [prefixWord, tailWord_8241073, baseEnd_8241073] using wordTrace_append hprefix tailTrace_8241073
  have hstable : (prefixWord ++ tailWord_8241073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241073).length < 2 ^ (prefixWord ++ tailWord_8241073).sum := by decide
  have hdescent : baseEnd_8241073 < baseStart_8241073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241093 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_8241093 : Nat := 118140960795 + 8241093 * 2 ^ 59
def prefixEnd_8241093 : Nat := 4983230072969 + 3 ^ 40 * 8241093 * 2
def baseEnd_8241093 : Nat := 4231641827403230419437409

theorem tailTrace_8241093 : CollatzResearch.WordTrace tailWord_8241093 prefixEnd_8241093 4231641827403230419437409 := by
  unfold tailWord_8241093
  simp only [CollatzResearch.WordTrace]
  refine ⟨300577355132935002475367933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200384903421956668316911955 300577355132935002475367933)
  ·
    refine ⟨112716508174850625928262975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300577355132935002475367933 112716508174850625928262975)
    ·
      refine ⟨169074762262275938892394463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112716508174850625928262975 169074762262275938892394463)
      ·
        refine ⟨253612143393413908338591695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169074762262275938892394463 253612143393413908338591695)
        ·
          refine ⟨380418215090120862507887543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253612143393413908338591695 380418215090120862507887543)
          ·
            refine ⟨570627322635181293761831315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380418215090120862507887543 570627322635181293761831315)
            ·
              refine ⟨855940983952771940642746973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570627322635181293761831315 855940983952771940642746973)
              ·
                refine ⟨320977868982289477741030115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855940983952771940642746973 320977868982289477741030115)
                ·
                  refine ⟨481466803473434216611545173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320977868982289477741030115 481466803473434216611545173)
                  ·
                    refine ⟨5642189103204307225916545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 481466803473434216611545173 5642189103204307225916545)
                    ·
                      refine ⟨4231641827403230419437409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642189103204307225916545 4231641827403230419437409)
                      ·
                        rfl

theorem cell23_8241093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_8241093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241093 prefixEnd_8241093 := by exact prefixLift 8241093
  have htrace : WordTrace (prefixWord ++ tailWord_8241093) baseStart_8241093 baseEnd_8241093 := by
    simpa [prefixWord, tailWord_8241093, baseEnd_8241093] using wordTrace_append hprefix tailTrace_8241093
  have hstable : (prefixWord ++ tailWord_8241093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241093).length < 2 ^ (prefixWord ++ tailWord_8241093).sum := by decide
  have hdescent : baseEnd_8241093 < baseStart_8241093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241103 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 4, 4]
def baseStart_8241103 : Nat := 118140960795 + 8241103 * 2 ^ 59
def prefixEnd_8241103 : Nat := 4983230072969 + 3 ^ 40 * 8241103 * 2
def baseEnd_8241103 : Nat := 1410548987403258460104121

theorem tailTrace_8241103 : CollatzResearch.WordTrace tailWord_8241103 prefixEnd_8241103 1410548987403258460104121 := by
  unfold tailWord_8241103
  simp only [CollatzResearch.WordTrace]
  refine ⟨300577719862898774183231963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200385146575265849455487975 300577719862898774183231963)
  ·
    refine ⟨450866579794348161274847945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300577719862898774183231963 450866579794348161274847945)
    ·
      refine ⟨338149934845761120956135959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450866579794348161274847945 338149934845761120956135959)
      ·
        refine ⟨507224902268641681434203939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338149934845761120956135959 507224902268641681434203939)
        ·
          refine ⟨760837353402962522151305909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507224902268641681434203939 760837353402962522151305909)
          ·
            refine ⟨71328501881527736451684929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 760837353402962522151305909 71328501881527736451684929)
            ·
              refine ⟨53496376411145802338763697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71328501881527736451684929 53496376411145802338763697)
              ·
                refine ⟨40122282308359351754072773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53496376411145802338763697 40122282308359351754072773)
                ·
                  refine ⟨7522927932817378453888645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40122282308359351754072773 7522927932817378453888645)
                  ·
                    refine ⟨1410548987403258460104121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7522927932817378453888645 1410548987403258460104121)
                    ·
                      rfl

theorem cell23_8241103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_8241103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241103 prefixEnd_8241103 := by exact prefixLift 8241103
  have htrace : WordTrace (prefixWord ++ tailWord_8241103) baseStart_8241103 baseEnd_8241103 := by
    simpa [prefixWord, tailWord_8241103, baseEnd_8241103] using wordTrace_append hprefix tailTrace_8241103
  have hstable : (prefixWord ++ tailWord_8241103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241103).length < 2 ^ (prefixWord ++ tailWord_8241103).sum := by decide
  have hdescent : baseEnd_8241103 < baseStart_8241103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241137 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_8241137 : Nat := 118140960795 + 8241137 * 2 ^ 59
def prefixEnd_8241137 : Nat := 4983230072969 + 3 ^ 40 * 8241137 * 2
def baseEnd_8241137 : Nat := 1410554806850676082429069

theorem tailTrace_8241137 : CollatzResearch.WordTrace tailWord_8241137 prefixEnd_8241137 1410554806850676082429069 := by
  unfold tailWord_8241137
  simp only [CollatzResearch.WordTrace]
  refine ⟨300578959944775597989969665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200385973296517065326646443 300578959944775597989969665)
  ·
    refine ⟨225434219958581698492477249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300578959944775597989969665 225434219958581698492477249)
    ·
      refine ⟨169075664968936273869357937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225434219958581698492477249 169075664968936273869357937)
      ·
        refine ⟨126806748726702205402018453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169075664968936273869357937 126806748726702205402018453)
        ·
          refine ⟨5944066346564165878219615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126806748726702205402018453 5944066346564165878219615)
          ·
            refine ⟨8916099519846248817329423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944066346564165878219615 8916099519846248817329423)
            ·
              refine ⟨13374149279769373225994135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916099519846248817329423 13374149279769373225994135)
              ·
                refine ⟨20061223919654059838991203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13374149279769373225994135 20061223919654059838991203)
                ·
                  refine ⟨30091835879481089758486805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20061223919654059838991203 30091835879481089758486805)
                  ·
                    refine ⟨1410554806850676082429069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30091835879481089758486805 1410554806850676082429069)
                    ·
                      rfl

theorem cell23_8241137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_8241137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241137 prefixEnd_8241137 := by exact prefixLift 8241137
  have htrace : WordTrace (prefixWord ++ tailWord_8241137) baseStart_8241137 baseEnd_8241137 := by
    simpa [prefixWord, tailWord_8241137, baseEnd_8241137] using wordTrace_append hprefix tailTrace_8241137
  have hstable : (prefixWord ++ tailWord_8241137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241137).length < 2 ^ (prefixWord ++ tailWord_8241137).sum := by decide
  have hdescent : baseEnd_8241137 < baseStart_8241137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241150 : List Nat := [4, 2, 2, 2, 1, 2, 1, 9]
def baseStart_8241150 : Nat := 118140960795 + 8241150 * 2 ^ 59
def prefixEnd_8241150 : Nat := 4983230072969 + 3 ^ 40 * 8241150 * 2
def baseEnd_8241150 : Nat := 156728559103723581349061

theorem tailTrace_8241150 : CollatzResearch.WordTrace tailWord_8241150 prefixEnd_8241150 156728559103723581349061 := by
  unfold tailWord_8241150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37572429261716062651274113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200386289395819000806795269 37572429261716062651274113)
  ·
    refine ⟨28179321946287046988455585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37572429261716062651274113 28179321946287046988455585)
    ·
      refine ⟨21134491459715285241341689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28179321946287046988455585 21134491459715285241341689)
      ·
        refine ⟨15850868594786463931006267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21134491459715285241341689 15850868594786463931006267)
        ·
          refine ⟨23776302892179695896509401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15850868594786463931006267 23776302892179695896509401)
          ·
            refine ⟨17832227169134771922382051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23776302892179695896509401 17832227169134771922382051)
            ·
              refine ⟨26748340753702157883573077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832227169134771922382051 26748340753702157883573077)
              ·
                refine ⟨156728559103723581349061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26748340753702157883573077 156728559103723581349061)
                ·
                  rfl

theorem cell23_8241150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_8241150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241150 prefixEnd_8241150 := by exact prefixLift 8241150
  have htrace : WordTrace (prefixWord ++ tailWord_8241150) baseStart_8241150 baseEnd_8241150 := by
    simpa [prefixWord, tailWord_8241150, baseEnd_8241150] using wordTrace_append hprefix tailTrace_8241150
  have hstable : (prefixWord ++ tailWord_8241150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241150).length < 2 ^ (prefixWord ++ tailWord_8241150).sum := by decide
  have hdescent : baseEnd_8241150 < baseStart_8241150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241160 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_8241160 : Nat := 118140960795 + 8241160 * 2 ^ 59
def prefixEnd_8241160 : Nat := 4983230072969 + 3 ^ 40 * 8241160 * 2
def baseEnd_8241160 : Nat := 4231676230607081657299601

theorem tailTrace_8241160 : CollatzResearch.WordTrace tailWord_8241160 prefixEnd_8241160 4231676230607081657299601 := by
  unfold tailWord_8241160
  simp only [CollatzResearch.WordTrace]
  refine ⟨150289899411846136459028467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200386532549128181945371289 150289899411846136459028467)
  ·
    refine ⟨225434849117769204688542701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150289899411846136459028467 225434849117769204688542701)
    ·
      refine ⟨84538068419163451758203513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225434849117769204688542701 84538068419163451758203513)
      ·
        refine ⟨63403551314372588818652635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84538068419163451758203513 63403551314372588818652635)
        ·
          refine ⟨95105326971558883227978953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63403551314372588818652635 95105326971558883227978953)
          ·
            refine ⟨71328995228669162420984215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95105326971558883227978953 71328995228669162420984215)
            ·
              refine ⟨106993492843003743631476323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71328995228669162420984215 106993492843003743631476323)
              ·
                refine ⟨160490239264505615447214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106993492843003743631476323 160490239264505615447214485)
                ·
                  refine ⟨7522979965523700724088179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160490239264505615447214485 7522979965523700724088179)
                  ·
                    refine ⟨11284469948285551086132269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522979965523700724088179 11284469948285551086132269)
                    ·
                      refine ⟨4231676230607081657299601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11284469948285551086132269 4231676230607081657299601)
                      ·
                        rfl

theorem cell23_8241160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_8241160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241160 prefixEnd_8241160 := by exact prefixLift 8241160
  have htrace : WordTrace (prefixWord ++ tailWord_8241160) baseStart_8241160 baseEnd_8241160 := by
    simpa [prefixWord, tailWord_8241160, baseEnd_8241160] using wordTrace_append hprefix tailTrace_8241160
  have hstable : (prefixWord ++ tailWord_8241160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241160).length < 2 ^ (prefixWord ++ tailWord_8241160).sum := by decide
  have hdescent : baseEnd_8241160 < baseStart_8241160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241183 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_8241183 : Nat := 118140960795 + 8241183 * 2 ^ 59
def prefixEnd_8241183 : Nat := 4983230072969 + 3 ^ 40 * 8241183 * 2
def baseEnd_8241183 : Nat := 4231688040662135067311995

theorem tailTrace_8241183 : CollatzResearch.WordTrace tailWord_8241183 prefixEnd_8241183 4231688040662135067311995 := by
  unfold tailWord_8241183
  simp only [CollatzResearch.WordTrace]
  refine ⟨300580637702608947846144203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200387091801739298564096135 300580637702608947846144203)
  ·
    refine ⟨450870956553913421769216305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300580637702608947846144203 450870956553913421769216305)
    ·
      refine ⟨338153217415435066326912229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450870956553913421769216305 338153217415435066326912229)
      ·
        refine ⟨63403728265394074936296043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338153217415435066326912229 63403728265394074936296043)
        ·
          refine ⟨95105592398091112404444065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63403728265394074936296043 95105592398091112404444065)
          ·
            refine ⟨71329194298568334303333049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95105592398091112404444065 71329194298568334303333049)
            ·
              refine ⟨53496895723926250727499787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71329194298568334303333049 53496895723926250727499787)
              ·
                refine ⟨80245343585889376091249681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53496895723926250727499787 80245343585889376091249681)
                ·
                  refine ⟨60184007689417032068437261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80245343585889376091249681 60184007689417032068437261)
                  ·
                    refine ⟨22569002883531387025663973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60184007689417032068437261 22569002883531387025663973)
                    ·
                      refine ⟨4231688040662135067311995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22569002883531387025663973 4231688040662135067311995)
                      ·
                        rfl

theorem cell23_8241183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_8241183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241183 prefixEnd_8241183 := by exact prefixLift 8241183
  have htrace : WordTrace (prefixWord ++ tailWord_8241183) baseStart_8241183 baseEnd_8241183 := by
    simpa [prefixWord, tailWord_8241183, baseEnd_8241183] using wordTrace_append hprefix tailTrace_8241183
  have hstable : (prefixWord ++ tailWord_8241183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241183).length < 2 ^ (prefixWord ++ tailWord_8241183).sum := by decide
  have hdescent : baseEnd_8241183 < baseStart_8241183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241194 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_8241194 : Nat := 118140960795 + 8241194 * 2 ^ 59
def prefixEnd_8241194 : Nat := 4983230072969 + 3 ^ 40 * 8241194 * 2
def baseEnd_8241194 : Nat := 4231693688949334524274445

theorem tailTrace_8241194 : CollatzResearch.WordTrace tailWord_8241194 prefixEnd_8241194 4231693688949334524274445 := by
  unfold tailWord_8241194
  simp only [CollatzResearch.WordTrace]
  refine ⟨75145259726392274181198659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200387359270379397816529757 75145259726392274181198659)
  ·
    refine ⟨112717889589588411271797989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75145259726392274181198659 112717889589588411271797989)
    ·
      refine ⟨21134604298047827113462123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112717889589588411271797989 21134604298047827113462123)
      ·
        refine ⟨31701906447071740670193185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21134604298047827113462123 31701906447071740670193185)
        ·
          refine ⟨23776429835303805502644889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31701906447071740670193185 23776429835303805502644889)
          ·
            refine ⟨17832322376477854126983667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23776429835303805502644889 17832322376477854126983667)
            ·
              refine ⟨26748483564716781190475501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832322376477854126983667 26748483564716781190475501)
              ·
                refine ⟨10030681336768792946428313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26748483564716781190475501 10030681336768792946428313)
                ·
                  refine ⟨7523011002576594709821235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10030681336768792946428313 7523011002576594709821235)
                  ·
                    refine ⟨11284516503864892064731853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7523011002576594709821235 11284516503864892064731853)
                    ·
                      refine ⟨4231693688949334524274445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11284516503864892064731853 4231693688949334524274445)
                      ·
                        rfl

theorem cell23_8241194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_8241194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241194 prefixEnd_8241194 := by exact prefixLift 8241194
  have htrace : WordTrace (prefixWord ++ tailWord_8241194) baseStart_8241194 baseEnd_8241194 := by
    simpa [prefixWord, tailWord_8241194, baseEnd_8241194] using wordTrace_append hprefix tailTrace_8241194
  have hstable : (prefixWord ++ tailWord_8241194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241194).length < 2 ^ (prefixWord ++ tailWord_8241194).sum := by decide
  have hdescent : baseEnd_8241194 < baseStart_8241194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241203 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_8241203 : Nat := 118140960795 + 8241203 * 2 ^ 59
def prefixEnd_8241203 : Nat := 4983230072969 + 3 ^ 40 * 8241203 * 2
def baseEnd_8241203 : Nat := 4231698310275224989061903

theorem tailTrace_8241203 : CollatzResearch.WordTrace tailWord_8241203 prefixEnd_8241203 4231698310275224989061903 := by
  unfold tailWord_8241203
  simp only [CollatzResearch.WordTrace]
  refine ⟨300581367162536491261872263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200387578108357660841248175 300581367162536491261872263)
  ·
    refine ⟨450872050743804736892808395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300581367162536491261872263 450872050743804736892808395)
    ·
      refine ⟨676308076115707105339212593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450872050743804736892808395 676308076115707105339212593)
      ·
        refine ⟨507231057086780329004409445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676308076115707105339212593 507231057086780329004409445)
        ·
          refine ⟨95105823203771311688326771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507231057086780329004409445 95105823203771311688326771)
          ·
            refine ⟨142658734805656967532490157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95105823203771311688326771 142658734805656967532490157)
            ·
              refine ⟨53497025552121362824683809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142658734805656967532490157 53497025552121362824683809)
              ·
                refine ⟨40122769164091022118512857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53497025552121362824683809 40122769164091022118512857)
                ·
                  refine ⟨30092076873068266588884643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40122769164091022118512857 30092076873068266588884643)
                  ·
                    refine ⟨45138115309602399883326965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30092076873068266588884643 45138115309602399883326965)
                    ·
                      refine ⟨4231698310275224989061903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45138115309602399883326965 4231698310275224989061903)
                      ·
                        rfl

theorem cell23_8241203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_8241203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241203 prefixEnd_8241203 := by exact prefixLift 8241203
  have htrace : WordTrace (prefixWord ++ tailWord_8241203) baseStart_8241203 baseEnd_8241203 := by
    simpa [prefixWord, tailWord_8241203, baseEnd_8241203] using wordTrace_append hprefix tailTrace_8241203
  have hstable : (prefixWord ++ tailWord_8241203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241203).length < 2 ^ (prefixWord ++ tailWord_8241203).sum := by decide
  have hdescent : baseEnd_8241203 < baseStart_8241203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241217 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_8241217 : Nat := 118140960795 + 8241217 * 2 ^ 59
def prefixEnd_8241217 : Nat := 4983230072969 + 3 ^ 40 * 8241217 * 2
def baseEnd_8241217 : Nat := 4231705499004387934286839

theorem tailTrace_8241217 : CollatzResearch.WordTrace tailWord_8241217 prefixEnd_8241217 4231705499004387934286839 := by
  unfold tailWord_8241217
  simp only [CollatzResearch.WordTrace]
  refine ⟨300581877784485771652881905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200387918522990514435254603 300581877784485771652881905)
  ·
    refine ⟨225436408338364328739661429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300581877784485771652881905 225436408338364328739661429)
    ·
      refine ⟨21134663281721655819343259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225436408338364328739661429 21134663281721655819343259)
      ·
        refine ⟨31701994922582483729014889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21134663281721655819343259 31701994922582483729014889)
        ·
          refine ⟨23776496191936862796761167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31701994922582483729014889 23776496191936862796761167)
          ·
            refine ⟨35664744287905294195141751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23776496191936862796761167 35664744287905294195141751)
            ·
              refine ⟨53497116431857941292712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35664744287905294195141751 53497116431857941292712627)
              ·
                refine ⟨80245674647786911939068941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53497116431857941292712627 80245674647786911939068941)
                ·
                  refine ⟨30092127992920091977150853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80245674647786911939068941 30092127992920091977150853)
                  ·
                    refine ⟨5642273998672517245715785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30092127992920091977150853 5642273998672517245715785)
                    ·
                      refine ⟨4231705499004387934286839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642273998672517245715785 4231705499004387934286839)
                      ·
                        rfl

theorem cell23_8241217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_8241217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241217 prefixEnd_8241217 := by exact prefixLift 8241217
  have htrace : WordTrace (prefixWord ++ tailWord_8241217) baseStart_8241217 baseEnd_8241217 := by
    simpa [prefixWord, tailWord_8241217, baseEnd_8241217] using wordTrace_append hprefix tailTrace_8241217
  have hstable : (prefixWord ++ tailWord_8241217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241217).length < 2 ^ (prefixWord ++ tailWord_8241217).sum := by decide
  have hdescent : baseEnd_8241217 < baseStart_8241217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241302 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_8241302 : Nat := 118140960795 + 8241302 * 2 ^ 59
def prefixEnd_8241302 : Nat := 4983230072969 + 3 ^ 40 * 8241302 * 2
def baseEnd_8241302 : Nat := 4231749144860020101723949

theorem tailTrace_8241302 : CollatzResearch.WordTrace tailWord_8241302 prefixEnd_8241302 4231749144860020101723949 := by
  unfold tailWord_8241302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786561124323614448107885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200389985326118554113150773 18786561124323614448107885)
  ·
    refine ⟨7044960421621355418040457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18786561124323614448107885 7044960421621355418040457)
    ·
      refine ⟨5283720316216016563530343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7044960421621355418040457 5283720316216016563530343)
      ·
        refine ⟨7925580474324024845295515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283720316216016563530343 7925580474324024845295515)
        ·
          refine ⟨11888370711486037267943273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925580474324024845295515 11888370711486037267943273)
          ·
            refine ⟨8916278033614527950957455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11888370711486037267943273 8916278033614527950957455)
            ·
              refine ⟨13374417050421791926436183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916278033614527950957455 13374417050421791926436183)
              ·
                refine ⟨20061625575632687889654275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13374417050421791926436183 20061625575632687889654275)
                ·
                  refine ⟨30092438363449031834481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20061625575632687889654275 30092438363449031834481413)
                  ·
                    refine ⟨5642332193146693468965265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30092438363449031834481413 5642332193146693468965265)
                    ·
                      refine ⟨4231749144860020101723949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642332193146693468965265 4231749144860020101723949)
                      ·
                        rfl

theorem cell23_8241302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_8241302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241302 prefixEnd_8241302 := by exact prefixLift 8241302
  have htrace : WordTrace (prefixWord ++ tailWord_8241302) baseStart_8241302 baseEnd_8241302 := by
    simpa [prefixWord, tailWord_8241302, baseEnd_8241302] using wordTrace_append hprefix tailTrace_8241302
  have hstable : (prefixWord ++ tailWord_8241302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241302).length < 2 ^ (prefixWord ++ tailWord_8241302).sum := by decide
  have hdescent : baseEnd_8241302 < baseStart_8241302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241367 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_8241367 : Nat := 118140960795 + 8241367 * 2 ^ 59
def prefixEnd_8241367 : Nat := 4983230072969 + 3 ^ 40 * 8241367 * 2
def baseEnd_8241367 : Nat := 4231782521102562347411149

theorem tailTrace_8241367 : CollatzResearch.WordTrace tailWord_8241367 prefixEnd_8241367 4231782521102562347411149 := by
  unfold tailWord_8241367
  simp only [CollatzResearch.WordTrace]
  refine ⟨300587348733942347270842355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200391565822628231513894903 300587348733942347270842355)
  ·
    refine ⟨450881023100913520906263533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300587348733942347270842355 450881023100913520906263533)
    ·
      refine ⟨169080383662842570339848825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450881023100913520906263533 169080383662842570339848825)
      ·
        refine ⟨126810287747131927754886619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169080383662842570339848825 126810287747131927754886619)
        ·
          refine ⟨190215431620697891632329929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126810287747131927754886619 190215431620697891632329929)
          ·
            refine ⟨142661573715523418724247447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190215431620697891632329929 142661573715523418724247447)
            ·
              refine ⟨213992360573285128086371171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142661573715523418724247447 213992360573285128086371171)
              ·
                refine ⟨320988540859927692129556757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213992360573285128086371171 320988540859927692129556757)
                ·
                  refine ⟨15046337852809110568572973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320988540859927692129556757 15046337852809110568572973)
                  ·
                    refine ⟨5642376694803416463214865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15046337852809110568572973 5642376694803416463214865)
                    ·
                      refine ⟨4231782521102562347411149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642376694803416463214865 4231782521102562347411149)
                      ·
                        rfl

theorem cell23_8241367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_8241367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241367 prefixEnd_8241367 := by exact prefixLift 8241367
  have htrace : WordTrace (prefixWord ++ tailWord_8241367) baseStart_8241367 baseEnd_8241367 := by
    simpa [prefixWord, tailWord_8241367, baseEnd_8241367] using wordTrace_append hprefix tailTrace_8241367
  have hstable : (prefixWord ++ tailWord_8241367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241367).length < 2 ^ (prefixWord ++ tailWord_8241367).sum := by decide
  have hdescent : baseEnd_8241367 < baseStart_8241367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241384 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_8241384 : Nat := 118140960795 + 8241384 * 2 ^ 59
def prefixEnd_8241384 : Nat := 4983230072969 + 3 ^ 40 * 8241384 * 2
def baseEnd_8241384 : Nat := 4231791250273688780898571

theorem tailTrace_8241384 : CollatzResearch.WordTrace tailWord_8241384 prefixEnd_8241384 4231791250273688780898571 := by
  unfold tailWord_8241384
  simp only [CollatzResearch.WordTrace]
  refine ⟨150293984387440379587105603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200391979183253839449474137 150293984387440379587105603)
  ·
    refine ⟨225440976581160569380658405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150293984387440379587105603 225440976581160569380658405)
    ·
      refine ⟨42270183108967606758873451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225440976581160569380658405 42270183108967606758873451)
      ·
        refine ⟨63405274663451410138310177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42270183108967606758873451 63405274663451410138310177)
        ·
          refine ⟨47553955997588557603732633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63405274663451410138310177 47553955997588557603732633)
          ·
            refine ⟨35665466998191418202799475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47553955997588557603732633 35665466998191418202799475)
            ·
              refine ⟨53498200497287127304199213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35665466998191418202799475 53498200497287127304199213)
              ·
                refine ⟨20061825186482672739074705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53498200497287127304199213 20061825186482672739074705)
                ·
                  refine ⟨15046368889862004554306029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20061825186482672739074705 15046368889862004554306029)
                  ·
                    refine ⟨5642388333698251707864761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15046368889862004554306029 5642388333698251707864761)
                    ·
                      refine ⟨4231791250273688780898571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642388333698251707864761 4231791250273688780898571)
                      ·
                        rfl

theorem cell23_8241384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_8241384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241384 prefixEnd_8241384 := by exact prefixLift 8241384
  have htrace : WordTrace (prefixWord ++ tailWord_8241384) baseStart_8241384 baseEnd_8241384 := by
    simpa [prefixWord, tailWord_8241384, baseEnd_8241384] using wordTrace_append hprefix tailTrace_8241384
  have hstable : (prefixWord ++ tailWord_8241384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241384).length < 2 ^ (prefixWord ++ tailWord_8241384).sum := by decide
  have hdescent : baseEnd_8241384 < baseStart_8241384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241417 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_8241417 : Nat := 118140960795 + 8241417 * 2 ^ 59
def prefixEnd_8241417 : Nat := 4983230072969 + 3 ^ 40 * 8241417 * 2
def baseEnd_8241417 : Nat := 4231808195135287151785919

theorem tailTrace_8241417 : CollatzResearch.WordTrace tailWord_8241417 prefixEnd_8241417 4231808195135287151785919 := by
  unfold tailWord_8241417
  simp only [CollatzResearch.WordTrace]
  refine ⟨300589172383761205810162505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200392781589174137206775003 300589172383761205810162505)
  ·
    refine ⟨225441879287820904357621879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300589172383761205810162505 225441879287820904357621879)
    ·
      refine ⟨338162818931731356536432819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225441879287820904357621879 338162818931731356536432819)
      ·
        refine ⟨507244228397597034804649229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338162818931731356536432819 507244228397597034804649229)
        ·
          refine ⟨190216585649098888051743461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507244228397597034804649229 190216585649098888051743461)
          ·
            refine ⟨35665609809206041509701899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190216585649098888051743461 35665609809206041509701899)
            ·
              refine ⟨53498414713809062264552849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35665609809206041509701899 53498414713809062264552849)
              ·
                refine ⟨40123811035356796698414637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53498414713809062264552849 40123811035356796698414637)
                ·
                  refine ⟨15046429138258798761905489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40123811035356796698414637 15046429138258798761905489)
                  ·
                    refine ⟨11284821853694099071429117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15046429138258798761905489 11284821853694099071429117)
                    ·
                      refine ⟨4231808195135287151785919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11284821853694099071429117 4231808195135287151785919)
                      ·
                        rfl

theorem cell23_8241417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_8241417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241417 prefixEnd_8241417 := by exact prefixLift 8241417
  have htrace : WordTrace (prefixWord ++ tailWord_8241417) baseStart_8241417 baseEnd_8241417 := by
    simpa [prefixWord, tailWord_8241417, baseEnd_8241417] using wordTrace_append hprefix tailTrace_8241417
  have hstable : (prefixWord ++ tailWord_8241417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241417).length < 2 ^ (prefixWord ++ tailWord_8241417).sum := by decide
  have hdescent : baseEnd_8241417 < baseStart_8241417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241431 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_8241431 : Nat := 118140960795 + 8241431 * 2 ^ 59
def prefixEnd_8241431 : Nat := 4983230072969 + 3 ^ 40 * 8241431 * 2
def baseEnd_8241431 : Nat := 4231815383864450097010855

theorem tailTrace_8241431 : CollatzResearch.WordTrace tailWord_8241431 prefixEnd_8241431 4231815383864450097010855 := by
  unfold tailWord_8241431
  simp only [CollatzResearch.WordTrace]
  refine ⟨300589683005710486201172147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200393122003806990800781431 300589683005710486201172147)
  ·
    refine ⟨450884524508565729301758221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300589683005710486201172147 450884524508565729301758221)
    ·
      refine ⟨169081696690712148488159333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450884524508565729301758221 169081696690712148488159333)
      ·
        refine ⟨31702818129508527841529875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169081696690712148488159333 31702818129508527841529875)
        ·
          refine ⟨47554227194262791762294813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31702818129508527841529875 47554227194262791762294813)
          ·
            refine ⟨17832835197848546910860555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47554227194262791762294813 17832835197848546910860555)
            ·
              refine ⟨26749252796772820366290833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832835197848546910860555 26749252796772820366290833)
              ·
                refine ⟨20061939597579615274718125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26749252796772820366290833 20061939597579615274718125)
                ·
                  refine ⟨7523227349092355728019297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20061939597579615274718125 7523227349092355728019297)
                  ·
                    refine ⟨5642420511819266796014473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523227349092355728019297 5642420511819266796014473)
                    ·
                      refine ⟨4231815383864450097010855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642420511819266796014473 4231815383864450097010855)
                      ·
                        rfl

theorem cell23_8241431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_8241431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241431 prefixEnd_8241431 := by exact prefixLift 8241431
  have htrace : WordTrace (prefixWord ++ tailWord_8241431) baseStart_8241431 baseEnd_8241431 := by
    simpa [prefixWord, tailWord_8241431, baseEnd_8241431] using wordTrace_append hprefix tailTrace_8241431
  have hstable : (prefixWord ++ tailWord_8241431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241431).length < 2 ^ (prefixWord ++ tailWord_8241431).sum := by decide
  have hdescent : baseEnd_8241431 < baseStart_8241431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241448 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_8241448 : Nat := 118140960795 + 8241448 * 2 ^ 59
def prefixEnd_8241448 : Nat := 4983230072969 + 3 ^ 40 * 8241448 * 2
def baseEnd_8241448 : Nat := 4231824113035576530498277

theorem tailTrace_8241448 : CollatzResearch.WordTrace tailWord_8241448 prefixEnd_8241448 4231824113035576530498277 := by
  unfold tailWord_8241448
  simp only [CollatzResearch.WordTrace]
  refine ⟨150295151523324449052270499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200393535364432598736360665 150295151523324449052270499)
  ·
    refine ⟨225442727284986673578405749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150295151523324449052270499 225442727284986673578405749)
    ·
      refine ⟨21135255682967500647975539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225442727284986673578405749 21135255682967500647975539)
      ·
        refine ⟨31702883524451250971963309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135255682967500647975539 31702883524451250971963309)
        ·
          refine ⟨11888581321669219114486241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31702883524451250971963309 11888581321669219114486241)
          ·
            refine ⟨8916435991251914335864681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11888581321669219114486241 8916435991251914335864681)
            ·
              refine ⟨6687326993438935751898511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916435991251914335864681 6687326993438935751898511)
              ·
                refine ⟨10030990490158403627847767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687326993438935751898511 10030990490158403627847767)
                ·
                  refine ⟨15046485735237605441771651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030990490158403627847767 15046485735237605441771651)
                  ·
                    refine ⟨22569728602856408162657477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15046485735237605441771651 22569728602856408162657477)
                    ·
                      refine ⟨4231824113035576530498277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22569728602856408162657477 4231824113035576530498277)
                      ·
                        rfl

theorem cell23_8241448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_8241448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241448 prefixEnd_8241448 := by exact prefixLift 8241448
  have htrace : WordTrace (prefixWord ++ tailWord_8241448) baseStart_8241448 baseEnd_8241448 := by
    simpa [prefixWord, tailWord_8241448, baseEnd_8241448] using wordTrace_append hprefix tailTrace_8241448
  have hstable : (prefixWord ++ tailWord_8241448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241448).length < 2 ^ (prefixWord ++ tailWord_8241448).sum := by decide
  have hdescent : baseEnd_8241448 < baseStart_8241448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241454 : List Nat := [4, 1, 3, 3, 1, 1, 10]
def baseStart_8241454 : Nat := 118140960795 + 8241454 * 2 ^ 59
def prefixEnd_8241454 : Nat := 4983230072969 + 3 ^ 40 * 8241454 * 2
def baseEnd_8241454 : Nat := 52244780171845722308929

theorem tailTrace_8241454 : CollatzResearch.WordTrace tailWord_8241454 prefixEnd_8241454 52244780171845722308929 := by
  unfold tailWord_8241454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573815235578395141157427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200393681256418107419506277 37573815235578395141157427)
  ·
    refine ⟨56360722853367592711736141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37573815235578395141157427 56360722853367592711736141)
    ·
      refine ⟨21135271070012847266901053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56360722853367592711736141 21135271070012847266901053)
      ·
        refine ⟨7925726651254817725087895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21135271070012847266901053 7925726651254817725087895)
        ·
          refine ⟨11888589976882226587631843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925726651254817725087895 11888589976882226587631843)
          ·
            refine ⟨17832884965323339881447765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888589976882226587631843 17832884965323339881447765)
            ·
              refine ⟨52244780171845722308929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17832884965323339881447765 52244780171845722308929)
              ·
                rfl

theorem cell23_8241454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 10].length) (baseStart_8241454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241454 prefixEnd_8241454 := by exact prefixLift 8241454
  have htrace : WordTrace (prefixWord ++ tailWord_8241454) baseStart_8241454 baseEnd_8241454 := by
    simpa [prefixWord, tailWord_8241454, baseEnd_8241454] using wordTrace_append hprefix tailTrace_8241454
  have hstable : (prefixWord ++ tailWord_8241454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241454).length < 2 ^ (prefixWord ++ tailWord_8241454).sum := by decide
  have hdescent : baseEnd_8241454 < baseStart_8241454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241458 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_8241458 : Nat := 118140960795 + 8241458 * 2 ^ 59
def prefixEnd_8241458 : Nat := 4983230072969 + 3 ^ 40 * 8241458 * 2
def baseEnd_8241458 : Nat := 1410609749280707163791077

theorem tailTrace_8241458 : CollatzResearch.WordTrace tailWord_8241458 prefixEnd_8241458 1410609749280707163791077 := by
  unfold tailWord_8241458
  simp only [CollatzResearch.WordTrace]
  refine ⟨75147666944153167453101257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200393778517741779874936685 75147666944153167453101257)
  ·
    refine ⟨56360750208114875589825943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75147666944153167453101257 56360750208114875589825943)
    ·
      refine ⟨84541125312172313384738915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56360750208114875589825943 84541125312172313384738915)
      ·
        refine ⟨126811687968258470077108373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84541125312172313384738915 126811687968258470077108373)
        ·
          refine ⟨5944297873512115784864455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126811687968258470077108373 5944297873512115784864455)
          ·
            refine ⟨8916446810268173677296683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944297873512115784864455 8916446810268173677296683)
            ·
              refine ⟨13374670215402260515945025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916446810268173677296683 13374670215402260515945025)
              ·
                refine ⟨10031002661551695386958769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13374670215402260515945025 10031002661551695386958769)
                ·
                  refine ⟨7523251996163771540219077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031002661551695386958769 7523251996163771540219077)
                  ·
                    refine ⟨1410609749280707163791077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7523251996163771540219077 1410609749280707163791077)
                    ·
                      rfl

theorem cell23_8241458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_8241458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241458 prefixEnd_8241458 := by exact prefixLift 8241458
  have htrace : WordTrace (prefixWord ++ tailWord_8241458) baseStart_8241458 baseEnd_8241458 := by
    simpa [prefixWord, tailWord_8241458, baseEnd_8241458] using wordTrace_append hprefix tailTrace_8241458
  have hstable : (prefixWord ++ tailWord_8241458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241458).length < 2 ^ (prefixWord ++ tailWord_8241458).sum := by decide
  have hdescent : baseEnd_8241458 < baseStart_8241458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241507 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_8241507 : Nat := 118140960795 + 8241507 * 2 ^ 59
def prefixEnd_8241507 : Nat := 4983230072969 + 3 ^ 40 * 8241507 * 2
def baseEnd_8241507 : Nat := 4231854408394191799660505

theorem tailTrace_8241507 : CollatzResearch.WordTrace tailWord_8241507 prefixEnd_8241507 4231854408394191799660505 := by
  unfold tailWord_8241507
  simp only [CollatzResearch.WordTrace]
  refine ⟨300592454953435151180938775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200394969968956767453959183 300592454953435151180938775)
  ·
    refine ⟨450888682430152726771408163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300592454953435151180938775 450888682430152726771408163)
    ·
      refine ⟨676333023645229090157112245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450888682430152726771408163 676333023645229090157112245)
      ·
        refine ⟨63406220966740227202229273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 676333023645229090157112245 63406220966740227202229273)
        ·
          refine ⟨47554665725055170401671955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63406220966740227202229273 47554665725055170401671955)
          ·
            refine ⟨71331998587582755602507933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47554665725055170401671955 71331998587582755602507933)
            ·
              refine ⟨26749499470343533350940475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71331998587582755602507933 26749499470343533350940475)
              ·
                refine ⟨40124249205515300026410713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26749499470343533350940475 40124249205515300026410713)
                ·
                  refine ⟨30093186904136475019808035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40124249205515300026410713 30093186904136475019808035)
                  ·
                    refine ⟨45139780356204712529712053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30093186904136475019808035 45139780356204712529712053)
                    ·
                      refine ⟨4231854408394191799660505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45139780356204712529712053 4231854408394191799660505)
                      ·
                        rfl

theorem cell23_8241507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_8241507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241507 prefixEnd_8241507 := by exact prefixLift 8241507
  have htrace : WordTrace (prefixWord ++ tailWord_8241507) baseStart_8241507 baseEnd_8241507 := by
    simpa [prefixWord, tailWord_8241507, baseEnd_8241507] using wordTrace_append hprefix tailTrace_8241507
  have hstable : (prefixWord ++ tailWord_8241507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241507).length < 2 ^ (prefixWord ++ tailWord_8241507).sum := by decide
  have hdescent : baseEnd_8241507 < baseStart_8241507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241521 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_8241521 : Nat := 118140960795 + 8241521 * 2 ^ 59
def prefixEnd_8241521 : Nat := 4983230072969 + 3 ^ 40 * 8241521 * 2
def baseEnd_8241521 : Nat := 4231861597123354744885441

theorem tailTrace_8241521 : CollatzResearch.WordTrace tailWord_8241521 prefixEnd_8241521 4231861597123354744885441 := by
  unfold tailWord_8241521
  simp only [CollatzResearch.WordTrace]
  refine ⟨300592965575384431571948417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200395310383589621047965611 300592965575384431571948417)
  ·
    refine ⟨225444724181538323678961313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300592965575384431571948417 225444724181538323678961313)
    ·
      refine ⟨169083543136153742759220985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225444724181538323678961313 169083543136153742759220985)
      ·
        refine ⟨126812657352115307069415739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169083543136153742759220985 126812657352115307069415739)
        ·
          refine ⟨190218986028172960604123609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126812657352115307069415739 190218986028172960604123609)
          ·
            refine ⟨142664239521129720453092707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190218986028172960604123609 142664239521129720453092707)
            ·
              refine ⟨213996359281694580679639061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142664239521129720453092707 213996359281694580679639061)
              ·
                refine ⟨10031079341329433469358081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213996359281694580679639061 10031079341329433469358081)
                ·
                  refine ⟨7523309505997075102018561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031079341329433469358081 7523309505997075102018561)
                  ·
                    refine ⟨5642482129497806326513921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523309505997075102018561 5642482129497806326513921)
                    ·
                      refine ⟨4231861597123354744885441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642482129497806326513921 4231861597123354744885441)
                      ·
                        rfl

theorem cell23_8241521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_8241521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241521 prefixEnd_8241521 := by exact prefixLift 8241521
  have htrace : WordTrace (prefixWord ++ tailWord_8241521) baseStart_8241521 baseEnd_8241521 := by
    simpa [prefixWord, tailWord_8241521, baseEnd_8241521] using wordTrace_append hprefix tailTrace_8241521
  have hstable : (prefixWord ++ tailWord_8241521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241521).length < 2 ^ (prefixWord ++ tailWord_8241521).sum := by decide
  have hdescent : baseEnd_8241521 < baseStart_8241521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241567 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_8241567 : Nat := 118140960795 + 8241567 * 2 ^ 59
def prefixEnd_8241567 : Nat := 4983230072969 + 3 ^ 40 * 8241567 * 2
def baseEnd_8241567 : Nat := 4231885217233461564910229

theorem tailTrace_8241567 : CollatzResearch.WordTrace tailWord_8241567 prefixEnd_8241567 4231885217233461564910229 := by
  unfold tailWord_8241567
  simp only [CollatzResearch.WordTrace]
  refine ⟨300594643333217781428122955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200396428888811854285415303 300594643333217781428122955)
  ·
    refine ⟨450891964999826672142184433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300594643333217781428122955 450891964999826672142184433)
    ·
      refine ⟨338168973749870004106638325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450891964999826672142184433 338168973749870004106638325)
      ·
        refine ⟨31703341289050312884997343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338168973749870004106638325 31703341289050312884997343)
        ·
          refine ⟨47555011933575469327496015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31703341289050312884997343 47555011933575469327496015)
          ·
            refine ⟨71332517900363203991244023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47555011933575469327496015 71332517900363203991244023)
            ·
              refine ⟨106998776850544805986866035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71332517900363203991244023 106998776850544805986866035)
              ·
                refine ⟨160498165275817208980299053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106998776850544805986866035 160498165275817208980299053)
                ·
                  refine ⟨60186811978431453367612145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160498165275817208980299053 60186811978431453367612145)
                  ·
                    refine ⟨45140108983823590025709109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60186811978431453367612145 45140108983823590025709109)
                    ·
                      refine ⟨4231885217233461564910229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45140108983823590025709109 4231885217233461564910229)
                      ·
                        rfl

theorem cell23_8241567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_8241567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241567 prefixEnd_8241567 := by exact prefixLift 8241567
  have htrace : WordTrace (prefixWord ++ tailWord_8241567) baseStart_8241567 baseEnd_8241567 := by
    simpa [prefixWord, tailWord_8241567, baseEnd_8241567] using wordTrace_append hprefix tailTrace_8241567
  have hstable : (prefixWord ++ tailWord_8241567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241567).length < 2 ^ (prefixWord ++ tailWord_8241567).sum := by decide
  have hdescent : baseEnd_8241567 < baseStart_8241567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241654 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_8241654 : Nat := 118140960795 + 8241654 * 2 ^ 59
def prefixEnd_8241654 : Nat := 4983230072969 + 3 ^ 40 * 8241654 * 2
def baseEnd_8241654 : Nat := 4231929890050402724522329

theorem tailTrace_8241654 : CollatzResearch.WordTrace tailWord_8241654 prefixEnd_8241654 4231929890050402724522329 := by
  unfold tailWord_8241654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787363530243912205408751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200398544322601730191026677 18787363530243912205408751)
  ·
    refine ⟨28181045295365868308113127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787363530243912205408751 28181045295365868308113127)
    ·
      refine ⟨42271567943048802462169691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28181045295365868308113127 42271567943048802462169691)
      ·
        refine ⟨63407351914573203693254537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42271567943048802462169691 63407351914573203693254537)
        ·
          refine ⟨47555513935929902769940903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63407351914573203693254537 47555513935929902769940903)
          ·
            refine ⟨71333270903894854154911355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47555513935929902769940903 71333270903894854154911355)
            ·
              refine ⟨106999906355842281232367033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71333270903894854154911355 106999906355842281232367033)
              ·
                refine ⟨80249929766881710924275275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106999906355842281232367033 80249929766881710924275275)
                ·
                  refine ⟨120374894650322566386412913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80249929766881710924275275 120374894650322566386412913)
                  ·
                    refine ⟨90281170987741924789809685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120374894650322566386412913 90281170987741924789809685)
                    ·
                      refine ⟨4231929890050402724522329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90281170987741924789809685 4231929890050402724522329)
                      ·
                        rfl

theorem cell23_8241654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_8241654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241654 prefixEnd_8241654 := by exact prefixLift 8241654
  have htrace : WordTrace (prefixWord ++ tailWord_8241654) baseStart_8241654 baseEnd_8241654 := by
    simpa [prefixWord, tailWord_8241654, baseEnd_8241654] using wordTrace_append hprefix tailTrace_8241654
  have hstable : (prefixWord ++ tailWord_8241654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241654).length < 2 ^ (prefixWord ++ tailWord_8241654).sum := by decide
  have hdescent : baseEnd_8241654 < baseStart_8241654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241657 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_8241657 : Nat := 118140960795 + 8241657 * 2 ^ 59
def prefixEnd_8241657 : Nat := 4983230072969 + 3 ^ 40 * 8241657 * 2
def baseEnd_8241657 : Nat := 4231931430492366212784815

theorem tailTrace_8241657 : CollatzResearch.WordTrace tailWord_8241657 prefixEnd_8241657 4231931430492366212784815 := by
  unfold tailWord_8241657
  simp only [CollatzResearch.WordTrace]
  refine ⟨300597925902891726798899225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200398617268594484532599483 300597925902891726798899225)
  ·
    refine ⟨225448444427168795099174419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300597925902891726798899225 225448444427168795099174419)
    ·
      refine ⟨338172666640753192648761629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225448444427168795099174419 338172666640753192648761629)
      ·
        refine ⟨126814749990282447243285611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338172666640753192648761629 126814749990282447243285611)
        ·
          refine ⟨190222124985423670864928417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126814749990282447243285611 190222124985423670864928417)
          ·
            refine ⟨142666593739067753148696313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190222124985423670864928417 142666593739067753148696313)
            ·
              refine ⟨106999945304300814861522235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142666593739067753148696313 106999945304300814861522235)
              ·
                refine ⟨160499917956451222292283353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106999945304300814861522235 160499917956451222292283353)
                ·
                  refine ⟨120374938467338416719212515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160499917956451222292283353 120374938467338416719212515)
                  ·
                    refine ⟨180562407701007625078818773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120374938467338416719212515 180562407701007625078818773)
                    ·
                      refine ⟨4231931430492366212784815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180562407701007625078818773 4231931430492366212784815)
                      ·
                        rfl

theorem cell23_8241657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_8241657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241657 prefixEnd_8241657 := by exact prefixLift 8241657
  have htrace : WordTrace (prefixWord ++ tailWord_8241657) baseStart_8241657 baseEnd_8241657 := by
    simpa [prefixWord, tailWord_8241657, baseEnd_8241657] using wordTrace_append hprefix tailTrace_8241657
  have hstable : (prefixWord ++ tailWord_8241657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241657).length < 2 ^ (prefixWord ++ tailWord_8241657).sum := by decide
  have hdescent : baseEnd_8241657 < baseStart_8241657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241661 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_8241661 : Nat := 118140960795 + 8241661 * 2 ^ 59
def prefixEnd_8241661 : Nat := 4983230072969 + 3 ^ 40 * 8241661 * 2
def baseEnd_8241661 : Nat := 4231933484414984197134797

theorem tailTrace_8241661 : CollatzResearch.WordTrace tailWord_8241661 prefixEnd_8241661 4231933484414984197134797 := by
  unfold tailWord_8241661
  simp only [CollatzResearch.WordTrace]
  refine ⟨300598071794877235482044837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200398714529918156988029891 300598071794877235482044837)
  ·
    refine ⟨56362138461539481652883407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300598071794877235482044837 56362138461539481652883407)
    ·
      refine ⟨84543207692309222479325111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56362138461539481652883407 84543207692309222479325111)
      ·
        refine ⟨126814811538463833718987667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84543207692309222479325111 126814811538463833718987667)
        ·
          refine ⟨190222217307695750578481501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126814811538463833718987667 190222217307695750578481501)
          ·
            refine ⟨71333331490385906466930563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190222217307695750578481501 71333331490385906466930563)
            ·
              refine ⟨106999997235578859700395845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71333331490385906466930563 106999997235578859700395845)
              ·
                refine ⟨20062499481671036193824221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106999997235578859700395845 20062499481671036193824221)
                ·
                  refine ⟨7523437305626638572684083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20062499481671036193824221 7523437305626638572684083)
                  ·
                    refine ⟨11285155958439957859026125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7523437305626638572684083 11285155958439957859026125)
                    ·
                      refine ⟨4231933484414984197134797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285155958439957859026125 4231933484414984197134797)
                      ·
                        rfl

theorem cell23_8241661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_8241661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241661 prefixEnd_8241661 := by exact prefixLift 8241661
  have htrace : WordTrace (prefixWord ++ tailWord_8241661) baseStart_8241661 baseEnd_8241661 := by
    simpa [prefixWord, tailWord_8241661, baseEnd_8241661] using wordTrace_append hprefix tailTrace_8241661
  have hstable : (prefixWord ++ tailWord_8241661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241661).length < 2 ^ (prefixWord ++ tailWord_8241661).sum := by decide
  have hdescent : baseEnd_8241661 < baseStart_8241661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241688 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_8241688 : Nat := 118140960795 + 8241688 * 2 ^ 59
def prefixEnd_8241688 : Nat := 4983230072969 + 3 ^ 40 * 8241688 * 2
def baseEnd_8241688 : Nat := 4231947348392655591497173

theorem tailTrace_8241688 : CollatzResearch.WordTrace tailWord_8241688 prefixEnd_8241688 4231947348392655591497173 := by
  unfold tailWord_8241688
  simp only [CollatzResearch.WordTrace]
  refine ⟨150299528282889709546638859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200399371043852946062185145 150299528282889709546638859)
  ·
    refine ⟨225449292424334564319958289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150299528282889709546638859 225449292424334564319958289)
    ·
      refine ⟨169086969318250923239968717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225449292424334564319958289 169086969318250923239968717)
      ·
        refine ⟨63407613494344096214988269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169086969318250923239968717 63407613494344096214988269)
        ·
          refine ⟨23777855060379036080620601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63407613494344096214988269 23777855060379036080620601)
          ·
            refine ⟨17833391295284277060465451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23777855060379036080620601 17833391295284277060465451)
            ·
              refine ⟨26750086942926415590698177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17833391295284277060465451 26750086942926415590698177)
              ·
                refine ⟨20062565207194811693023633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26750086942926415590698177 20062565207194811693023633)
                ·
                  refine ⟨15046923905396108769767725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20062565207194811693023633 15046923905396108769767725)
                  ·
                    refine ⟨5642596464523540788662897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15046923905396108769767725 5642596464523540788662897)
                    ·
                      refine ⟨4231947348392655591497173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642596464523540788662897 4231947348392655591497173)
                      ·
                        rfl

theorem cell23_8241688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_8241688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241688 prefixEnd_8241688 := by exact prefixLift 8241688
  have htrace : WordTrace (prefixWord ++ tailWord_8241688) baseStart_8241688 baseEnd_8241688 := by
    simpa [prefixWord, tailWord_8241688, baseEnd_8241688] using wordTrace_append hprefix tailTrace_8241688
  have hstable : (prefixWord ++ tailWord_8241688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241688).length < 2 ^ (prefixWord ++ tailWord_8241688).sum := by decide
  have hdescent : baseEnd_8241688 < baseStart_8241688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241714 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_8241714 : Nat := 118140960795 + 8241714 * 2 ^ 59
def prefixEnd_8241714 : Nat := 4983230072969 + 3 ^ 40 * 8241714 * 2
def baseEnd_8241714 : Nat := 4231960698889672489772053

theorem tailTrace_8241714 : CollatzResearch.WordTrace tailWord_8241714 prefixEnd_8241714 4231960698889672489772053 := by
  unfold tailWord_8241714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150001215921306383431049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200400003242456817022482797 75150001215921306383431049)
  ·
    refine ⟨56362500911940979787573287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75150001215921306383431049 56362500911940979787573287)
    ·
      refine ⟨84543751367911469681359931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56362500911940979787573287 84543751367911469681359931)
      ·
        refine ⟨126815627051867204522039897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84543751367911469681359931 126815627051867204522039897)
        ·
          refine ⟨95111720288900403391529923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126815627051867204522039897 95111720288900403391529923)
          ·
            refine ⟨142667580433350605087294885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95111720288900403391529923 142667580433350605087294885)
            ·
              refine ⟨26750171331253238453867791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142667580433350605087294885 26750171331253238453867791)
              ·
                refine ⟨40125256996879857680801687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26750171331253238453867791 40125256996879857680801687)
                ·
                  refine ⟨60187885495319786521202531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40125256996879857680801687 60187885495319786521202531)
                  ·
                    refine ⟨90281828242979679781803797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60187885495319786521202531 90281828242979679781803797)
                    ·
                      refine ⟨4231960698889672489772053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90281828242979679781803797 4231960698889672489772053)
                      ·
                        rfl

theorem cell23_8241714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_8241714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241714 prefixEnd_8241714 := by exact prefixLift 8241714
  have htrace : WordTrace (prefixWord ++ tailWord_8241714) baseStart_8241714 baseEnd_8241714 := by
    simpa [prefixWord, tailWord_8241714, baseEnd_8241714] using wordTrace_append hprefix tailTrace_8241714
  have hstable : (prefixWord ++ tailWord_8241714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241714).length < 2 ^ (prefixWord ++ tailWord_8241714).sum := by decide
  have hdescent : baseEnd_8241714 < baseStart_8241714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241718 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_8241718 : Nat := 118140960795 + 8241718 * 2 ^ 59
def prefixEnd_8241718 : Nat := 4983230072969 + 3 ^ 40 * 8241718 * 2
def baseEnd_8241718 : Nat := 4231962752812290474122035

theorem tailTrace_8241718 : CollatzResearch.WordTrace tailWord_8241718 prefixEnd_8241718 4231962752812290474122035 := by
  unfold tailWord_8241718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787509422229420888554363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200400100503780489477913205 18787509422229420888554363)
  ·
    refine ⟨28181264133344131332831545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787509422229420888554363 28181264133344131332831545)
    ·
      refine ⟨21135948100008098499623659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28181264133344131332831545 21135948100008098499623659)
      ·
        refine ⟨31703922150012147749435489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135948100008098499623659 31703922150012147749435489)
        ·
          refine ⟨23777941612509110812076617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31703922150012147749435489 23777941612509110812076617)
          ·
            refine ⟨17833456209381833109057463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23777941612509110812076617 17833456209381833109057463)
            ·
              refine ⟨26750184314072749663586195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17833456209381833109057463 26750184314072749663586195)
              ·
                refine ⟨40125276471109124495379293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26750184314072749663586195 40125276471109124495379293)
                ·
                  refine ⟨15046978676665921685767235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40125276471109124495379293 15046978676665921685767235)
                  ·
                    refine ⟨22570468014998882528650853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15046978676665921685767235 22570468014998882528650853)
                    ·
                      refine ⟨4231962752812290474122035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22570468014998882528650853 4231962752812290474122035)
                      ·
                        rfl

theorem cell23_8241718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_8241718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241718 prefixEnd_8241718 := by exact prefixLift 8241718
  have htrace : WordTrace (prefixWord ++ tailWord_8241718) baseStart_8241718 baseEnd_8241718 := by
    simpa [prefixWord, tailWord_8241718, baseEnd_8241718] using wordTrace_append hprefix tailTrace_8241718
  have hstable : (prefixWord ++ tailWord_8241718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241718).length < 2 ^ (prefixWord ++ tailWord_8241718).sum := by decide
  have hdescent : baseEnd_8241718 < baseStart_8241718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241721 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_8241721 : Nat := 118140960795 + 8241721 * 2 ^ 59
def prefixEnd_8241721 : Nat := 4983230072969 + 3 ^ 40 * 8241721 * 2
def baseEnd_8241721 : Nat := 4231964293254253962384521

theorem tailTrace_8241721 : CollatzResearch.WordTrace tailWord_8241721 prefixEnd_8241721 4231964293254253962384521 := by
  unfold tailWord_8241721
  simp only [CollatzResearch.WordTrace]
  refine ⟨300600260174659865729229017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200400173449773243819486011 300600260174659865729229017)
  ·
    refine ⟨225450195130994899296921763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300600260174659865729229017 225450195130994899296921763)
    ·
      refine ⟨338175292696492348945382645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225450195130994899296921763 338175292696492348945382645)
      ·
        refine ⟨31703933690296157713629623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338175292696492348945382645 31703933690296157713629623)
        ·
          refine ⟨47555900535444236570444435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31703933690296157713629623 47555900535444236570444435)
          ·
            refine ⟨71333850803166354855666653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47555900535444236570444435 71333850803166354855666653)
            ·
              refine ⟨26750194051187383070874995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71333850803166354855666653 26750194051187383070874995)
              ·
                refine ⟨40125291076781074606312493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26750194051187383070874995 40125291076781074606312493)
                ·
                  refine ⟨15046984153792902977367185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40125291076781074606312493 15046984153792902977367185)
                  ·
                    refine ⟨11285238115344677233025389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15046984153792902977367185 11285238115344677233025389)
                    ·
                      refine ⟨4231964293254253962384521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285238115344677233025389 4231964293254253962384521)
                      ·
                        rfl

theorem cell23_8241721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_8241721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241721 prefixEnd_8241721 := by exact prefixLift 8241721
  have htrace : WordTrace (prefixWord ++ tailWord_8241721) baseStart_8241721 baseEnd_8241721 := by
    simpa [prefixWord, tailWord_8241721, baseEnd_8241721] using wordTrace_append hprefix tailTrace_8241721
  have hstable : (prefixWord ++ tailWord_8241721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241721).length < 2 ^ (prefixWord ++ tailWord_8241721).sum := by decide
  have hdescent : baseEnd_8241721 < baseStart_8241721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241724 : List Nat := [2, 2, 2, 2, 3, 1, 2, 9]
def baseStart_8241724 : Nat := 118140960795 + 8241724 * 2 ^ 59
def prefixEnd_8241724 : Nat := 4983230072969 + 3 ^ 40 * 8241724 * 2
def baseEnd_8241724 : Nat := 156739475322082127801741

theorem tailTrace_8241724 : CollatzResearch.WordTrace tailWord_8241724 prefixEnd_8241724 156739475322082127801741 := by
  unfold tailWord_8241724
  simp only [CollatzResearch.WordTrace]
  refine ⟨150300184796824498620794113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200400246395765998161058817 150300184796824498620794113)
  ·
    refine ⟨112725138597618373965595585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150300184796824498620794113 112725138597618373965595585)
    ·
      refine ⟨84543853948213780474196689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112725138597618373965595585 84543853948213780474196689)
      ·
        refine ⟨63407890461160335355647517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84543853948213780474196689 63407890461160335355647517)
        ·
          refine ⟨23777958922935125758367819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63407890461160335355647517 23777958922935125758367819)
          ·
            refine ⟨35666938384402688637551729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23777958922935125758367819 35666938384402688637551729)
            ·
              refine ⟨26750203788302016478163797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35666938384402688637551729 26750203788302016478163797)
              ·
                refine ⟨156739475322082127801741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26750203788302016478163797 156739475322082127801741)
                ·
                  rfl

theorem cell23_8241724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 9].length) (baseStart_8241724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241724 prefixEnd_8241724 := by exact prefixLift 8241724
  have htrace : WordTrace (prefixWord ++ tailWord_8241724) baseStart_8241724 baseEnd_8241724 := by
    simpa [prefixWord, tailWord_8241724, baseEnd_8241724] using wordTrace_append hprefix tailTrace_8241724
  have hstable : (prefixWord ++ tailWord_8241724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241724).length < 2 ^ (prefixWord ++ tailWord_8241724).sum := by decide
  have hdescent : baseEnd_8241724 < baseStart_8241724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241752 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_8241752 : Nat := 118140960795 + 8241752 * 2 ^ 59
def prefixEnd_8241752 : Nat := 4983230072969 + 3 ^ 40 * 8241752 * 2
def baseEnd_8241752 : Nat := 4231980211154543341096879

theorem tailTrace_8241752 : CollatzResearch.WordTrace tailWord_8241752 prefixEnd_8241752 4231980211154543341096879 := by
  unfold tailWord_8241752
  simp only [CollatzResearch.WordTrace]
  refine ⟨150300695418773779011803755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200400927225031705349071673 150300695418773779011803755)
  ·
    refine ⟨225451043128160668517705633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150300695418773779011803755 225451043128160668517705633)
    ·
      refine ⟨169088282346120501388279225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225451043128160668517705633 169088282346120501388279225)
      ·
        refine ⟨126816211759590376041209419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169088282346120501388279225 126816211759590376041209419)
        ·
          refine ⟨190224317639385564061814129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126816211759590376041209419 190224317639385564061814129)
          ·
            refine ⟨142668238229539173046360597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190224317639385564061814129 142668238229539173046360597)
            ·
              refine ⟨6687573667009648736548153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142668238229539173046360597 6687573667009648736548153)
              ·
                refine ⟨5015680250257236552411115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687573667009648736548153 5015680250257236552411115)
                ·
                  refine ⟨7523520375385854828616673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015680250257236552411115 7523520375385854828616673)
                  ·
                    refine ⟨5642640281539391121462505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523520375385854828616673 5642640281539391121462505)
                    ·
                      refine ⟨4231980211154543341096879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642640281539391121462505 4231980211154543341096879)
                      ·
                        rfl

theorem cell23_8241752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_8241752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241752 prefixEnd_8241752 := by exact prefixLift 8241752
  have htrace : WordTrace (prefixWord ++ tailWord_8241752) baseStart_8241752 baseEnd_8241752 := by
    simpa [prefixWord, tailWord_8241752, baseEnd_8241752] using wordTrace_append hprefix tailTrace_8241752
  have hstable : (prefixWord ++ tailWord_8241752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241752).length < 2 ^ (prefixWord ++ tailWord_8241752).sum := by decide
  have hdescent : baseEnd_8241752 < baseStart_8241752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241791 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 4, 2]
def baseStart_8241791 : Nat := 118140960795 + 8241791 * 2 ^ 59
def prefixEnd_8241791 : Nat := 4983230072969 + 3 ^ 40 * 8241791 * 2
def baseEnd_8241791 : Nat := 4232000236900068688509199

theorem tailTrace_8241791 : CollatzResearch.WordTrace tailWord_8241791 prefixEnd_8241791 4232000236900068688509199 := by
  unfold tailWord_8241791
  simp only [CollatzResearch.WordTrace]
  refine ⟨300602813284406267684277227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200401875522937511789518151 300602813284406267684277227)
  ·
    refine ⟨450904219926609401526415841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300602813284406267684277227 450904219926609401526415841)
    ·
      refine ⟨338178164944957051144811881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450904219926609401526415841 338178164944957051144811881)
      ·
        refine ⟨253633623708717788358608911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338178164944957051144811881 253633623708717788358608911)
        ·
          refine ⟨380450435563076682537913367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253633623708717788358608911 380450435563076682537913367)
          ·
            refine ⟨570675653344615023806870051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380450435563076682537913367 570675653344615023806870051)
            ·
              refine ⟨856013480016922535710305077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570675653344615023806870051 856013480016922535710305077)
              ·
                refine ⟨80251263751586487722841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856013480016922535710305077 80251263751586487722841101)
                ·
                  refine ⟨30094223906844932896065413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80251263751586487722841101 30094223906844932896065413)
                  ·
                    refine ⟨5642666982533424918012265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30094223906844932896065413 5642666982533424918012265)
                    ·
                      refine ⟨4232000236900068688509199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642666982533424918012265 4232000236900068688509199)
                      ·
                        rfl

theorem cell23_8241791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_8241791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241791 prefixEnd_8241791 := by exact prefixLift 8241791
  have htrace : WordTrace (prefixWord ++ tailWord_8241791) baseStart_8241791 baseEnd_8241791 := by
    simpa [prefixWord, tailWord_8241791, baseEnd_8241791] using wordTrace_append hprefix tailTrace_8241791
  have hstable : (prefixWord ++ tailWord_8241791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241791).length < 2 ^ (prefixWord ++ tailWord_8241791).sum := by decide
  have hdescent : baseEnd_8241791 < baseStart_8241791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241795 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 1, 3, 2]
def baseStart_8241795 : Nat := 118140960795 + 8241795 * 2 ^ 59
def prefixEnd_8241795 : Nat := 4983230072969 + 3 ^ 40 * 8241795 * 2
def baseEnd_8241795 : Nat := 4232002290822686672859181

theorem tailTrace_8241795 : CollatzResearch.WordTrace tailWord_8241795 prefixEnd_8241795 4232002290822686672859181 := by
  unfold tailWord_8241795
  simp only [CollatzResearch.WordTrace]
  refine ⟨300602959176391776367422839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200401972784261184244948559 300602959176391776367422839)
  ·
    refine ⟨450904438764587664551134259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300602959176391776367422839 450904438764587664551134259)
    ·
      refine ⟨676356658146881496826701389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450904438764587664551134259 676356658146881496826701389)
      ·
        refine ⟨253633746805080561310013021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676356658146881496826701389 253633746805080561310013021)
        ·
          refine ⟨95112655051905210491254883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253633746805080561310013021 95112655051905210491254883)
          ·
            refine ⟨142668982577857815736882325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95112655051905210491254883 142668982577857815736882325)
            ·
              refine ⟨6687608558337085112666359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142668982577857815736882325 6687608558337085112666359)
              ·
                refine ⟨10031412837505627668999539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687608558337085112666359 10031412837505627668999539)
                ·
                  refine ⟨15047119256258441503499309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10031412837505627668999539 15047119256258441503499309)
                  ·
                    refine ⟨5642669721096915563812241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15047119256258441503499309 5642669721096915563812241)
                    ·
                      refine ⟨4232002290822686672859181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642669721096915563812241 4232002290822686672859181)
                      ·
                        rfl

theorem cell23_8241795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_8241795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241795 prefixEnd_8241795 := by exact prefixLift 8241795
  have htrace : WordTrace (prefixWord ++ tailWord_8241795) baseStart_8241795 baseEnd_8241795 := by
    simpa [prefixWord, tailWord_8241795, baseEnd_8241795] using wordTrace_append hprefix tailTrace_8241795
  have hstable : (prefixWord ++ tailWord_8241795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241795).length < 2 ^ (prefixWord ++ tailWord_8241795).sum := by decide
  have hdescent : baseEnd_8241795 < baseStart_8241795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241802 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_8241802 : Nat := 118140960795 + 8241802 * 2 ^ 59
def prefixEnd_8241802 : Nat := 4983230072969 + 3 ^ 40 * 8241802 * 2
def baseEnd_8241802 : Nat := 4232005885187268145471649

theorem tailTrace_8241802 : CollatzResearch.WordTrace tailWord_8241802 prefixEnd_8241802 4232005885187268145471649 := by
  unfold tailWord_8241802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150803621841604140731915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200402142991577611041951773 75150803621841604140731915)
  ·
    refine ⟨112726205432762406211097873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75150803621841604140731915 112726205432762406211097873)
    ·
      refine ⟨84544654074571804658323405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112726205432762406211097873 84544654074571804658323405)
      ·
        refine ⟨31704245277964426746871277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84544654074571804658323405 31704245277964426746871277)
        ·
          refine ⟨11889091979236660030076729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31704245277964426746871277 11889091979236660030076729)
          ·
            refine ⟨8916818984427495022557547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11889091979236660030076729 8916818984427495022557547)
            ·
              refine ⟨13375228476641242533836321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916818984427495022557547 13375228476641242533836321)
              ·
                refine ⟨10031421357480931900377241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13375228476641242533836321 10031421357480931900377241)
                ·
                  refine ⟨7523566018110698925282931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031421357480931900377241 7523566018110698925282931)
                  ·
                    refine ⟨11285349027166048387924397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7523566018110698925282931 11285349027166048387924397)
                    ·
                      refine ⟨4232005885187268145471649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285349027166048387924397 4232005885187268145471649)
                      ·
                        rfl

theorem cell23_8241802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_8241802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241802 prefixEnd_8241802 := by exact prefixLift 8241802
  have htrace : WordTrace (prefixWord ++ tailWord_8241802) baseStart_8241802 baseEnd_8241802 := by
    simpa [prefixWord, tailWord_8241802, baseEnd_8241802] using wordTrace_append hprefix tailTrace_8241802
  have hstable : (prefixWord ++ tailWord_8241802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241802).length < 2 ^ (prefixWord ++ tailWord_8241802).sum := by decide
  have hdescent : baseEnd_8241802 < baseStart_8241802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241821 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_8241821 : Nat := 118140960795 + 8241821 * 2 ^ 59
def prefixEnd_8241821 : Nat := 4983230072969 + 3 ^ 40 * 8241821 * 2
def baseEnd_8241821 : Nat := 4232015641319703571134061

theorem tailTrace_8241821 : CollatzResearch.WordTrace tailWord_8241821 prefixEnd_8241821 4232015641319703571134061 := by
  unfold tailWord_8241821
  simp only [CollatzResearch.WordTrace]
  refine ⟨300603907474297582807869317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200402604982865055205246211 300603907474297582807869317)
  ·
    refine ⟨56363232651430796776475497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300603907474297582807869317 56363232651430796776475497)
    ·
      refine ⟨42272424488573097582356623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56363232651430796776475497 42272424488573097582356623)
      ·
        refine ⟨63408636732859646373534935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42272424488573097582356623 63408636732859646373534935)
        ·
          refine ⟨95112955099289469560302403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63408636732859646373534935 95112955099289469560302403)
          ·
            refine ⟨142669432648934204340453605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95112955099289469560302403 142669432648934204340453605)
            ·
              refine ⟨26750518621675163313835051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142669432648934204340453605 26750518621675163313835051)
              ·
                refine ⟨40125777932512744970752577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26750518621675163313835051 40125777932512744970752577)
                ·
                  refine ⟨30094333449384558728064433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40125777932512744970752577 30094333449384558728064433)
                  ·
                    refine ⟨22570750087038419046048325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30094333449384558728064433 22570750087038419046048325)
                    ·
                      refine ⟨4232015641319703571134061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22570750087038419046048325 4232015641319703571134061)
                      ·
                        rfl

theorem cell23_8241821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_8241821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241821 prefixEnd_8241821 := by exact prefixLift 8241821
  have htrace : WordTrace (prefixWord ++ tailWord_8241821) baseStart_8241821 baseEnd_8241821 := by
    simpa [prefixWord, tailWord_8241821, baseEnd_8241821] using wordTrace_append hprefix tailTrace_8241821
  have hstable : (prefixWord ++ tailWord_8241821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241821).length < 2 ^ (prefixWord ++ tailWord_8241821).sum := by decide
  have hdescent : baseEnd_8241821 < baseStart_8241821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241851 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 7, 2]
def baseStart_8241851 : Nat := 118140960795 + 8241851 * 2 ^ 59
def prefixEnd_8241851 : Nat := 4983230072969 + 3 ^ 40 * 8241851 * 2
def baseEnd_8241851 : Nat := 4232031045739338453758923

theorem tailTrace_8241851 : CollatzResearch.WordTrace tailWord_8241851 prefixEnd_8241851 4232031045739338453758923 := by
  unfold tailWord_8241851
  simp only [CollatzResearch.WordTrace]
  refine ⟨300605001664188897931461407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200403334442792598620974271 300605001664188897931461407)
  ·
    refine ⟨450907502496283346897192111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300605001664188897931461407 450907502496283346897192111)
    ·
      refine ⟨676361253744425020345788167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450907502496283346897192111 676361253744425020345788167)
      ·
        refine ⟨1014541880616637530518682251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676361253744425020345788167 1014541880616637530518682251)
        ·
          refine ⟨1521812820924956295778023377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014541880616637530518682251 1521812820924956295778023377)
          ·
            refine ⟨1141359615693717221833517533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521812820924956295778023377 1141359615693717221833517533)
            ·
              refine ⟨428009855885143958187569075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141359615693717221833517533 428009855885143958187569075)
              ·
                refine ⟨642014783827715937281353613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428009855885143958187569075 642014783827715937281353613)
                ·
                  refine ⟨240755543935393476480507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642014783827715937281353613 240755543935393476480507605)
                  ·
                    refine ⟨5642708060985784605011897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240755543935393476480507605 5642708060985784605011897)
                    ·
                      refine ⟨4232031045739338453758923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642708060985784605011897 4232031045739338453758923)
                      ·
                        rfl

theorem cell23_8241851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7, 2].length) (baseStart_8241851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241851 prefixEnd_8241851 := by exact prefixLift 8241851
  have htrace : WordTrace (prefixWord ++ tailWord_8241851) baseStart_8241851 baseEnd_8241851 := by
    simpa [prefixWord, tailWord_8241851, baseEnd_8241851] using wordTrace_append hprefix tailTrace_8241851
  have hstable : (prefixWord ++ tailWord_8241851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241851).length < 2 ^ (prefixWord ++ tailWord_8241851).sum := by decide
  have hdescent : baseEnd_8241851 < baseStart_8241851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241876 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_8241876 : Nat := 118140960795 + 8241876 * 2 ^ 59
def prefixEnd_8241876 : Nat := 4983230072969 + 3 ^ 40 * 8241876 * 2
def baseEnd_8241876 : Nat := 4232043882755700855946309

theorem tailTrace_8241876 : CollatzResearch.WordTrace tailWord_8241876 prefixEnd_8241876 4232043882755700855946309 := by
  unfold tailWord_8241876
  simp only [CollatzResearch.WordTrace]
  refine ⟨150302956744549163600560741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200403942326065551467414321 150302956744549163600560741)
  ·
    refine ⟨28181804389602968175105139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150302956744549163600560741 28181804389602968175105139)
    ·
      refine ⟨42272706584404452262657709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28181804389602968175105139 42272706584404452262657709)
      ·
        refine ⟨15852264969151669598496641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42272706584404452262657709 15852264969151669598496641)
        ·
          refine ⟨11889198726863752198872481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15852264969151669598496641 11889198726863752198872481)
          ·
            refine ⟨8916899045147814149154361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11889198726863752198872481 8916899045147814149154361)
            ·
              refine ⟨6687674283860860611865771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916899045147814149154361 6687674283860860611865771)
              ·
                refine ⟨10031511425791290917798657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687674283860860611865771 10031511425791290917798657)
                ·
                  refine ⟨7523633569343468188348993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031511425791290917798657 7523633569343468188348993)
                  ·
                    refine ⟨5642725177007601141261745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523633569343468188348993 5642725177007601141261745)
                    ·
                      refine ⟨4232043882755700855946309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642725177007601141261745 4232043882755700855946309)
                      ·
                        rfl

theorem cell23_8241876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_8241876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241876 prefixEnd_8241876 := by exact prefixLift 8241876
  have htrace : WordTrace (prefixWord ++ tailWord_8241876) baseStart_8241876 baseEnd_8241876 := by
    simpa [prefixWord, tailWord_8241876, baseEnd_8241876] using wordTrace_append hprefix tailTrace_8241876
  have hstable : (prefixWord ++ tailWord_8241876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241876).length < 2 ^ (prefixWord ++ tailWord_8241876).sum := by decide
  have hdescent : baseEnd_8241876 < baseStart_8241876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241881 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_8241881 : Nat := 118140960795 + 8241881 * 2 ^ 59
def prefixEnd_8241881 : Nat := 4983230072969 + 3 ^ 40 * 8241881 * 2
def baseEnd_8241881 : Nat := 4232046450158973336383785

theorem tailTrace_8241881 : CollatzResearch.WordTrace tailWord_8241881 prefixEnd_8241881 4232046450158973336383785 := by
  unfold tailWord_8241881
  simp only [CollatzResearch.WordTrace]
  refine ⟨300606095854080213055053497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200404063902720142036702331 300606095854080213055053497)
  ·
    refine ⟨225454571890560159791290123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300606095854080213055053497 225454571890560159791290123)
    ·
      refine ⟨338181857835840239686935185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225454571890560159791290123 338181857835840239686935185)
      ·
        refine ⟨253636393376880179765201389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338181857835840239686935185 253636393376880179765201389)
        ·
          refine ⟨95113647516330067411950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253636393376880179765201389 95113647516330067411950521)
          ·
            refine ⟨71335235637247550558962891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95113647516330067411950521 71335235637247550558962891)
            ·
              refine ⟨107002853455871325838444337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71335235637247550558962891 107002853455871325838444337)
              ·
                refine ⟨80252140091903494378833253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107002853455871325838444337 80252140091903494378833253)
                ·
                  refine ⟨15047276267231905196031235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80252140091903494378833253 15047276267231905196031235)
                  ·
                    refine ⟨22570914400847857794046853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15047276267231905196031235 22570914400847857794046853)
                    ·
                      refine ⟨4232046450158973336383785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22570914400847857794046853 4232046450158973336383785)
                      ·
                        rfl

theorem cell23_8241881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_8241881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241881 prefixEnd_8241881 := by exact prefixLift 8241881
  have htrace : WordTrace (prefixWord ++ tailWord_8241881) baseStart_8241881 baseEnd_8241881 := by
    simpa [prefixWord, tailWord_8241881, baseEnd_8241881] using wordTrace_append hprefix tailTrace_8241881
  have hstable : (prefixWord ++ tailWord_8241881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241881).length < 2 ^ (prefixWord ++ tailWord_8241881).sum := by decide
  have hdescent : baseEnd_8241881 < baseStart_8241881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241898 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_8241898 : Nat := 118140960795 + 8241898 * 2 ^ 59
def prefixEnd_8241898 : Nat := 4983230072969 + 3 ^ 40 * 8241898 * 2
def baseEnd_8241898 : Nat := 4232055179330099769871207

theorem tailTrace_8241898 : CollatzResearch.WordTrace tailWord_8241898 prefixEnd_8241898 4232055179330099769871207 := by
  unfold tailWord_8241898
  simp only [CollatzResearch.WordTrace]
  refine ⟨75151678973754656239605587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200404477263345749972281565 75151678973754656239605587)
  ·
    refine ⟨112727518460631984359408381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75151678973754656239605587 112727518460631984359408381)
    ·
      refine ⟨42272819422736994134778143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112727518460631984359408381 42272819422736994134778143)
      ·
        refine ⟨63409229134105491202167215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42272819422736994134778143 63409229134105491202167215)
        ·
          refine ⟨95113843701158236803250823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63409229134105491202167215 95113843701158236803250823)
          ·
            refine ⟨142670765551737355204876235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95113843701158236803250823 142670765551737355204876235)
            ·
              refine ⟨214006148327606032807314353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142670765551737355204876235 214006148327606032807314353)
              ·
                refine ⟨160504611245704524605485765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214006148327606032807314353 160504611245704524605485765)
                ·
                  refine ⟨30094614608569598363528581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160504611245704524605485765 30094614608569598363528581)
                  ·
                    refine ⟨5642740239106799693161609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30094614608569598363528581 5642740239106799693161609)
                    ·
                      refine ⟨4232055179330099769871207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642740239106799693161609 4232055179330099769871207)
                      ·
                        rfl

theorem cell23_8241898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_8241898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241898 prefixEnd_8241898 := by exact prefixLift 8241898
  have htrace : WordTrace (prefixWord ++ tailWord_8241898) baseStart_8241898 baseEnd_8241898 := by
    simpa [prefixWord, tailWord_8241898, baseEnd_8241898] using wordTrace_append hprefix tailTrace_8241898
  have hstable : (prefixWord ++ tailWord_8241898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241898).length < 2 ^ (prefixWord ++ tailWord_8241898).sum := by decide
  have hdescent : baseEnd_8241898 < baseStart_8241898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241931 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3]
def baseStart_8241931 : Nat := 118140960795 + 8241931 * 2 ^ 59
def prefixEnd_8241931 : Nat := 4983230072969 + 3 ^ 40 * 8241931 * 2
def baseEnd_8241931 : Nat := 4232072124191698140758555

theorem tailTrace_8241931 : CollatzResearch.WordTrace tailWord_8241931 prefixEnd_8241931 4232072124191698140758555 := by
  unfold tailWord_8241931
  simp only [CollatzResearch.WordTrace]
  refine ⟨300607919503899071594373647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200405279669266047729582431 300607919503899071594373647)
  ·
    refine ⟨450911879255848607391560471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300607919503899071594373647 450911879255848607391560471)
    ·
      refine ⟨676367818883772911087340707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450911879255848607391560471 676367818883772911087340707)
      ·
        refine ⟨1014551728325659366631011061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676367818883772911087340707 1014551728325659366631011061)
        ·
          refine ⟨95114224530530565621657287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1014551728325659366631011061 95114224530530565621657287)
          ·
            refine ⟨142671336795795848432485931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95114224530530565621657287 142671336795795848432485931)
            ·
              refine ⟨214007005193693772648728897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142671336795795848432485931 214007005193693772648728897)
              ·
                refine ⟨160505253895270329486546673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214007005193693772648728897 160505253895270329486546673)
                ·
                  refine ⟨120378940421452747114910005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160505253895270329486546673 120378940421452747114910005)
                  ·
                    refine ⟨11285525664511195042022813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120378940421452747114910005 11285525664511195042022813)
                    ·
                      refine ⟨4232072124191698140758555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285525664511195042022813 4232072124191698140758555)
                      ·
                        rfl

theorem cell23_8241931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].length) (baseStart_8241931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241931 prefixEnd_8241931 := by exact prefixLift 8241931
  have htrace : WordTrace (prefixWord ++ tailWord_8241931) baseStart_8241931 baseEnd_8241931 := by
    simpa [prefixWord, tailWord_8241931, baseEnd_8241931] using wordTrace_append hprefix tailTrace_8241931
  have hstable : (prefixWord ++ tailWord_8241931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241931).length < 2 ^ (prefixWord ++ tailWord_8241931).sum := by decide
  have hdescent : baseEnd_8241931 < baseStart_8241931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241949 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_8241949 : Nat := 118140960795 + 8241949 * 2 ^ 59
def prefixEnd_8241949 : Nat := 4983230072969 + 3 ^ 40 * 8241949 * 2
def baseEnd_8241949 : Nat := 4232081366843479070333473

theorem tailTrace_8241949 : CollatzResearch.WordTrace tailWord_8241949 prefixEnd_8241949 4232081366843479070333473 := by
  unfold tailWord_8241949
  simp only [CollatzResearch.WordTrace]
  refine ⟨300608576017833860668528901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200405717345222573779019267 300608576017833860668528901)
  ·
    refine ⟨56364108003343848875349169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300608576017833860668528901 56364108003343848875349169)
    ·
      refine ⟨42273081002507886656511877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56364108003343848875349169 42273081002507886656511877)
      ·
        refine ⟨7926202687970228748095977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42273081002507886656511877 7926202687970228748095977)
        ·
          refine ⟨5944652015977671561071983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926202687970228748095977 5944652015977671561071983)
          ·
            refine ⟨8916978023966507341607975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944652015977671561071983 8916978023966507341607975)
            ·
              refine ⟨13375467035949761012411963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916978023966507341607975 13375467035949761012411963)
              ·
                refine ⟨20063200553924641518617945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375467035949761012411963 20063200553924641518617945)
                ·
                  refine ⟨15047400415443481138963459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20063200553924641518617945 15047400415443481138963459)
                  ·
                    refine ⟨22571100623165221708445189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15047400415443481138963459 22571100623165221708445189)
                    ·
                      refine ⟨4232081366843479070333473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22571100623165221708445189 4232081366843479070333473)
                      ·
                        rfl

theorem cell23_8241949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_8241949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241949 prefixEnd_8241949 := by exact prefixLift 8241949
  have htrace : WordTrace (prefixWord ++ tailWord_8241949) baseStart_8241949 baseEnd_8241949 := by
    simpa [prefixWord, tailWord_8241949, baseEnd_8241949] using wordTrace_append hprefix tailTrace_8241949
  have hstable : (prefixWord ++ tailWord_8241949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241949).length < 2 ^ (prefixWord ++ tailWord_8241949).sum := by decide
  have hdescent : baseEnd_8241949 < baseStart_8241949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8241972 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 6]
def baseStart_8241972 : Nat := 118140960795 + 8241972 * 2 ^ 59
def prefixEnd_8241972 : Nat := 4983230072969 + 3 ^ 40 * 8241972 * 2
def baseEnd_8241972 : Nat := 470232575210948053371763

theorem tailTrace_8241972 : CollatzResearch.WordTrace tailWord_8241972 prefixEnd_8241972 470232575210948053371763 := by
  unfold tailWord_8241972
  simp only [CollatzResearch.WordTrace]
  refine ⟨150304707448375267798308085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200406276597833690397744113 150304707448375267798308085)
  ·
    refine ⟨14091066323285181356091383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150304707448375267798308085 14091066323285181356091383)
    ·
      refine ⟨21136599484927772034137075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091066323285181356091383 21136599484927772034137075)
      ·
        refine ⟨31704899227391658051205613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136599484927772034137075 31704899227391658051205613)
        ·
          refine ⟨11889337210271871769202105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31704899227391658051205613 11889337210271871769202105)
          ·
            refine ⟨8917002907703903826901579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11889337210271871769202105 8917002907703903826901579)
            ·
              refine ⟨13375504361555855740352369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917002907703903826901579 13375504361555855740352369)
              ·
                refine ⟨10031628271166891805264277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13375504361555855740352369 10031628271166891805264277)
                ·
                  refine ⟨470232575210948053371763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10031628271166891805264277 470232575210948053371763)
                  ·
                    rfl

theorem cell23_8241972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_8241972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8241972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8241972 prefixEnd_8241972 := by exact prefixLift 8241972
  have htrace : WordTrace (prefixWord ++ tailWord_8241972) baseStart_8241972 baseEnd_8241972 := by
    simpa [prefixWord, tailWord_8241972, baseEnd_8241972] using wordTrace_append hprefix tailTrace_8241972
  have hstable : (prefixWord ++ tailWord_8241972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8241972).length < 2 ^ (prefixWord ++ tailWord_8241972).sum := by decide
  have hdescent : baseEnd_8241972 < baseStart_8241972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8241972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242005 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_8242005 : Nat := 118140960795 + 8242005 * 2 ^ 59
def prefixEnd_8242005 : Nat := 4983230072969 + 3 ^ 40 * 8242005 * 2
def baseEnd_8242005 : Nat := 4232110121760130851233215

theorem tailTrace_8242005 : CollatzResearch.WordTrace tailWord_8242005 prefixEnd_8242005 4232110121760130851233215 := by
  unfold tailWord_8242005
  simp only [CollatzResearch.WordTrace]
  refine ⟨300610618505630982232567469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200407079003753988155044979 300610618505630982232567469)
  ·
    refine ⟨112728981939611618337212801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300610618505630982232567469 112728981939611618337212801)
    ·
      refine ⟨84546736454708713752909601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112728981939611618337212801 84546736454708713752909601)
      ·
        refine ⟨63410052341031535314682201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84546736454708713752909601 63410052341031535314682201)
        ·
          refine ⟨47557539255773651486011651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63410052341031535314682201 47557539255773651486011651)
          ·
            refine ⟨71336308883660477229017477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47557539255773651486011651 71336308883660477229017477)
            ·
              refine ⟨13375557915686339480440777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71336308883660477229017477 13375557915686339480440777)
              ·
                refine ⟨10031668436764754610330583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13375557915686339480440777 10031668436764754610330583)
                ·
                  refine ⟨15047502655147131915495875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10031668436764754610330583 15047502655147131915495875)
                  ·
                    refine ⟨22571253982720697873243813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15047502655147131915495875 22571253982720697873243813)
                    ·
                      refine ⟨4232110121760130851233215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22571253982720697873243813 4232110121760130851233215)
                      ·
                        rfl

theorem cell23_8242005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_8242005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242005 prefixEnd_8242005 := by exact prefixLift 8242005
  have htrace : WordTrace (prefixWord ++ tailWord_8242005) baseStart_8242005 baseEnd_8242005 := by
    simpa [prefixWord, tailWord_8242005, baseEnd_8242005] using wordTrace_append hprefix tailTrace_8242005
  have hstable : (prefixWord ++ tailWord_8242005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242005).length < 2 ^ (prefixWord ++ tailWord_8242005).sum := by decide
  have hdescent : baseEnd_8242005 < baseStart_8242005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242008 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_8242008 : Nat := 118140960795 + 8242008 * 2 ^ 59
def prefixEnd_8242008 : Nat := 4983230072969 + 3 ^ 40 * 8242008 * 2
def baseEnd_8242008 : Nat := 4232111662202094339495701

theorem tailTrace_8242008 : CollatzResearch.WordTrace tailWord_8242008 prefixEnd_8242008 4232111662202094339495701 := by
  unfold tailWord_8242008
  simp only [CollatzResearch.WordTrace]
  refine ⟨150305363962310056872463339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200407151949746742496617785 150305363962310056872463339)
  ·
    refine ⟨225458045943465085308695009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150305363962310056872463339 225458045943465085308695009)
    ·
      refine ⟨169093534457598813981521257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225458045943465085308695009 169093534457598813981521257)
      ·
        refine ⟨126820150843199110486140943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169093534457598813981521257 126820150843199110486140943)
        ·
          refine ⟨190230226264798665729211415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126820150843199110486140943 190230226264798665729211415)
          ·
            refine ⟨285345339397197998593817123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190230226264798665729211415 285345339397197998593817123)
            ·
              refine ⟨428018009095796997890725685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285345339397197998593817123 428018009095796997890725685)
              ·
                refine ⟨40126688352730968552255533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428018009095796997890725685 40126688352730968552255533)
                ·
                  refine ⟨15047508132274113207095825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40126688352730968552255533 15047508132274113207095825)
                  ·
                    refine ⟨11285631099205584905321869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15047508132274113207095825 11285631099205584905321869)
                    ·
                      refine ⟨4232111662202094339495701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285631099205584905321869 4232111662202094339495701)
                      ·
                        rfl

theorem cell23_8242008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_8242008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242008 prefixEnd_8242008 := by exact prefixLift 8242008
  have htrace : WordTrace (prefixWord ++ tailWord_8242008) baseStart_8242008 baseEnd_8242008 := by
    simpa [prefixWord, tailWord_8242008, baseEnd_8242008] using wordTrace_append hprefix tailTrace_8242008
  have hstable : (prefixWord ++ tailWord_8242008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242008).length < 2 ^ (prefixWord ++ tailWord_8242008).sum := by decide
  have hdescent : baseEnd_8242008 < baseStart_8242008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242112 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2]
def baseStart_8242112 : Nat := 118140960795 + 8242112 * 2 ^ 59
def prefixEnd_8242112 : Nat := 4983230072969 + 3 ^ 40 * 8242112 * 2
def baseEnd_8242112 : Nat := 4232165064190161932595223

theorem tailTrace_8242112 : CollatzResearch.WordTrace tailWord_8242112 prefixEnd_8242112 4232165064190161932595223 := by
  unfold tailWord_8242112
  simp only [CollatzResearch.WordTrace]
  refine ⟨150307260558121669753356295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200409680744162226337808393 150307260558121669753356295)
  ·
    refine ⟨225460890837182504630034443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150307260558121669753356295 225460890837182504630034443)
    ·
      refine ⟨338191336255773756945051665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225460890837182504630034443 338191336255773756945051665)
      ·
        refine ⟨253643502191830317708788749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338191336255773756945051665 253643502191830317708788749)
        ·
          refine ⟨95116313321936369140795781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253643502191830317708788749 95116313321936369140795781)
          ·
            refine ⟨17834308747863069213899209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95116313321936369140795781 17834308747863069213899209)
            ·
              refine ⟨13375731560897301910424407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17834308747863069213899209 13375731560897301910424407)
              ·
                refine ⟨20063597341345952865636611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375731560897301910424407 20063597341345952865636611)
                ·
                  refine ⟨30095396012018929298454917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20063597341345952865636611 30095396012018929298454917)
                  ·
                    refine ⟨5642886752253549243460297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30095396012018929298454917 5642886752253549243460297)
                    ·
                      refine ⟨4232165064190161932595223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642886752253549243460297 4232165064190161932595223)
                      ·
                        rfl

theorem cell23_8242112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_8242112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242112 prefixEnd_8242112 := by exact prefixLift 8242112
  have htrace : WordTrace (prefixWord ++ tailWord_8242112) baseStart_8242112 baseEnd_8242112 := by
    simpa [prefixWord, tailWord_8242112, baseEnd_8242112] using wordTrace_append hprefix tailTrace_8242112
  have hstable : (prefixWord ++ tailWord_8242112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242112).length < 2 ^ (prefixWord ++ tailWord_8242112).sum := by decide
  have hdescent : baseEnd_8242112 < baseStart_8242112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242128 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_8242128 : Nat := 118140960795 + 8242128 * 2 ^ 59
def prefixEnd_8242128 : Nat := 4983230072969 + 3 ^ 40 * 8242128 * 2
def baseEnd_8242128 : Nat := 4232173279880633869995149

theorem tailTrace_8242128 : CollatzResearch.WordTrace tailWord_8242128 prefixEnd_8242128 4232173279880633869995149 := by
  unfold tailWord_8242128
  simp only [CollatzResearch.WordTrace]
  refine ⟨150307552342092687119647519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200410069789456916159530025 150307552342092687119647519)
  ·
    refine ⟨225461328513139030679471279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150307552342092687119647519 225461328513139030679471279)
    ·
      refine ⟨338191992769708546019206919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225461328513139030679471279 338191992769708546019206919)
      ·
        refine ⟨507287989154562819028810379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338191992769708546019206919 507287989154562819028810379)
        ·
          refine ⟨760931983731844228543215569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507287989154562819028810379 760931983731844228543215569)
          ·
            refine ⟨570698987798883171407411677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760931983731844228543215569 570698987798883171407411677)
            ·
              refine ⟨214012120424581189277779379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570698987798883171407411677 214012120424581189277779379)
              ·
                refine ⟨321018180636871783916669069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214012120424581189277779379 321018180636871783916669069)
                ·
                  refine ⟨120381817738826918968750901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321018180636871783916669069 120381817738826918968750901)
                  ·
                    refine ⟨11285795413015023653320397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120381817738826918968750901 11285795413015023653320397)
                    ·
                      refine ⟨4232173279880633869995149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285795413015023653320397 4232173279880633869995149)
                      ·
                        rfl

theorem cell23_8242128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_8242128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242128 prefixEnd_8242128 := by exact prefixLift 8242128
  have htrace : WordTrace (prefixWord ++ tailWord_8242128) baseStart_8242128 baseEnd_8242128 := by
    simpa [prefixWord, tailWord_8242128, baseEnd_8242128] using wordTrace_append hprefix tailTrace_8242128
  have hstable : (prefixWord ++ tailWord_8242128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242128).length < 2 ^ (prefixWord ++ tailWord_8242128).sum := by decide
  have hdescent : baseEnd_8242128 < baseStart_8242128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242133 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_8242133 : Nat := 118140960795 + 8242133 * 2 ^ 59
def prefixEnd_8242133 : Nat := 4983230072969 + 3 ^ 40 * 8242133 * 2
def baseEnd_8242133 : Nat := 4232175847283906350432627

theorem tailTrace_8242133 : CollatzResearch.WordTrace tailWord_8242133 prefixEnd_8242133 4232175847283906350432627 := by
  unfold tailWord_8242133
  simp only [CollatzResearch.WordTrace]
  refine ⟨300615287049167260093227053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200410191366111506728818035 300615287049167260093227053)
  ·
    refine ⟨112730732643437722534960145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300615287049167260093227053 112730732643437722534960145)
    ·
      refine ⟨84548049482578291901220109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112730732643437722534960145 84548049482578291901220109)
      ·
        refine ⟨31705518555966859462957541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84548049482578291901220109 31705518555966859462957541)
        ·
          refine ⟨5944784729243786149304539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31705518555966859462957541 5944784729243786149304539)
          ·
            refine ⟨8917177093865679223956809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944784729243786149304539 8917177093865679223956809)
            ·
              refine ⟨6687882820399259417967607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8917177093865679223956809 6687882820399259417967607)
              ·
                refine ⟨10031824230598889126951411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687882820399259417967607 10031824230598889126951411)
                ·
                  refine ⟨15047736345898333690427117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10031824230598889126951411 15047736345898333690427117)
                  ·
                    refine ⟨5642901129711875133910169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15047736345898333690427117 5642901129711875133910169)
                    ·
                      refine ⟨4232175847283906350432627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642901129711875133910169 4232175847283906350432627)
                      ·
                        rfl

theorem cell23_8242133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_8242133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242133 prefixEnd_8242133 := by exact prefixLift 8242133
  have htrace : WordTrace (prefixWord ++ tailWord_8242133) baseStart_8242133 baseEnd_8242133 := by
    simpa [prefixWord, tailWord_8242133, baseEnd_8242133] using wordTrace_append hprefix tailTrace_8242133
  have hstable : (prefixWord ++ tailWord_8242133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242133).length < 2 ^ (prefixWord ++ tailWord_8242133).sum := by decide
  have hdescent : baseEnd_8242133 < baseStart_8242133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242146 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_8242146 : Nat := 118140960795 + 8242146 * 2 ^ 59
def prefixEnd_8242146 : Nat := 4983230072969 + 3 ^ 40 * 8242146 * 2
def baseEnd_8242146 : Nat := 4232182522532414799570067

theorem tailTrace_8242146 : CollatzResearch.WordTrace tailWord_8242146 prefixEnd_8242146 4232182522532414799570067 := by
  unfold tailWord_8242146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75153940299530040828362573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200410507465413442208966861 75153940299530040828362573)
  ·
    refine ⟨28182727612323765310635965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75153940299530040828362573 28182727612323765310635965)
    ·
      refine ⟨10568522854621411991488487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28182727612323765310635965 10568522854621411991488487)
      ·
        refine ⟨15852784281932117987232731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568522854621411991488487 15852784281932117987232731)
        ·
          refine ⟨23779176422898176980849097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15852784281932117987232731 23779176422898176980849097)
          ·
            refine ⟨17834382317173632735636823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23779176422898176980849097 17834382317173632735636823)
            ·
              refine ⟨26751573475760449103455235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17834382317173632735636823 26751573475760449103455235)
              ·
                refine ⟨40127360213640673655182853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26751573475760449103455235 40127360213640673655182853)
                ·
                  refine ⟨7523880040057626310346785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40127360213640673655182853 7523880040057626310346785)
                  ·
                    refine ⟨5642910030043219732760089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523880040057626310346785 5642910030043219732760089)
                    ·
                      refine ⟨4232182522532414799570067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642910030043219732760089 4232182522532414799570067)
                      ·
                        rfl

theorem cell23_8242146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_8242146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242146 prefixEnd_8242146 := by exact prefixLift 8242146
  have htrace : WordTrace (prefixWord ++ tailWord_8242146) baseStart_8242146 baseEnd_8242146 := by
    simpa [prefixWord, tailWord_8242146, baseEnd_8242146] using wordTrace_append hprefix tailTrace_8242146
  have hstable : (prefixWord ++ tailWord_8242146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242146).length < 2 ^ (prefixWord ++ tailWord_8242146).sum := by decide
  have hdescent : baseEnd_8242146 < baseStart_8242146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242185 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 6, 2]
def baseStart_8242185 : Nat := 118140960795 + 8242185 * 2 ^ 59
def prefixEnd_8242185 : Nat := 4983230072969 + 3 ^ 40 * 8242185 * 2
def baseEnd_8242185 : Nat := 4232202548277940146982387

theorem tailTrace_8242185 : CollatzResearch.WordTrace tailWord_8242185 prefixEnd_8242185 4232202548277940146982387 := by
  unfold tailWord_8242185
  simp only [CollatzResearch.WordTrace]
  refine ⟨300617183644978872974120009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200411455763319248649413339 300617183644978872974120009)
  ·
    refine ⟨225462887733734154730590007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300617183644978872974120009 225462887733734154730590007)
    ·
      refine ⟨338194331600601232095885011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225462887733734154730590007 338194331600601232095885011)
      ·
        refine ⟨507291497400901848143827517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338194331600601232095885011 507291497400901848143827517)
        ·
          refine ⟨190234311525338193053935319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507291497400901848143827517 190234311525338193053935319)
          ·
            refine ⟨285351467288007289580902979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190234311525338193053935319 285351467288007289580902979)
            ·
              refine ⟨428027200932010934371354469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285351467288007289580902979 428027200932010934371354469)
              ·
                refine ⟨80255100174752050194628963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428027200932010934371354469 80255100174752050194628963)
                ·
                  refine ⟨120382650262128075291943445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80255100174752050194628963 120382650262128075291943445)
                  ·
                    refine ⟨5642936731037253529309849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120382650262128075291943445 5642936731037253529309849)
                    ·
                      refine ⟨4232202548277940146982387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5642936731037253529309849 4232202548277940146982387)
                      ·
                        rfl

theorem cell23_8242185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6, 2].length) (baseStart_8242185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242185 prefixEnd_8242185 := by exact prefixLift 8242185
  have htrace : WordTrace (prefixWord ++ tailWord_8242185) baseStart_8242185 baseEnd_8242185 := by
    simpa [prefixWord, tailWord_8242185, baseEnd_8242185] using wordTrace_append hprefix tailTrace_8242185
  have hstable : (prefixWord ++ tailWord_8242185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242185).length < 2 ^ (prefixWord ++ tailWord_8242185).sum := by decide
  have hdescent : baseEnd_8242185 < baseStart_8242185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242222 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_8242222 : Nat := 118140960795 + 8242222 * 2 ^ 59
def prefixEnd_8242222 : Nat := 4983230072969 + 3 ^ 40 * 8242222 * 2
def baseEnd_8242222 : Nat := 4232221547062156502219717

theorem tailTrace_8242222 : CollatzResearch.WordTrace tailWord_8242222 prefixEnd_8242222 4232221547062156502219717 := by
  unfold tailWord_8242222
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577316643230603536652115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200412355430563218862144613 37577316643230603536652115)
  ·
    refine ⟨56365974964845905304978173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37577316643230603536652115 56365974964845905304978173)
    ·
      refine ⟨21137240611817214489366815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56365974964845905304978173 21137240611817214489366815)
      ·
        refine ⟨31705860917725821734050223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21137240611817214489366815 31705860917725821734050223)
        ·
          refine ⟨47558791376588732601075335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31705860917725821734050223 47558791376588732601075335)
          ·
            refine ⟨71338187064883098901613003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47558791376588732601075335 71338187064883098901613003)
            ·
              refine ⟨107007280597324648352419505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71338187064883098901613003 107007280597324648352419505)
              ·
                refine ⟨80255460447993486264314629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107007280597324648352419505 80255460447993486264314629)
                ·
                  refine ⟨15047898833998778674558993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80255460447993486264314629 15047898833998778674558993)
                  ·
                    refine ⟨11285924125499084005919245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15047898833998778674558993 11285924125499084005919245)
                    ·
                      refine ⟨4232221547062156502219717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11285924125499084005919245 4232221547062156502219717)
                      ·
                        rfl

theorem cell23_8242222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_8242222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242222 prefixEnd_8242222 := by exact prefixLift 8242222
  have htrace : WordTrace (prefixWord ++ tailWord_8242222) baseStart_8242222 baseEnd_8242222 := by
    simpa [prefixWord, tailWord_8242222, baseEnd_8242222] using wordTrace_append hprefix tailTrace_8242222
  have hstable : (prefixWord ++ tailWord_8242222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242222).length < 2 ^ (prefixWord ++ tailWord_8242222).sum := by decide
  have hdescent : baseEnd_8242222 < baseStart_8242222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242225 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 6]
def baseStart_8242225 : Nat := 118140960795 + 8242225 * 2 ^ 59
def prefixEnd_8242225 : Nat := 4983230072969 + 3 ^ 40 * 8242225 * 2
def baseEnd_8242225 : Nat := 470247009722679998942467

theorem tailTrace_8242225 : CollatzResearch.WordTrace tailWord_8242225 prefixEnd_8242225 470247009722679998942467 := by
  unfold tailWord_8242225
  simp only [CollatzResearch.WordTrace]
  refine ⟨300618642564833959805576129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200412428376555973203717419 300618642564833959805576129)
  ·
    refine ⟨225463981923625469854182097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300618642564833959805576129 225463981923625469854182097)
    ·
      refine ⟨169097986442719102390636573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225463981923625469854182097 169097986442719102390636573)
      ·
        refine ⟨63411744916019663396488715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169097986442719102390636573 63411744916019663396488715)
        ·
          refine ⟨95117617374029495094733073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63411744916019663396488715 95117617374029495094733073)
          ·
            refine ⟨71338213030522121321049805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95117617374029495094733073 71338213030522121321049805)
            ·
              refine ⟨26751829886445795495393677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71338213030522121321049805 26751829886445795495393677)
              ·
                refine ⟨10031936207417173310772629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26751829886445795495393677 10031936207417173310772629)
                ·
                  refine ⟨470247009722679998942467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10031936207417173310772629 470247009722679998942467)
                  ·
                    rfl

theorem cell23_8242225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_8242225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242225 prefixEnd_8242225 := by exact prefixLift 8242225
  have htrace : WordTrace (prefixWord ++ tailWord_8242225) baseStart_8242225 baseEnd_8242225 := by
    simpa [prefixWord, tailWord_8242225, baseEnd_8242225] using wordTrace_append hprefix tailTrace_8242225
  have hstable : (prefixWord ++ tailWord_8242225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242225).length < 2 ^ (prefixWord ++ tailWord_8242225).sum := by decide
  have hdescent : baseEnd_8242225 < baseStart_8242225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242309 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_8242309 : Nat := 118140960795 + 8242309 * 2 ^ 59
def prefixEnd_8242309 : Nat := 4983230072969 + 3 ^ 40 * 8242309 * 2
def baseEnd_8242309 : Nat := 4232266219879097661831817

theorem tailTrace_8242309 : CollatzResearch.WordTrace tailWord_8242309 prefixEnd_8242309 4232266219879097661831817 := by
  unfold tailWord_8242309
  simp only [CollatzResearch.WordTrace]
  refine ⟨300621706296529642151633981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200414470864353094767755987 300621706296529642151633981)
  ·
    refine ⟨112733139861198615806862743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300621706296529642151633981 112733139861198615806862743)
    ·
      refine ⟨169099709791797923710294115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112733139861198615806862743 169099709791797923710294115)
      ·
        refine ⟨253649564687696885565441173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169099709791797923710294115 253649564687696885565441173)
        ·
          refine ⟨11889823344735791510880055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253649564687696885565441173 11889823344735791510880055)
          ·
            refine ⟨17834735017103687266320083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889823344735791510880055 17834735017103687266320083)
            ·
              refine ⟨26752102525655530899480125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17834735017103687266320083 26752102525655530899480125)
              ·
                refine ⟨10032038447120824087305047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26752102525655530899480125 10032038447120824087305047)
                ·
                  refine ⟨15048057670681236130957571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032038447120824087305047 15048057670681236130957571)
                  ·
                    refine ⟨22572086506021854196436357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15048057670681236130957571 22572086506021854196436357)
                    ·
                      refine ⟨4232266219879097661831817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22572086506021854196436357 4232266219879097661831817)
                      ·
                        rfl

theorem cell23_8242309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_8242309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242309 prefixEnd_8242309 := by exact prefixLift 8242309
  have htrace : WordTrace (prefixWord ++ tailWord_8242309) baseStart_8242309 baseEnd_8242309 := by
    simpa [prefixWord, tailWord_8242309, baseEnd_8242309] using wordTrace_append hprefix tailTrace_8242309
  have hstable : (prefixWord ++ tailWord_8242309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242309).length < 2 ^ (prefixWord ++ tailWord_8242309).sum := by decide
  have hdescent : baseEnd_8242309 < baseStart_8242309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242346 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_8242346 : Nat := 118140960795 + 8242346 * 2 ^ 59
def prefixEnd_8242346 : Nat := 4983230072969 + 3 ^ 40 * 8242346 * 2
def baseEnd_8242346 : Nat := 4232285218663314017069147

theorem tailTrace_8242346 : CollatzResearch.WordTrace tailWord_8242346 prefixEnd_8242346 4232285218663314017069147 := by
  unfold tailWord_8242346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155763949348899367682723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200415370531597064980487261 75155763949348899367682723)
  ·
    refine ⟨112733645924023349051524085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75155763949348899367682723 112733645924023349051524085)
    ·
      refine ⟨10568779305377188973580383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112733645924023349051524085 10568779305377188973580383)
      ·
        refine ⟨15853168958065783460370575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568779305377188973580383 15853168958065783460370575)
        ·
          refine ⟨23779753437098675190555863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15853168958065783460370575 23779753437098675190555863)
          ·
            refine ⟨35669630155648012785833795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23779753437098675190555863 35669630155648012785833795)
            ·
              refine ⟨53504445233472019178750693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35669630155648012785833795 53504445233472019178750693)
              ·
                refine ⟨10032083481276003596015755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53504445233472019178750693 10032083481276003596015755)
                ·
                  refine ⟨15048125221914005394023633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032083481276003596015755 15048125221914005394023633)
                  ·
                    refine ⟨11286093916435504045517725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15048125221914005394023633 11286093916435504045517725)
                    ·
                      refine ⟨4232285218663314017069147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286093916435504045517725 4232285218663314017069147)
                      ·
                        rfl

theorem cell23_8242346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_8242346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242346 prefixEnd_8242346 := by exact prefixLift 8242346
  have htrace : WordTrace (prefixWord ++ tailWord_8242346) baseStart_8242346 baseEnd_8242346 := by
    simpa [prefixWord, tailWord_8242346, baseEnd_8242346] using wordTrace_append hprefix tailTrace_8242346
  have hstable : (prefixWord ++ tailWord_8242346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242346).length < 2 ^ (prefixWord ++ tailWord_8242346).sum := by decide
  have hdescent : baseEnd_8242346 < baseStart_8242346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242355 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_8242355 : Nat := 118140960795 + 8242355 * 2 ^ 59
def prefixEnd_8242355 : Nat := 4983230072969 + 3 ^ 40 * 8242355 * 2
def baseEnd_8242355 : Nat := 4232289839989204481856605

theorem tailTrace_8242355 : CollatzResearch.WordTrace tailWord_8242355 prefixEnd_8242355 4232289839989204481856605 := by
  unfold tailWord_8242355
  simp only [CollatzResearch.WordTrace]
  refine ⟨300623384054362992007808519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200415589369575328005205679 300623384054362992007808519)
  ·
    refine ⟨450935076081544488011712779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300623384054362992007808519 450935076081544488011712779)
    ·
      refine ⟨676402614122316732017569169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450935076081544488011712779 676402614122316732017569169)
      ·
        refine ⟨507301960591737549013176877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676402614122316732017569169 507301960591737549013176877)
        ·
          refine ⟨190238235221901580879941329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507301960591737549013176877 190238235221901580879941329)
          ·
            refine ⟨142678676416426185659955997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190238235221901580879941329 142678676416426185659955997)
            ·
              refine ⟨53504503656159819622483499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142678676416426185659955997 53504503656159819622483499)
              ·
                refine ⟨80256755484239729433725249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53504503656159819622483499 80256755484239729433725249)
                ·
                  refine ⟨60192566613179797075293937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80256755484239729433725249 60192566613179797075293937)
                  ·
                    refine ⟨45144424959884847806470453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60192566613179797075293937 45144424959884847806470453)
                    ·
                      refine ⟨4232289839989204481856605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45144424959884847806470453 4232289839989204481856605)
                      ·
                        rfl

theorem cell23_8242355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_8242355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242355 prefixEnd_8242355 := by exact prefixLift 8242355
  have htrace : WordTrace (prefixWord ++ tailWord_8242355) baseStart_8242355 baseEnd_8242355 := by
    simpa [prefixWord, tailWord_8242355, baseEnd_8242355] using wordTrace_append hprefix tailTrace_8242355
  have hstable : (prefixWord ++ tailWord_8242355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242355).length < 2 ^ (prefixWord ++ tailWord_8242355).sum := by decide
  have hdescent : baseEnd_8242355 < baseStart_8242355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242375 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 6]
def baseStart_8242375 : Nat := 118140960795 + 8242375 * 2 ^ 59
def prefixEnd_8242375 : Nat := 4983230072969 + 3 ^ 40 * 8242375 * 2
def baseEnd_8242375 : Nat := 1410766703200764801202171

theorem tailTrace_8242375 : CollatzResearch.WordTrace tailWord_8242375 prefixEnd_8242375 1410766703200764801202171 := by
  unfold tailWord_8242375
  simp only [CollatzResearch.WordTrace]
  refine ⟨300624113514290535423536579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200416075676193690282357719 300624113514290535423536579)
  ·
    refine ⟨450936170271435803135304869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300624113514290535423536579 450936170271435803135304869)
    ·
      refine ⟨84550531925894213087869663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450936170271435803135304869 84550531925894213087869663)
      ·
        refine ⟨126825797888841319631804495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84550531925894213087869663 126825797888841319631804495)
        ·
          refine ⟨190238696833261979447706743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126825797888841319631804495 190238696833261979447706743)
          ·
            refine ⟨285358045249892969171560115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190238696833261979447706743 285358045249892969171560115)
            ·
              refine ⟨428037067874839453757340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285358045249892969171560115 428037067874839453757340173)
              ·
                refine ⟨160513900453064795159002565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428037067874839453757340173 160513900453064795159002565)
                ·
                  refine ⟨30096356334949649092312981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160513900453064795159002565 30096356334949649092312981)
                  ·
                    refine ⟨1410766703200764801202171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30096356334949649092312981 1410766703200764801202171)
                    ·
                      rfl

theorem cell23_8242375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_8242375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242375 prefixEnd_8242375 := by exact prefixLift 8242375
  have htrace : WordTrace (prefixWord ++ tailWord_8242375) baseStart_8242375 baseEnd_8242375 := by
    simpa [prefixWord, tailWord_8242375, baseEnd_8242375] using wordTrace_append hprefix tailTrace_8242375
  have hstable : (prefixWord ++ tailWord_8242375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242375).length < 2 ^ (prefixWord ++ tailWord_8242375).sum := by decide
  have hdescent : baseEnd_8242375 < baseStart_8242375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242385 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_8242385 : Nat := 118140960795 + 8242385 * 2 ^ 59
def prefixEnd_8242385 : Nat := 4983230072969 + 3 ^ 40 * 8242385 * 2
def baseEnd_8242385 : Nat := 4232305244408839364481467

theorem tailTrace_8242385 : CollatzResearch.WordTrace tailWord_8242385 prefixEnd_8242385 4232305244408839364481467 := by
  unfold tailWord_8242385
  simp only [CollatzResearch.WordTrace]
  refine ⟨300624478244254307131400609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200416318829502871420933739 300624478244254307131400609)
  ·
    refine ⟨225468358683190730348550457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300624478244254307131400609 225468358683190730348550457)
    ·
      refine ⟨169101269012393047761412843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225468358683190730348550457 169101269012393047761412843)
      ·
        refine ⟨253651903518589571642119265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169101269012393047761412843 253651903518589571642119265)
        ·
          refine ⟨190238927638942178731589449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253651903518589571642119265 190238927638942178731589449)
          ·
            refine ⟨142679195729206634048692087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190238927638942178731589449 142679195729206634048692087)
            ·
              refine ⟨214018793593809951073038131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142679195729206634048692087 214018793593809951073038131)
              ·
                refine ⟨321028190390714926609557197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214018793593809951073038131 321028190390714926609557197)
                ·
                  refine ⟨120385571396518097478583949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321028190390714926609557197 120385571396518097478583949)
                  ·
                    refine ⟨45144589273694286554468981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120385571396518097478583949 45144589273694286554468981)
                    ·
                      refine ⟨4232305244408839364481467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45144589273694286554468981 4232305244408839364481467)
                      ·
                        rfl

theorem cell23_8242385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_8242385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242385 prefixEnd_8242385 := by exact prefixLift 8242385
  have htrace : WordTrace (prefixWord ++ tailWord_8242385) baseStart_8242385 baseEnd_8242385 := by
    simpa [prefixWord, tailWord_8242385, baseEnd_8242385] using wordTrace_append hprefix tailTrace_8242385
  have hstable : (prefixWord ++ tailWord_8242385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242385).length < 2 ^ (prefixWord ++ tailWord_8242385).sum := by decide
  have hdescent : baseEnd_8242385 < baseStart_8242385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242432 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_8242432 : Nat := 118140960795 + 8242432 * 2 ^ 59
def prefixEnd_8242432 : Nat := 4983230072969 + 3 ^ 40 * 8242432 * 2
def baseEnd_8242432 : Nat := 4232329377999600680593751

theorem tailTrace_8242432 : CollatzResearch.WordTrace tailWord_8242432 prefixEnd_8242432 4232329377999600680593751 := by
  unfold tailWord_8242432
  simp only [CollatzResearch.WordTrace]
  refine ⟨150313096237542017079180775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200417461650056022772241033 150313096237542017079180775)
  ·
    refine ⟨225469644356313025618771163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150313096237542017079180775 225469644356313025618771163)
    ·
      refine ⟨338204466534469538428156745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225469644356313025618771163 338204466534469538428156745)
      ·
        refine ⟨253653349900852153821117559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338204466534469538428156745 253653349900852153821117559)
        ·
          refine ⟨380480024851278230731676339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253653349900852153821117559 380480024851278230731676339)
          ·
            refine ⟨570720037276917346097514509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380480024851278230731676339 570720037276917346097514509)
            ·
              refine ⟨214020013978844004786567941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570720037276917346097514509 214020013978844004786567941)
              ·
                refine ⟨40128752621033250897481489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214020013978844004786567941 40128752621033250897481489)
                ·
                  refine ⟨30096564465774938173111117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40128752621033250897481489 30096564465774938173111117)
                  ·
                    refine ⟨11286211674665601814916669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30096564465774938173111117 11286211674665601814916669)
                    ·
                      refine ⟨4232329377999600680593751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286211674665601814916669 4232329377999600680593751)
                      ·
                        rfl

theorem cell23_8242432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_8242432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242432 prefixEnd_8242432 := by exact prefixLift 8242432
  have htrace : WordTrace (prefixWord ++ tailWord_8242432) baseStart_8242432 baseEnd_8242432 := by
    simpa [prefixWord, tailWord_8242432, baseEnd_8242432] using wordTrace_append hprefix tailTrace_8242432
  have hstable : (prefixWord ++ tailWord_8242432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242432).length < 2 ^ (prefixWord ++ tailWord_8242432).sum := by decide
  have hdescent : baseEnd_8242432 < baseStart_8242432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242433 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_8242433 : Nat := 118140960795 + 8242433 * 2 ^ 59
def prefixEnd_8242433 : Nat := 4983230072969 + 3 ^ 40 * 8242433 * 2
def baseEnd_8242433 : Nat := 4232329891480255176681247

theorem tailTrace_8242433 : CollatzResearch.WordTrace tailWord_8242433 prefixEnd_8242433 4232329891480255176681247 := by
  unfold tailWord_8242433
  simp only [CollatzResearch.WordTrace]
  refine ⟨300626228948080411329147953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200417485965386940886098635 300626228948080411329147953)
  ·
    refine ⟨225469671711060308496860965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300626228948080411329147953 225469671711060308496860965)
    ·
      refine ⟨42275563445823807843161431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225469671711060308496860965 42275563445823807843161431)
      ·
        refine ⟨63413345168735711764742147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42275563445823807843161431 63413345168735711764742147)
        ·
          refine ⟨95120017753103567647113221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63413345168735711764742147 95120017753103567647113221)
          ·
            refine ⟨17835003328706918933833729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95120017753103567647113221 17835003328706918933833729)
            ·
              refine ⟨13376252496530189200375297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17835003328706918933833729 13376252496530189200375297)
              ·
                refine ⟨10032189372397641900281473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13376252496530189200375297 10032189372397641900281473)
                ·
                  refine ⟨7524142029298231425211105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032189372397641900281473 7524142029298231425211105)
                  ·
                    refine ⟨5643106521973673568908329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7524142029298231425211105 5643106521973673568908329)
                    ·
                      refine ⟨4232329891480255176681247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643106521973673568908329 4232329891480255176681247)
                      ·
                        rfl

theorem cell23_8242433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_8242433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242433 prefixEnd_8242433 := by exact prefixLift 8242433
  have htrace : WordTrace (prefixWord ++ tailWord_8242433) baseStart_8242433 baseEnd_8242433 := by
    simpa [prefixWord, tailWord_8242433, baseEnd_8242433] using wordTrace_append hprefix tailTrace_8242433
  have hstable : (prefixWord ++ tailWord_8242433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242433).length < 2 ^ (prefixWord ++ tailWord_8242433).sum := by decide
  have hdescent : baseEnd_8242433 < baseStart_8242433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242450 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8242450 : Nat := 118140960795 + 8242450 * 2 ^ 59
def prefixEnd_8242450 : Nat := 4983230072969 + 3 ^ 40 * 8242450 * 2
def baseEnd_8242450 : Nat := 4232338620651381610168669

theorem tailTrace_8242450 : CollatzResearch.WordTrace tailWord_8242450 prefixEnd_8242450 4232338620651381610168669 := by
  unfold tailWord_8242450
  simp only [CollatzResearch.WordTrace]
  refine ⟨75156712247254705808129201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200417899326012548821677869 75156712247254705808129201)
  ·
    refine ⟨56367534185441029356096901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75156712247254705808129201 56367534185441029356096901)
    ·
      refine ⟨10568912659770193004268169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56367534185441029356096901 10568912659770193004268169)
      ·
        refine ⟨7926684494827644753201127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10568912659770193004268169 7926684494827644753201127)
        ·
          refine ⟨11890026742241467129801691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926684494827644753201127 11890026742241467129801691)
          ·
            refine ⟨17835040113362200694702537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890026742241467129801691 17835040113362200694702537)
            ·
              refine ⟨13376280085021650521026903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17835040113362200694702537 13376280085021650521026903)
              ·
                refine ⟨20064420127532475781540355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13376280085021650521026903 20064420127532475781540355)
                ·
                  refine ⟨30096630191298713672310533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20064420127532475781540355 30096630191298713672310533)
                  ·
                    refine ⟨5643118160868508813558225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30096630191298713672310533 5643118160868508813558225)
                    ·
                      refine ⟨4232338620651381610168669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643118160868508813558225 4232338620651381610168669)
                      ·
                        rfl

theorem cell23_8242450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8242450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242450 prefixEnd_8242450 := by exact prefixLift 8242450
  have htrace : WordTrace (prefixWord ++ tailWord_8242450) baseStart_8242450 baseEnd_8242450 := by
    simpa [prefixWord, tailWord_8242450, baseEnd_8242450] using wordTrace_append hprefix tailTrace_8242450
  have hstable : (prefixWord ++ tailWord_8242450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242450).length < 2 ^ (prefixWord ++ tailWord_8242450).sum := by decide
  have hdescent : baseEnd_8242450 < baseStart_8242450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242469 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_8242469 : Nat := 118140960795 + 8242469 * 2 ^ 59
def prefixEnd_8242469 : Nat := 4983230072969 + 3 ^ 40 * 8242469 * 2
def baseEnd_8242469 : Nat := 1410782792261272345277027

theorem tailTrace_8242469 : CollatzResearch.WordTrace tailWord_8242469 prefixEnd_8242469 1410782792261272345277027 := by
  unfold tailWord_8242469
  simp only [CollatzResearch.WordTrace]
  refine ⟨300627541975949989477458461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200418361317299992984972307 300627541975949989477458461)
  ·
    refine ⟨112735328240981246054046923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300627541975949989477458461 112735328240981246054046923)
    ·
      refine ⟨169102992361471869081070385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112735328240981246054046923 169102992361471869081070385)
      ·
        refine ⟨126827244271103901810802789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169102992361471869081070385 126827244271103901810802789)
        ·
          refine ⟨23780108300831981589525523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126827244271103901810802789 23780108300831981589525523)
          ·
            refine ⟨35670162451247972384288285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23780108300831981589525523 35670162451247972384288285)
            ·
              refine ⟨13376310919217989644108107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35670162451247972384288285 13376310919217989644108107)
              ·
                refine ⟨20064466378826984466162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13376310919217989644108107 20064466378826984466162161)
                ·
                  refine ⟨15048349784120238349621621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20064466378826984466162161 15048349784120238349621621)
                  ·
                    refine ⟨1410782792261272345277027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15048349784120238349621621 1410782792261272345277027)
                    ·
                      rfl

theorem cell23_8242469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_8242469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242469 prefixEnd_8242469 := by exact prefixLift 8242469
  have htrace : WordTrace (prefixWord ++ tailWord_8242469) baseStart_8242469 baseEnd_8242469 := by
    simpa [prefixWord, tailWord_8242469, baseEnd_8242469] using wordTrace_append hprefix tailTrace_8242469
  have hstable : (prefixWord ++ tailWord_8242469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242469).length < 2 ^ (prefixWord ++ tailWord_8242469).sum := by decide
  have hdescent : baseEnd_8242469 < baseStart_8242469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242589 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_8242589 : Nat := 118140960795 + 8242589 * 2 ^ 59
def prefixEnd_8242589 : Nat := 4983230072969 + 3 ^ 40 * 8242589 * 2
def baseEnd_8242589 : Nat := 1410803331487452188776843

theorem tailTrace_8242589 : CollatzResearch.WordTrace tailWord_8242589 prefixEnd_8242589 1410803331487452188776843 := by
  unfold tailWord_8242589
  simp only [CollatzResearch.WordTrace]
  refine ⟨300631918735515249971826821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200421279157010166647884547 300631918735515249971826821)
  ·
    refine ⟨56368484762909109369717529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300631918735515249971826821 56368484762909109369717529)
    ·
      refine ⟨42276363572181832027288147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56368484762909109369717529 42276363572181832027288147)
      ·
        refine ⟨63414545358272748040932221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42276363572181832027288147 63414545358272748040932221)
        ·
          refine ⟨23780454509352280515349583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63414545358272748040932221 23780454509352280515349583)
          ·
            refine ⟨35670681764028420773024375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23780454509352280515349583 35670681764028420773024375)
            ·
              refine ⟨53506022646042631159536563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35670681764028420773024375 53506022646042631159536563)
              ·
                refine ⟨80259033969063946739304845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53506022646042631159536563 80259033969063946739304845)
                ·
                  refine ⟨30097137738398980027239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80259033969063946739304845 30097137738398980027239317)
                  ·
                    refine ⟨1410803331487452188776843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30097137738398980027239317 1410803331487452188776843)
                    ·
                      rfl

theorem cell23_8242589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_8242589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242589 prefixEnd_8242589 := by exact prefixLift 8242589
  have htrace : WordTrace (prefixWord ++ tailWord_8242589) baseStart_8242589 baseEnd_8242589 := by
    simpa [prefixWord, tailWord_8242589, baseEnd_8242589] using wordTrace_append hprefix tailTrace_8242589
  have hstable : (prefixWord ++ tailWord_8242589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242589).length < 2 ^ (prefixWord ++ tailWord_8242589).sum := by decide
  have hdescent : baseEnd_8242589 < baseStart_8242589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242609 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_8242609 : Nat := 118140960795 + 8242609 * 2 ^ 59
def prefixEnd_8242609 : Nat := 4983230072969 + 3 ^ 40 * 8242609 * 2
def baseEnd_8242609 : Nat := 4232420264075446488080437

theorem tailTrace_8242609 : CollatzResearch.WordTrace tailWord_8242609 prefixEnd_8242609 4232420264075446488080437 := by
  unfold tailWord_8242609
  simp only [CollatzResearch.WordTrace]
  refine ⟨300632648195442793387554881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200421765463628528925036587 300632648195442793387554881)
  ·
    refine ⟨225474486146582095040666161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300632648195442793387554881 225474486146582095040666161)
    ·
      refine ⟨169105864609936571280499621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225474486146582095040666161 169105864609936571280499621)
      ·
        refine ⟨31707349614363107115093679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169105864609936571280499621 31707349614363107115093679)
        ·
          refine ⟨47561024421544660672640519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31707349614363107115093679 47561024421544660672640519)
          ·
            refine ⟨71341536632316991008960779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47561024421544660672640519 71341536632316991008960779)
            ·
              refine ⟨107012304948475486513441169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71341536632316991008960779 107012304948475486513441169)
              ·
                refine ⟨80259228711356614885080877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107012304948475486513441169 80259228711356614885080877)
                ·
                  refine ⟨30097210766758730581905329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80259228711356614885080877 30097210766758730581905329)
                  ·
                    refine ⟨22572908075069047936428997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30097210766758730581905329 22572908075069047936428997)
                    ·
                      refine ⟨4232420264075446488080437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22572908075069047936428997 4232420264075446488080437)
                      ·
                        rfl

theorem cell23_8242609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_8242609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242609 prefixEnd_8242609 := by exact prefixLift 8242609
  have htrace : WordTrace (prefixWord ++ tailWord_8242609) baseStart_8242609 baseEnd_8242609 := by
    simpa [prefixWord, tailWord_8242609, baseEnd_8242609] using wordTrace_append hprefix tailTrace_8242609
  have hstable : (prefixWord ++ tailWord_8242609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242609).length < 2 ^ (prefixWord ++ tailWord_8242609).sum := by decide
  have hdescent : baseEnd_8242609 < baseStart_8242609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242636 : List Nat := [2, 2, 1, 4, 2, 2, 3, 7]
def baseStart_8242636 : Nat := 118140960795 + 8242636 * 2 ^ 59
def prefixEnd_8242636 : Nat := 4983230072969 + 3 ^ 40 * 8242636 * 2
def baseEnd_8242636 : Nat := 156756819557522884534919

theorem tailTrace_8242636 : CollatzResearch.WordTrace tailWord_8242636 prefixEnd_8242636 156756819557522884534919 := by
  unfold tailWord_8242636
  simp only [CollatzResearch.WordTrace]
  refine ⟨150316816483172488499393881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200422421977563317999191841 150316816483172488499393881)
  ·
    refine ⟨112737612362379366374545411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150316816483172488499393881 112737612362379366374545411)
    ·
      refine ⟨169106418543569049561818117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112737612362379366374545411 169106418543569049561818117)
      ·
        refine ⟨31707453476919196792840897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169106418543569049561818117 31707453476919196792840897)
        ·
          refine ⟨23780590107689397594630673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31707453476919196792840897 23780590107689397594630673)
          ·
            refine ⟨17835442580767048195973005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23780590107689397594630673 17835442580767048195973005)
            ·
              refine ⟨6688290967787643073489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17835442580767048195973005 6688290967787643073489877)
              ·
                refine ⟨156756819557522884534919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6688290967787643073489877 156756819557522884534919)
                ·
                  rfl

theorem cell23_8242636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 7].length) (baseStart_8242636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242636 prefixEnd_8242636 := by exact prefixLift 8242636
  have htrace : WordTrace (prefixWord ++ tailWord_8242636) baseStart_8242636 baseEnd_8242636 := by
    simpa [prefixWord, tailWord_8242636, baseEnd_8242636] using wordTrace_append hprefix tailTrace_8242636
  have hstable : (prefixWord ++ tailWord_8242636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242636).length < 2 ^ (prefixWord ++ tailWord_8242636).sum := by decide
  have hdescent : baseEnd_8242636 < baseStart_8242636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242650 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_8242650 : Nat := 118140960795 + 8242650 * 2 ^ 59
def prefixEnd_8242650 : Nat := 4983230072969 + 3 ^ 40 * 8242650 * 2
def baseEnd_8242650 : Nat := 4232441316782280827667749

theorem tailTrace_8242650 : CollatzResearch.WordTrace tailWord_8242650 prefixEnd_8242650 4232441316782280827667749 := by
  unfold tailWord_8242650
  simp only [CollatzResearch.WordTrace]
  refine ⟨75158535897073564347449351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200422762392196171593198269 75158535897073564347449351)
  ·
    refine ⟨112737803845610346521174027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75158535897073564347449351 112737803845610346521174027)
    ·
      refine ⟨169106705768415519781761041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112737803845610346521174027 169106705768415519781761041)
      ·
        refine ⟨126830029326311639836320781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169106705768415519781761041 126830029326311639836320781)
        ·
          refine ⟨47561260997366864938620293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126830029326311639836320781 47561260997366864938620293)
          ·
            refine ⟨8917736437006287175991305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47561260997366864938620293 8917736437006287175991305)
            ·
              refine ⟨6688302327754715381993479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8917736437006287175991305 6688302327754715381993479)
              ·
                refine ⟨10032453491632073072990219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688302327754715381993479 10032453491632073072990219)
                ·
                  refine ⟨15048680237448109609485329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032453491632073072990219 15048680237448109609485329)
                  ·
                    refine ⟨11286510178086082207113997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15048680237448109609485329 11286510178086082207113997)
                    ·
                      refine ⟨4232441316782280827667749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286510178086082207113997 4232441316782280827667749)
                      ·
                        rfl

theorem cell23_8242650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_8242650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242650 prefixEnd_8242650 := by exact prefixLift 8242650
  have htrace : WordTrace (prefixWord ++ tailWord_8242650) baseStart_8242650 baseEnd_8242650 := by
    simpa [prefixWord, tailWord_8242650, baseEnd_8242650] using wordTrace_append hprefix tailTrace_8242650
  have hstable : (prefixWord ++ tailWord_8242650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242650).length < 2 ^ (prefixWord ++ tailWord_8242650).sum := by decide
  have hdescent : baseEnd_8242650 < baseStart_8242650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242656 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2]
def baseStart_8242656 : Nat := 118140960795 + 8242656 * 2 ^ 59
def prefixEnd_8242656 : Nat := 4983230072969 + 3 ^ 40 * 8242656 * 2
def baseEnd_8242656 : Nat := 4232444397666207804192721

theorem tailTrace_8242656 : CollatzResearch.WordTrace tailWord_8242656 prefixEnd_8242656 4232444397666207804192721 := by
  unfold tailWord_8242656
  simp only [CollatzResearch.WordTrace]
  refine ⟨150317181213136260207257911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200422908284181680276343881 150317181213136260207257911)
  ·
    refine ⟨225475771819704390310886867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150317181213136260207257911 225475771819704390310886867)
    ·
      refine ⟨338213657729556585466330301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225475771819704390310886867 338213657729556585466330301)
      ·
        refine ⟨126830121648583719549873863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338213657729556585466330301 126830121648583719549873863)
        ·
          refine ⟨190245182472875579324810795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126830121648583719549873863 190245182472875579324810795)
          ·
            refine ⟨285367773709313368987216193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190245182472875579324810795 285367773709313368987216193)
            ·
              refine ⟨214025830281985026740412145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285367773709313368987216193 214025830281985026740412145)
              ·
                refine ⟨160519372711488770055309109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214025830281985026740412145 160519372711488770055309109)
                ·
                  refine ⟨15048691191702072192685229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160519372711488770055309109 15048691191702072192685229)
                  ·
                    refine ⟨5643259196888277072256961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15048691191702072192685229 5643259196888277072256961)
                    ·
                      refine ⟨4232444397666207804192721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643259196888277072256961 4232444397666207804192721)
                      ·
                        rfl

theorem cell23_8242656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_8242656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242656 prefixEnd_8242656 := by exact prefixLift 8242656
  have htrace : WordTrace (prefixWord ++ tailWord_8242656) baseStart_8242656 baseEnd_8242656 := by
    simpa [prefixWord, tailWord_8242656, baseEnd_8242656] using wordTrace_append hprefix tailTrace_8242656
  have hstable : (prefixWord ++ tailWord_8242656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242656).length < 2 ^ (prefixWord ++ tailWord_8242656).sum := by decide
  have hdescent : baseEnd_8242656 < baseStart_8242656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242663 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_8242663 : Nat := 118140960795 + 8242663 * 2 ^ 59
def prefixEnd_8242663 : Nat := 4983230072969 + 3 ^ 40 * 8242663 * 2
def baseEnd_8242663 : Nat := 4232447992030789276805189

theorem tailTrace_8242663 : CollatzResearch.WordTrace tailWord_8242663 prefixEnd_8242663 4232447992030789276805189 := by
  unfold tailWord_8242663
  simp only [CollatzResearch.WordTrace]
  refine ⟨300634617737247160610020643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200423078491498107073347095 300634617737247160610020643)
  ·
    refine ⟨450951926605870740915030965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300634617737247160610020643 450951926605870740915030965)
    ·
      refine ⟨42276743119300381960784153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450951926605870740915030965 42276743119300381960784153)
      ·
        refine ⟨31707557339475286470588115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42276743119300381960784153 31707557339475286470588115)
        ·
          refine ⟨47561336009212929705882173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31707557339475286470588115 47561336009212929705882173)
          ·
            refine ⟨17835501003454848639705815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47561336009212929705882173 17835501003454848639705815)
            ·
              refine ⟨26753251505182272959558723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17835501003454848639705815 26753251505182272959558723)
              ·
                refine ⟨40129877257773409439338085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26753251505182272959558723 40129877257773409439338085)
                ·
                  refine ⟨7524351985832514269875891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40129877257773409439338085 7524351985832514269875891)
                  ·
                    refine ⟨11286527978748771404813837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524351985832514269875891 11286527978748771404813837)
                    ·
                      refine ⟨4232447992030789276805189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286527978748771404813837 4232447992030789276805189)
                      ·
                        rfl

theorem cell23_8242663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_8242663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242663 prefixEnd_8242663 := by exact prefixLift 8242663
  have htrace : WordTrace (prefixWord ++ tailWord_8242663) baseStart_8242663 baseEnd_8242663 := by
    simpa [prefixWord, tailWord_8242663, baseEnd_8242663] using wordTrace_append hprefix tailTrace_8242663
  have hstable : (prefixWord ++ tailWord_8242663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242663).length < 2 ^ (prefixWord ++ tailWord_8242663).sum := by decide
  have hdescent : baseEnd_8242663 < baseStart_8242663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242680 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_8242680 : Nat := 118140960795 + 8242680 * 2 ^ 59
def prefixEnd_8242680 : Nat := 4983230072969 + 3 ^ 40 * 8242680 * 2
def baseEnd_8242680 : Nat := 4232456721201915710292611

theorem tailTrace_8242680 : CollatzResearch.WordTrace tailWord_8242680 prefixEnd_8242680 4232456721201915710292611 := by
  unfold tailWord_8242680
  simp only [CollatzResearch.WordTrace]
  refine ⟨150317618889092786256694747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200423491852123715008926329 150317618889092786256694747)
  ·
    refine ⟨225476428333639179385042121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150317618889092786256694747 225476428333639179385042121)
    ·
      refine ⟨169107321250229384538781591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225476428333639179385042121 169107321250229384538781591)
      ·
        refine ⟨253660981875344076808172387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169107321250229384538781591 253660981875344076808172387)
        ·
          refine ⟨380491472813016115212258581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253660981875344076808172387 380491472813016115212258581)
          ·
            refine ⟨17835537788110130400574621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380491472813016115212258581 17835537788110130400574621)
            ·
              refine ⟨6688326670541298900215483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17835537788110130400574621 6688326670541298900215483)
              ·
                refine ⟨10032490005811948350323225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688326670541298900215483 10032490005811948350323225)
                ·
                  refine ⟨7524367504358961262742419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032490005811948350323225 7524367504358961262742419)
                  ·
                    refine ⟨11286551256538441894113629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524367504358961262742419 11286551256538441894113629)
                    ·
                      refine ⟨4232456721201915710292611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286551256538441894113629 4232456721201915710292611)
                      ·
                        rfl

theorem cell23_8242680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_8242680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242680 prefixEnd_8242680 := by exact prefixLift 8242680
  have htrace : WordTrace (prefixWord ++ tailWord_8242680) baseStart_8242680 baseEnd_8242680 := by
    simpa [prefixWord, tailWord_8242680, baseEnd_8242680] using wordTrace_append hprefix tailTrace_8242680
  have hstable : (prefixWord ++ tailWord_8242680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242680).length < 2 ^ (prefixWord ++ tailWord_8242680).sum := by decide
  have hdescent : baseEnd_8242680 < baseStart_8242680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242720 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8242720 : Nat := 118140960795 + 8242720 * 2 ^ 59
def prefixEnd_8242720 : Nat := 4983230072969 + 3 ^ 40 * 8242720 * 2
def baseEnd_8242720 : Nat := 4232477260428095553792427

theorem tailTrace_8242720 : CollatzResearch.WordTrace tailWord_8242720 prefixEnd_8242720 4232477260428095553792427 := by
  unfold tailWord_8242720
  simp only [CollatzResearch.WordTrace]
  refine ⟨150318348349020329672422807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200424464465360439563230409 150318348349020329672422807)
  ·
    refine ⟨225477522523530494508634211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150318348349020329672422807 225477522523530494508634211)
    ·
      refine ⟨338216283785295741762951317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225477522523530494508634211 338216283785295741762951317)
      ·
        refine ⟨15853888302435737895138343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338216283785295741762951317 15853888302435737895138343)
        ·
          refine ⟨23780832453653606842707515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15853888302435737895138343 23780832453653606842707515)
          ·
            refine ⟨35671248680480410264061273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23780832453653606842707515 35671248680480410264061273)
            ·
              refine ⟨26753436510360307698045955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35671248680480410264061273 26753436510360307698045955)
              ·
                refine ⟨40130154765540461547068933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26753436510360307698045955 40130154765540461547068933)
                ·
                  refine ⟨7524404018538836540075425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40130154765540461547068933 7524404018538836540075425)
                  ·
                    refine ⟨5643303013904127405056569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7524404018538836540075425 5643303013904127405056569)
                    ·
                      refine ⟨4232477260428095553792427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643303013904127405056569 4232477260428095553792427)
                      ·
                        rfl

theorem cell23_8242720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8242720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242720 prefixEnd_8242720 := by exact prefixLift 8242720
  have htrace : WordTrace (prefixWord ++ tailWord_8242720) baseStart_8242720 baseEnd_8242720 := by
    simpa [prefixWord, tailWord_8242720, baseEnd_8242720] using wordTrace_append hprefix tailTrace_8242720
  have hstable : (prefixWord ++ tailWord_8242720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242720).length < 2 ^ (prefixWord ++ tailWord_8242720).sum := by decide
  have hdescent : baseEnd_8242720 < baseStart_8242720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242796 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_8242796 : Nat := 118140960795 + 8242796 * 2 ^ 59
def prefixEnd_8242796 : Nat := 4983230072969 + 3 ^ 40 * 8242796 * 2
def baseEnd_8242796 : Nat := 4232516284957837256442077

theorem tailTrace_8242796 : CollatzResearch.WordTrace tailWord_8242796 prefixEnd_8242796 4232516284957837256442077 := by
  unfold tailWord_8242796
  simp only [CollatzResearch.WordTrace]
  refine ⟨150319734322882662162306121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200426312430510216216408161 150319734322882662162306121)
  ·
    refine ⟨112739800742161996621729591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150319734322882662162306121 112739800742161996621729591)
    ·
      refine ⟨169109701113242994932594387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112739800742161996621729591 169109701113242994932594387)
      ·
        refine ⟨253664551669864492398891581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169109701113242994932594387 253664551669864492398891581)
        ·
          refine ⟨95124206876199184649584343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253664551669864492398891581 95124206876199184649584343)
          ·
            refine ⟨142686310314298776974376515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95124206876199184649584343 142686310314298776974376515)
            ·
              refine ⟨214029465471448165461564773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142686310314298776974376515 214029465471448165461564773)
              ·
                refine ⟨40130524775896531024043395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214029465471448165461564773 40130524775896531024043395)
                ·
                  refine ⟨60195787163844796536065093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40130524775896531024043395 60195787163844796536065093)
                  ·
                    refine ⟨11286710093220899350512205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60195787163844796536065093 11286710093220899350512205)
                    ·
                      refine ⟨4232516284957837256442077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286710093220899350512205 4232516284957837256442077)
                      ·
                        rfl

theorem cell23_8242796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_8242796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242796 prefixEnd_8242796 := by exact prefixLift 8242796
  have htrace : WordTrace (prefixWord ++ tailWord_8242796) baseStart_8242796 baseEnd_8242796 := by
    simpa [prefixWord, tailWord_8242796, baseEnd_8242796] using wordTrace_append hprefix tailTrace_8242796
  have hstable : (prefixWord ++ tailWord_8242796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242796).length < 2 ^ (prefixWord ++ tailWord_8242796).sum := by decide
  have hdescent : baseEnd_8242796 < baseStart_8242796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242799 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 10]
def baseStart_8242799 : Nat := 118140960795 + 8242799 * 2 ^ 59
def prefixEnd_8242799 : Nat := 4983230072969 + 3 ^ 40 * 8242799 * 2
def baseEnd_8242799 : Nat := 470279758377755638300507

theorem tailTrace_8242799 : CollatzResearch.WordTrace tailWord_8242799 prefixEnd_8242799 470279758377755638300507 := by
  unfold tailWord_8242799
  simp only [CollatzResearch.WordTrace]
  refine ⟨300639578064754455836971451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200426385376502970557980967 300639578064754455836971451)
  ·
    refine ⟨450959367097131683755457177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300639578064754455836971451 450959367097131683755457177)
    ·
      refine ⟨338219525322848762816592883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450959367097131683755457177 338219525322848762816592883)
      ·
        refine ⟨507329287984273144224889325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338219525322848762816592883 507329287984273144224889325)
        ·
          refine ⟨190248482994102429084333497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507329287984273144224889325 190248482994102429084333497)
          ·
            refine ⟨142686362245576821813250123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190248482994102429084333497 142686362245576821813250123)
            ·
              refine ⟨214029543368365232719875185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142686362245576821813250123 214029543368365232719875185)
              ·
                refine ⟨160522157526273924539906389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214029543368365232719875185 160522157526273924539906389)
                ·
                  refine ⟨470279758377755638300507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 160522157526273924539906389 470279758377755638300507)
                  ·
                    rfl

theorem cell23_8242799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 10].length) (baseStart_8242799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242799 prefixEnd_8242799 := by exact prefixLift 8242799
  have htrace : WordTrace (prefixWord ++ tailWord_8242799) baseStart_8242799 baseEnd_8242799 := by
    simpa [prefixWord, tailWord_8242799, baseEnd_8242799] using wordTrace_append hprefix tailTrace_8242799
  have hstable : (prefixWord ++ tailWord_8242799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242799).length < 2 ^ (prefixWord ++ tailWord_8242799).sum := by decide
  have hdescent : baseEnd_8242799 < baseStart_8242799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242813 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_8242813 : Nat := 118140960795 + 8242813 * 2 ^ 59
def prefixEnd_8242813 : Nat := 4983230072969 + 3 ^ 40 * 8242813 * 2
def baseEnd_8242813 : Nat := 4232525014128963689929499

theorem tailTrace_8242813 : CollatzResearch.WordTrace tailWord_8242813 prefixEnd_8242813 4232525014128963689929499 := by
  unfold tailWord_8242813
  simp only [CollatzResearch.WordTrace]
  refine ⟨300640088686703736227981093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200426725791135824151987395 300640088686703736227981093)
  ·
    refine ⟨56370016628756950542746455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300640088686703736227981093 56370016628756950542746455)
    ·
      refine ⟨84555024943135425814119683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56370016628756950542746455 84555024943135425814119683)
      ·
        refine ⟨126832537414703138721179525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84555024943135425814119683 126832537414703138721179525)
        ·
          refine ⟨23781100765256838510221161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126832537414703138721179525 23781100765256838510221161)
          ·
            refine ⟨17835825573942628882665871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23781100765256838510221161 17835825573942628882665871)
            ·
              refine ⟨26753738360913943323998807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17835825573942628882665871 26753738360913943323998807)
              ·
                refine ⟨40130607541370914985998211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26753738360913943323998807 40130607541370914985998211)
                ·
                  refine ⟨60195911312056372478997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40130607541370914985998211 60195911312056372478997317)
                  ·
                    refine ⟨11286733371010569839811997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60195911312056372478997317 11286733371010569839811997)
                    ·
                      refine ⟨4232525014128963689929499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286733371010569839811997 4232525014128963689929499)
                      ·
                        rfl

theorem cell23_8242813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_8242813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242813 prefixEnd_8242813 := by exact prefixLift 8242813
  have htrace : WordTrace (prefixWord ++ tailWord_8242813) baseStart_8242813 baseEnd_8242813 := by
    simpa [prefixWord, tailWord_8242813, baseEnd_8242813] using wordTrace_append hprefix tailTrace_8242813
  have hstable : (prefixWord ++ tailWord_8242813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242813).length < 2 ^ (prefixWord ++ tailWord_8242813).sum := by decide
  have hdescent : baseEnd_8242813 < baseStart_8242813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242853 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_8242853 : Nat := 118140960795 + 8242853 * 2 ^ 59
def prefixEnd_8242853 : Nat := 4983230072969 + 3 ^ 40 * 8242853 * 2
def baseEnd_8242853 : Nat := 4232545553355143533429315

theorem tailTrace_8242853 : CollatzResearch.WordTrace tailWord_8242853 prefixEnd_8242853 4232545553355143533429315 := by
  unfold tailWord_8242853
  simp only [CollatzResearch.WordTrace]
  refine ⟨300641547606558823059437213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200427698404372548706291475 300641547606558823059437213)
  ·
    refine ⟨112740580352459558647288955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300641547606558823059437213 112740580352459558647288955)
    ·
      refine ⟨169110870528689337970933433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112740580352459558647288955 169110870528689337970933433)
      ·
        refine ⟨126833152896517003478200075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169110870528689337970933433 126833152896517003478200075)
        ·
          refine ⟨190249729344775505217300113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126833152896517003478200075 190249729344775505217300113)
          ·
            refine ⟨142687297008581628912975085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190249729344775505217300113 142687297008581628912975085)
            ·
              refine ⟨53507736378218110842365657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142687297008581628912975085 53507736378218110842365657)
              ·
                refine ⟨40130802283663583131774243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53507736378218110842365657 40130802283663583131774243)
                ·
                  refine ⟨60196203425495374697661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40130802283663583131774243 60196203425495374697661365)
                  ·
                    refine ⟨5643394071140191377905753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60196203425495374697661365 5643394071140191377905753)
                    ·
                      refine ⟨4232545553355143533429315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643394071140191377905753 4232545553355143533429315)
                      ·
                        rfl

theorem cell23_8242853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_8242853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242853 prefixEnd_8242853 := by exact prefixLift 8242853
  have htrace : WordTrace (prefixWord ++ tailWord_8242853) baseStart_8242853 baseEnd_8242853 := by
    simpa [prefixWord, tailWord_8242853, baseEnd_8242853] using wordTrace_append hprefix tailTrace_8242853
  have hstable : (prefixWord ++ tailWord_8242853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242853).length < 2 ^ (prefixWord ++ tailWord_8242853).sum := by decide
  have hdescent : baseEnd_8242853 < baseStart_8242853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242863 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 1, 5]
def baseStart_8242863 : Nat := 118140960795 + 8242863 * 2 ^ 59
def prefixEnd_8242863 : Nat := 4983230072969 + 3 ^ 40 * 8242863 * 2
def baseEnd_8242863 : Nat := 1410850229387229498101423

theorem tailTrace_8242863 : CollatzResearch.WordTrace tailWord_8242863 prefixEnd_8242863 1410850229387229498101423 := by
  unfold tailWord_8242863
  simp only [CollatzResearch.WordTrace]
  refine ⟨300641912336522594767301243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200427941557681729844867495 300641912336522594767301243)
  ·
    refine ⟨450962868504783892150951865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300641912336522594767301243 450962868504783892150951865)
    ·
      refine ⟨338222151378587919113213899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450962868504783892150951865 338222151378587919113213899)
      ·
        refine ⟨507333227067881878669820849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338222151378587919113213899 507333227067881878669820849)
        ·
          refine ⟨380499920300911409002365637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507333227067881878669820849 380499920300911409002365637)
          ·
            refine ⟨71343735056420889187943557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380499920300911409002365637 71343735056420889187943557)
            ·
              refine ⟨13376950323078916722739417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71343735056420889187943557 13376950323078916722739417)
              ·
                refine ⟨10032712742309187542054563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13376950323078916722739417 10032712742309187542054563)
                ·
                  refine ⟨15049069113463781313081845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032712742309187542054563 15049069113463781313081845)
                  ·
                    refine ⟨1410850229387229498101423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15049069113463781313081845 1410850229387229498101423)
                    ·
                      rfl

theorem cell23_8242863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_8242863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242863 prefixEnd_8242863 := by exact prefixLift 8242863
  have htrace : WordTrace (prefixWord ++ tailWord_8242863) baseStart_8242863 baseEnd_8242863 := by
    simpa [prefixWord, tailWord_8242863, baseEnd_8242863] using wordTrace_append hprefix tailTrace_8242863
  have hstable : (prefixWord ++ tailWord_8242863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242863).length < 2 ^ (prefixWord ++ tailWord_8242863).sum := by decide
  have hdescent : baseEnd_8242863 < baseStart_8242863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242894 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_8242894 : Nat := 118140960795 + 8242894 * 2 ^ 59
def prefixEnd_8242894 : Nat := 4983230072969 + 3 ^ 40 * 8242894 * 2
def baseEnd_8242894 : Nat := 4232566606061977873016627

theorem tailTrace_8242894 : CollatzResearch.WordTrace tailWord_8242894 prefixEnd_8242894 4232566606061977873016627 := by
  unfold tailWord_8242894
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580380374926285882709967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200428695332940191374453157 37580380374926285882709967)
  ·
    refine ⟨56370570562389428824064951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37580380374926285882709967 56370570562389428824064951)
    ·
      refine ⟨84555855843584143236097427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56370570562389428824064951 84555855843584143236097427)
      ·
        refine ⟨126833783765376214854146141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84555855843584143236097427 126833783765376214854146141)
        ·
          refine ⟨47562668912016080570304803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126833783765376214854146141 47562668912016080570304803)
          ·
            refine ⟨71344003368024120855457205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47562668912016080570304803 71344003368024120855457205)
            ·
              refine ⟨6688500315752261330199113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71344003368024120855457205 6688500315752261330199113)
              ·
                refine ⟨5016375236814195997649335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6688500315752261330199113 5016375236814195997649335)
                ·
                  refine ⟨7524562855221293996474003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016375236814195997649335 7524562855221293996474003)
                  ·
                    refine ⟨11286844282831940994711005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524562855221293996474003 11286844282831940994711005)
                    ·
                      refine ⟨4232566606061977873016627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286844282831940994711005 4232566606061977873016627)
                      ·
                        rfl

theorem cell23_8242894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_8242894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242894 prefixEnd_8242894 := by exact prefixLift 8242894
  have htrace : WordTrace (prefixWord ++ tailWord_8242894) baseStart_8242894 baseEnd_8242894 := by
    simpa [prefixWord, tailWord_8242894, baseEnd_8242894] using wordTrace_append hprefix tailTrace_8242894
  have hstable : (prefixWord ++ tailWord_8242894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242894).length < 2 ^ (prefixWord ++ tailWord_8242894).sum := by decide
  have hdescent : baseEnd_8242894 < baseStart_8242894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242896 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_8242896 : Nat := 118140960795 + 8242896 * 2 ^ 59
def prefixEnd_8242896 : Nat := 4983230072969 + 3 ^ 40 * 8242896 * 2
def baseEnd_8242896 : Nat := 4232567633023286865191617

theorem tailTrace_8242896 : CollatzResearch.WordTrace tailWord_8242896 prefixEnd_8242896 4232567633023286865191617 := by
  unfold tailWord_8242896
  simp only [CollatzResearch.WordTrace]
  refine ⟨150321557972701520701626271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200428743963602027602168361 150321557972701520701626271)
  ·
    refine ⟨225482336959052281052439407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150321557972701520701626271 225482336959052281052439407)
    ·
      refine ⟨338223505438578421578659111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225482336959052281052439407 338223505438578421578659111)
      ·
        refine ⟨507335258157867632367988667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338223505438578421578659111 507335258157867632367988667)
        ·
          refine ⟨761002887236801448551983001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507335258157867632367988667 761002887236801448551983001)
          ·
            refine ⟨570752165427601086413987251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761002887236801448551983001 570752165427601086413987251)
            ·
              refine ⟨856128248141401629620980877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570752165427601086413987251 856128248141401629620980877)
              ·
                refine ⟨321048093053025611107867829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856128248141401629620980877 321048093053025611107867829)
                ·
                  refine ⟨30098258723721151041362609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321048093053025611107867829 30098258723721151041362609)
                  ·
                    refine ⟨22573694042790863281021957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30098258723721151041362609 22573694042790863281021957)
                    ·
                      refine ⟨4232567633023286865191617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22573694042790863281021957 4232567633023286865191617)
                      ·
                        rfl

theorem cell23_8242896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_8242896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242896 prefixEnd_8242896 := by exact prefixLift 8242896
  have htrace : WordTrace (prefixWord ++ tailWord_8242896) baseStart_8242896 baseEnd_8242896 := by
    simpa [prefixWord, tailWord_8242896, baseEnd_8242896] using wordTrace_append hprefix tailTrace_8242896
  have hstable : (prefixWord ++ tailWord_8242896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242896).length < 2 ^ (prefixWord ++ tailWord_8242896).sum := by decide
  have hdescent : baseEnd_8242896 < baseStart_8242896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242903 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_8242903 : Nat := 118140960795 + 8242903 * 2 ^ 59
def prefixEnd_8242903 : Nat := 4983230072969 + 3 ^ 40 * 8242903 * 2
def baseEnd_8242903 : Nat := 4232571227387868337804085

theorem tailTrace_8242903 : CollatzResearch.WordTrace tailWord_8242903 prefixEnd_8242903 4232571227387868337804085 := by
  unfold tailWord_8242903
  simp only [CollatzResearch.WordTrace]
  refine ⟨300643371256377681598757363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200428914170918454399171575 300643371256377681598757363)
  ·
    refine ⟨450965056884566522398136045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300643371256377681598757363 450965056884566522398136045)
    ·
      refine ⟨169111896331712445899301017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450965056884566522398136045 169111896331712445899301017)
      ·
        refine ⟨126833922248784334424475763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169111896331712445899301017 126833922248784334424475763)
        ·
          refine ⟨190250883373176501636713645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126833922248784334424475763 190250883373176501636713645)
          ·
            refine ⟨71344081264941188113767617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190250883373176501636713645 71344081264941188113767617)
            ·
              refine ⟨53508060948705891085325713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71344081264941188113767617 53508060948705891085325713)
              ·
                refine ⟨40131045711529418313994285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53508060948705891085325713 40131045711529418313994285)
                ·
                  refine ⟨15049142141823531867747857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40131045711529418313994285 15049142141823531867747857)
                  ·
                    refine ⟨11286856606367648900810893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15049142141823531867747857 11286856606367648900810893)
                    ·
                      refine ⟨4232571227387868337804085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286856606367648900810893 4232571227387868337804085)
                      ·
                        rfl

theorem cell23_8242903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_8242903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242903 prefixEnd_8242903 := by exact prefixLift 8242903
  have htrace : WordTrace (prefixWord ++ tailWord_8242903) baseStart_8242903 baseEnd_8242903 := by
    simpa [prefixWord, tailWord_8242903, baseEnd_8242903] using wordTrace_append hprefix tailTrace_8242903
  have hstable : (prefixWord ++ tailWord_8242903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242903).length < 2 ^ (prefixWord ++ tailWord_8242903).sum := by decide
  have hdescent : baseEnd_8242903 < baseStart_8242903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242906 : List Nat := [3, 1, 1, 2, 2, 3, 1, 10]
def baseStart_8242906 : Nat := 118140960795 + 8242906 * 2 ^ 59
def prefixEnd_8242906 : Nat := 4983230072969 + 3 ^ 40 * 8242906 * 2
def baseEnd_8242906 : Nat := 156761954364067845409873

theorem tailTrace_8242906 : CollatzResearch.WordTrace tailWord_8242906 prefixEnd_8242906 156761954364067845409873 := by
  unfold tailWord_8242906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75160870168841703277779143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200428987116911208740744381 75160870168841703277779143)
  ·
    refine ⟨112741305253262554916668715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75160870168841703277779143 112741305253262554916668715)
    ·
      refine ⟨169111957879893832375003073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112741305253262554916668715 169111957879893832375003073)
      ·
        refine ⟨126833968409920374281252305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169111957879893832375003073 126833968409920374281252305)
        ·
          refine ⟨95125476307440280710939229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126833968409920374281252305 95125476307440280710939229)
          ·
            refine ⟨35672053615290105266602211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95125476307440280710939229 35672053615290105266602211)
            ·
              refine ⟨53508080422935157899903317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35672053615290105266602211 53508080422935157899903317)
              ·
                refine ⟨156761954364067845409873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53508080422935157899903317 156761954364067845409873)
                ·
                  rfl

theorem cell23_8242906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_8242906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242906 prefixEnd_8242906 := by exact prefixLift 8242906
  have htrace : WordTrace (prefixWord ++ tailWord_8242906) baseStart_8242906 baseEnd_8242906 := by
    simpa [prefixWord, tailWord_8242906, baseEnd_8242906] using wordTrace_append hprefix tailTrace_8242906
  have hstable : (prefixWord ++ tailWord_8242906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242906).length < 2 ^ (prefixWord ++ tailWord_8242906).sum := by decide
  have hdescent : baseEnd_8242906 < baseStart_8242906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242920 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_8242920 : Nat := 118140960795 + 8242920 * 2 ^ 59
def prefixEnd_8242920 : Nat := 4983230072969 + 3 ^ 40 * 8242920 * 2
def baseEnd_8242920 : Nat := 4232579956558994771291507

theorem tailTrace_8242920 : CollatzResearch.WordTrace tailWord_8242920 prefixEnd_8242920 4232579956558994771291507 := by
  unfold tailWord_8242920
  simp only [CollatzResearch.WordTrace]
  refine ⟨150321995648658046751063107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200429327531544062334750809 150321995648658046751063107)
  ·
    refine ⟨225482993472987070126594661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150321995648658046751063107 225482993472987070126594661)
    ·
      refine ⟨42278061276185075648736499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225482993472987070126594661 42278061276185075648736499)
      ·
        refine ⟨63417091914277613473104749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42278061276185075648736499 63417091914277613473104749)
        ·
          refine ⟨23781409467854105052414281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63417091914277613473104749 23781409467854105052414281)
          ·
            refine ⟨17836057100890578789310711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23781409467854105052414281 17836057100890578789310711)
            ·
              refine ⟨26754085651335868183966067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836057100890578789310711 26754085651335868183966067)
              ·
                refine ⟨40131128477003802275949101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26754085651335868183966067 40131128477003802275949101)
                ·
                  refine ⟨15049173178876425853480913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40131128477003802275949101 15049173178876425853480913)
                  ·
                    refine ⟨11286879884157319390110685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15049173178876425853480913 11286879884157319390110685)
                    ·
                      refine ⟨4232579956558994771291507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286879884157319390110685 4232579956558994771291507)
                      ·
                        rfl

theorem cell23_8242920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_8242920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242920 prefixEnd_8242920 := by exact prefixLift 8242920
  have htrace : WordTrace (prefixWord ++ tailWord_8242920) baseStart_8242920 baseEnd_8242920 := by
    simpa [prefixWord, tailWord_8242920, baseEnd_8242920] using wordTrace_append hprefix tailTrace_8242920
  have hstable : (prefixWord ++ tailWord_8242920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242920).length < 2 ^ (prefixWord ++ tailWord_8242920).sum := by decide
  have hdescent : baseEnd_8242920 < baseStart_8242920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242951 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8242951 : Nat := 118140960795 + 8242951 * 2 ^ 59
def prefixEnd_8242951 : Nat := 4983230072969 + 3 ^ 40 * 8242951 * 2
def baseEnd_8242951 : Nat := 4232595874459284150003865

theorem tailTrace_8242951 : CollatzResearch.WordTrace tailWord_8242951 prefixEnd_8242951 4232595874459284150003865 := by
  unfold tailWord_8242951
  simp only [CollatzResearch.WordTrace]
  refine ⟨300645121960203785796504707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200430081306802523864336471 300645121960203785796504707)
  ·
    refine ⟨450967682940305678694757061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300645121960203785796504707 450967682940305678694757061)
    ·
      refine ⟨84556440551307314755266949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450967682940305678694757061 84556440551307314755266949)
      ·
        refine ⟨15854332603370121516612553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84556440551307314755266949 15854332603370121516612553)
        ·
          refine ⟨11890749452527591137459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15854332603370121516612553 11890749452527591137459415)
          ·
            refine ⟨17836124178791386706189123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890749452527591137459415 17836124178791386706189123)
            ·
              refine ⟨26754186268187080059283685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836124178791386706189123 26754186268187080059283685)
              ·
                refine ⟨5016409925285077511115691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26754186268187080059283685 5016409925285077511115691)
                ·
                  refine ⟨7524614887927616266673537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016409925285077511115691 7524614887927616266673537)
                  ·
                    refine ⟨5643461165945712200005153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7524614887927616266673537 5643461165945712200005153)
                    ·
                      refine ⟨4232595874459284150003865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643461165945712200005153 4232595874459284150003865)
                      ·
                        rfl

theorem cell23_8242951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8242951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242951 prefixEnd_8242951 := by exact prefixLift 8242951
  have htrace : WordTrace (prefixWord ++ tailWord_8242951) baseStart_8242951 baseEnd_8242951 := by
    simpa [prefixWord, tailWord_8242951, baseEnd_8242951] using wordTrace_append hprefix tailTrace_8242951
  have hstable : (prefixWord ++ tailWord_8242951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242951).length < 2 ^ (prefixWord ++ tailWord_8242951).sum := by decide
  have hdescent : baseEnd_8242951 < baseStart_8242951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242967 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_8242967 : Nat := 118140960795 + 8242967 * 2 ^ 59
def prefixEnd_8242967 : Nat := 4983230072969 + 3 ^ 40 * 8242967 * 2
def baseEnd_8242967 : Nat := 4232604090149756087403791

theorem tailTrace_8242967 : CollatzResearch.WordTrace tailWord_8242967 prefixEnd_8242967 4232604090149756087403791 := by
  unfold tailWord_8242967
  simp only [CollatzResearch.WordTrace]
  refine ⟨300645705528145820529087155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200430470352097213686058103 300645705528145820529087155)
  ·
    refine ⟨450968558292218730793630733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300645705528145820529087155 450968558292218730793630733)
    ·
      refine ⟨169113209359582024047611525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450968558292218730793630733 169113209359582024047611525)
      ·
        refine ⟨31708726754921629508927161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169113209359582024047611525 31708726754921629508927161)
        ·
          refine ⟨23781545066191222131695371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31708726754921629508927161 23781545066191222131695371)
          ·
            refine ⟨35672317599286833197543057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23781545066191222131695371 35672317599286833197543057)
            ·
              refine ⟨26754238199465124898157293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35672317599286833197543057 26754238199465124898157293)
              ·
                refine ⟨10032839324799421836808985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26754238199465124898157293 10032839324799421836808985)
                ·
                  refine ⟨7524629493599566377606739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032839324799421836808985 7524629493599566377606739)
                  ·
                    refine ⟨11286944240399349566410109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524629493599566377606739 11286944240399349566410109)
                    ·
                      refine ⟨4232604090149756087403791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286944240399349566410109 4232604090149756087403791)
                      ·
                        rfl

theorem cell23_8242967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_8242967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242967 prefixEnd_8242967 := by exact prefixLift 8242967
  have htrace : WordTrace (prefixWord ++ tailWord_8242967) baseStart_8242967 baseEnd_8242967 := by
    simpa [prefixWord, tailWord_8242967, baseEnd_8242967] using wordTrace_append hprefix tailTrace_8242967
  have hstable : (prefixWord ++ tailWord_8242967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242967).length < 2 ^ (prefixWord ++ tailWord_8242967).sum := by decide
  have hdescent : baseEnd_8242967 < baseStart_8242967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242974 : List Nat := [4, 3, 2, 2, 1, 1, 3, 7]
def baseStart_8242974 : Nat := 118140960795 + 8242974 * 2 ^ 59
def prefixEnd_8242974 : Nat := 4983230072969 + 3 ^ 40 * 8242974 * 2
def baseEnd_8242974 : Nat := 156763247574605094815417

theorem tailTrace_8242974 : CollatzResearch.WordTrace tailWord_8242974 prefixEnd_8242974 156763247574605094815417 := by
  unfold tailWord_8242974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580745104890057590573997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200430640559413640483061317 37580745104890057590573997)
  ·
    refine ⟨14092779414333771596465249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37580745104890057590573997 14092779414333771596465249)
    ·
      refine ⟨10569584560750328697348937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14092779414333771596465249 10569584560750328697348937)
      ·
        refine ⟨7927188420562746523011703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10569584560750328697348937 7927188420562746523011703)
        ·
          refine ⟨11890782630844119784517555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927188420562746523011703 11890782630844119784517555)
          ·
            refine ⟨17836173946266179676776333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890782630844119784517555 17836173946266179676776333)
            ·
              refine ⟨6688565229849817378791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17836173946266179676776333 6688565229849817378791125)
              ·
                refine ⟨156763247574605094815417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6688565229849817378791125 156763247574605094815417)
                ·
                  rfl

theorem cell23_8242974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_8242974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242974 prefixEnd_8242974 := by exact prefixLift 8242974
  have htrace : WordTrace (prefixWord ++ tailWord_8242974) baseStart_8242974 baseEnd_8242974 := by
    simpa [prefixWord, tailWord_8242974, baseEnd_8242974] using wordTrace_append hprefix tailTrace_8242974
  have hstable : (prefixWord ++ tailWord_8242974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242974).length < 2 ^ (prefixWord ++ tailWord_8242974).sum := by decide
  have hdescent : baseEnd_8242974 < baseStart_8242974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8242994 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_8242994 : Nat := 118140960795 + 8242994 * 2 ^ 59
def prefixEnd_8242994 : Nat := 4983230072969 + 3 ^ 40 * 8242994 * 2
def baseEnd_8242994 : Nat := 4232617954127427481766167

theorem tailTrace_8242994 : CollatzResearch.WordTrace tailWord_8242994 prefixEnd_8242994 4232617954127427481766167 := by
  unfold tailWord_8242994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75161672574762001035080009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200431126866032002760213357 75161672574762001035080009)
  ·
    refine ⟨56371254431071500776310007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75161672574762001035080009 56371254431071500776310007)
    ·
      refine ⟨84556881646607251164465011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56371254431071500776310007 84556881646607251164465011)
      ·
        refine ⟨126835322469910876746697517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84556881646607251164465011 126835322469910876746697517)
        ·
          refine ⟨47563245926216578780011569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126835322469910876746697517 47563245926216578780011569)
          ·
            refine ⟨35672434444662434085008677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47563245926216578780011569 35672434444662434085008677)
            ·
              refine ⟨6688581458374206390939127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35672434444662434085008677 6688581458374206390939127)
              ·
                refine ⟨10032872187561309586408691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688581458374206390939127 10032872187561309586408691)
                ·
                  refine ⟨15049308281341964379613037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10032872187561309586408691 15049308281341964379613037)
                  ·
                    refine ⟨5643490605503236642354889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15049308281341964379613037 5643490605503236642354889)
                    ·
                      refine ⟨4232617954127427481766167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643490605503236642354889 4232617954127427481766167)
                      ·
                        rfl

theorem cell23_8242994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_8242994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8242994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8242994 prefixEnd_8242994 := by exact prefixLift 8242994
  have htrace : WordTrace (prefixWord ++ tailWord_8242994) baseStart_8242994 baseEnd_8242994 := by
    simpa [prefixWord, tailWord_8242994, baseEnd_8242994] using wordTrace_append hprefix tailTrace_8242994
  have hstable : (prefixWord ++ tailWord_8242994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8242994).length < 2 ^ (prefixWord ++ tailWord_8242994).sum := by decide
  have hdescent : baseEnd_8242994 < baseStart_8242994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8242994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243001 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8243001 : Nat := 118140960795 + 8243001 * 2 ^ 59
def prefixEnd_8243001 : Nat := 4983230072969 + 3 ^ 40 * 8243001 * 2
def baseEnd_8243001 : Nat := 4232621548492008954378635

theorem tailTrace_8243001 : CollatzResearch.WordTrace tailWord_8243001 prefixEnd_8243001 4232621548492008954378635 := by
  unfold tailWord_8243001
  simp only [CollatzResearch.WordTrace]
  refine ⟨300646945610022644335824857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200431297073348429557216571 300646945610022644335824857)
  ·
    refine ⟨225485209207516983251868643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300646945610022644335824857 225485209207516983251868643)
    ·
      refine ⟨338227813811275474877802965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225485209207516983251868643 338227813811275474877802965)
      ·
        refine ⟨7927214386201768942448507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 338227813811275474877802965 7927214386201768942448507)
        ·
          refine ⟨11890821579302653413672761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927214386201768942448507 11890821579302653413672761)
          ·
            refine ⟨8918116184476990060254571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11890821579302653413672761 8918116184476990060254571)
            ·
              refine ⟨13377174276715485090381857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918116184476990060254571 13377174276715485090381857)
              ·
                refine ⟨10032880707536613817786393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13377174276715485090381857 10032880707536613817786393)
                ·
                  refine ⟨7524660530652460363339795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10032880707536613817786393 7524660530652460363339795)
                  ·
                    refine ⟨11286990795978690545009693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524660530652460363339795 11286990795978690545009693)
                    ·
                      refine ⟨4232621548492008954378635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286990795978690545009693 4232621548492008954378635)
                      ·
                        rfl

theorem cell23_8243001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8243001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243001 prefixEnd_8243001 := by exact prefixLift 8243001
  have htrace : WordTrace (prefixWord ++ tailWord_8243001) baseStart_8243001 baseEnd_8243001 := by
    simpa [prefixWord, tailWord_8243001, baseEnd_8243001] using wordTrace_append hprefix tailTrace_8243001
  have hstable : (prefixWord ++ tailWord_8243001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243001).length < 2 ^ (prefixWord ++ tailWord_8243001).sum := by decide
  have hdescent : baseEnd_8243001 < baseStart_8243001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243013 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 7]
def baseStart_8243013 : Nat := 118140960795 + 8243013 * 2 ^ 59
def prefixEnd_8243013 : Nat := 4983230072969 + 3 ^ 40 * 8243013 * 2
def baseEnd_8243013 : Nat := 470291967806651434158731

theorem tailTrace_8243013 : CollatzResearch.WordTrace tailWord_8243013 prefixEnd_8243013 470291967806651434158731 := by
  unfold tailWord_8243013
  simp only [CollatzResearch.WordTrace]
  refine ⟨300647383285979170385261693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200431588857319446923507795 300647383285979170385261693)
  ·
    refine ⟨112742768732242188894473135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300647383285979170385261693 112742768732242188894473135)
    ·
      refine ⟨169114153098363283341709703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112742768732242188894473135 169114153098363283341709703)
      ·
        refine ⟨253671229647544925012564555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169114153098363283341709703 253671229647544925012564555)
        ·
          refine ⟨380506844471317387518846833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253671229647544925012564555 380506844471317387518846833)
          ·
            refine ⟨285380133353488040639135125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380506844471317387518846833 285380133353488040639135125)
            ·
              refine ⟨13377193750944751904959459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 285380133353488040639135125 13377193750944751904959459)
              ·
                refine ⟨20065790626417127857439189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13377193750944751904959459 20065790626417127857439189)
                ·
                  refine ⟨470291967806651434158731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20065790626417127857439189 470291967806651434158731)
                  ·
                    rfl

theorem cell23_8243013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_8243013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243013 prefixEnd_8243013 := by exact prefixLift 8243013
  have htrace : WordTrace (prefixWord ++ tailWord_8243013) baseStart_8243013 baseEnd_8243013 := by
    simpa [prefixWord, tailWord_8243013, baseEnd_8243013] using wordTrace_append hprefix tailTrace_8243013
  have hstable : (prefixWord ++ tailWord_8243013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243013).length < 2 ^ (prefixWord ++ tailWord_8243013).sum := by decide
  have hdescent : baseEnd_8243013 < baseStart_8243013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243107 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 1, 4]
def baseStart_8243107 : Nat := 118140960795 + 8243107 * 2 ^ 59
def prefixEnd_8243107 : Nat := 4983230072969 + 3 ^ 40 * 8243107 * 2
def baseEnd_8243107 : Nat := 1410891992480461846551049

theorem tailTrace_8243107 : CollatzResearch.WordTrace tailWord_8243107 prefixEnd_8243107 1410891992480461846551049 := by
  unfold tailWord_8243107
  simp only [CollatzResearch.WordTrace]
  refine ⟨300650811747638624439183575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200433874498425749626122383 300650811747638624439183575)
  ·
    refine ⟨450976217621457936658775363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300650811747638624439183575 450976217621457936658775363)
    ·
      refine ⟨676464326432186904988163045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450976217621457936658775363 676464326432186904988163045)
      ·
        refine ⟨126837061206035044685280571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 676464326432186904988163045 126837061206035044685280571)
        ·
          refine ⟨190255591809052567027920857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126837061206035044685280571 190255591809052567027920857)
          ·
            refine ⟨142691693856789425270940643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190255591809052567027920857 142691693856789425270940643)
            ·
              refine ⟨214037540785184137906410965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142691693856789425270940643 214037540785184137906410965)
              ·
                refine ⟨5016504862152753232181507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214037540785184137906410965 5016504862152753232181507)
                ·
                  refine ⟨7524757293229129848272261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016504862152753232181507 7524757293229129848272261)
                  ·
                    refine ⟨1410891992480461846551049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524757293229129848272261 1410891992480461846551049)
                    ·
                      rfl

theorem cell23_8243107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 4].length) (baseStart_8243107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243107 prefixEnd_8243107 := by exact prefixLift 8243107
  have htrace : WordTrace (prefixWord ++ tailWord_8243107) baseStart_8243107 baseEnd_8243107 := by
    simpa [prefixWord, tailWord_8243107, baseEnd_8243107] using wordTrace_append hprefix tailTrace_8243107
  have hstable : (prefixWord ++ tailWord_8243107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243107).length < 2 ^ (prefixWord ++ tailWord_8243107).sum := by decide
  have hdescent : baseEnd_8243107 < baseStart_8243107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243123 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_8243123 : Nat := 118140960795 + 8243123 * 2 ^ 59
def prefixEnd_8243123 : Nat := 4983230072969 + 3 ^ 40 * 8243123 * 2
def baseEnd_8243123 : Nat := 4232684193131857477053073

theorem tailTrace_8243123 : CollatzResearch.WordTrace tailWord_8243123 prefixEnd_8243123 4232684193131857477053073 := by
  unfold tailWord_8243123
  simp only [CollatzResearch.WordTrace]
  refine ⟨300651395315580659171766023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200434263543720439447844015 300651395315580659171766023)
  ·
    refine ⟨450977092973370988757649035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300651395315580659171766023 450977092973370988757649035)
    ·
      refine ⟨676465639460056483136473553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450977092973370988757649035 676465639460056483136473553)
      ·
        refine ⟨507349229595042362352355165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676465639460056483136473553 507349229595042362352355165)
        ·
          refine ⟨190255961098140885882133187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507349229595042362352355165 190255961098140885882133187)
          ·
            refine ⟨285383941647211328823199781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190255961098140885882133187 285383941647211328823199781)
            ·
              refine ⟨53509489058852124154349959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285383941647211328823199781 53509489058852124154349959)
              ·
                refine ⟨80264233588278186231524939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53509489058852124154349959 80264233588278186231524939)
                ·
                  refine ⟨120396350382417279347287409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80264233588278186231524939 120396350382417279347287409)
                  ·
                    refine ⟨90297262786812959510465557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120396350382417279347287409 90297262786812959510465557)
                    ·
                      refine ⟨4232684193131857477053073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90297262786812959510465557 4232684193131857477053073)
                      ·
                        rfl

theorem cell23_8243123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_8243123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243123 prefixEnd_8243123 := by exact prefixLift 8243123
  have htrace : WordTrace (prefixWord ++ tailWord_8243123) baseStart_8243123 baseEnd_8243123 := by
    simpa [prefixWord, tailWord_8243123, baseEnd_8243123] using wordTrace_append hprefix tailTrace_8243123
  have hstable : (prefixWord ++ tailWord_8243123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243123).length < 2 ^ (prefixWord ++ tailWord_8243123).sum := by decide
  have hdescent : baseEnd_8243123 < baseStart_8243123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243143 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_8243143 : Nat := 118140960795 + 8243143 * 2 ^ 59
def prefixEnd_8243143 : Nat := 4983230072969 + 3 ^ 40 * 8243143 * 2
def baseEnd_8243143 : Nat := 4232694462744947398802981

theorem tailTrace_8243143 : CollatzResearch.WordTrace tailWord_8243143 prefixEnd_8243143 4232694462744947398802981 := by
  unfold tailWord_8243143
  simp only [CollatzResearch.WordTrace]
  refine ⟨300652124775508202587494083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200434749850338801724996055 300652124775508202587494083)
  ·
    refine ⟨450978187163262303881241125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300652124775508202587494083 450978187163262303881241125)
    ·
      refine ⟨84558410093111681977732711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450978187163262303881241125 84558410093111681977732711)
      ·
        refine ⟨126837615139667522966599067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84558410093111681977732711 126837615139667522966599067)
        ·
          refine ⟨190256422709501284449898601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126837615139667522966599067 190256422709501284449898601)
          ·
            refine ⟨142692317032125963337423951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190256422709501284449898601 142692317032125963337423951)
            ·
              refine ⟨214038475548188945006135927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142692317032125963337423951 214038475548188945006135927)
              ·
                refine ⟨321057713322283417509203891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214038475548188945006135927 321057713322283417509203891)
                ·
                  refine ⟨481586569983425126263805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321057713322283417509203891 481586569983425126263805837)
                  ·
                    refine ⟨180594963743784422348927189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481586569983425126263805837 180594963743784422348927189)
                    ·
                      refine ⟨4232694462744947398802981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180594963743784422348927189 4232694462744947398802981)
                      ·
                        rfl

theorem cell23_8243143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_8243143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243143 prefixEnd_8243143 := by exact prefixLift 8243143
  have htrace : WordTrace (prefixWord ++ tailWord_8243143) baseStart_8243143 baseEnd_8243143 := by
    simpa [prefixWord, tailWord_8243143, baseEnd_8243143] using wordTrace_append hprefix tailTrace_8243143
  have hstable : (prefixWord ++ tailWord_8243143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243143).length < 2 ^ (prefixWord ++ tailWord_8243143).sum := by decide
  have hdescent : baseEnd_8243143 < baseStart_8243143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243147 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 3]
def baseStart_8243147 : Nat := 118140960795 + 8243147 * 2 ^ 59
def prefixEnd_8243147 : Nat := 4983230072969 + 3 ^ 40 * 8243147 * 2
def baseEnd_8243147 : Nat := 4232696516667565383152963

theorem tailTrace_8243147 : CollatzResearch.WordTrace tailWord_8243147 prefixEnd_8243147 4232696516667565383152963 := by
  unfold tailWord_8243147
  simp only [CollatzResearch.WordTrace]
  refine ⟨300652270667493711270639695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200434847111662474180426463 300652270667493711270639695)
  ·
    refine ⟨450978406001240566905959543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300652270667493711270639695 450978406001240566905959543)
    ·
      refine ⟨676467609001860850358939315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450978406001240566905959543 676467609001860850358939315)
      ·
        refine ⟨1014701413502791275538408973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676467609001860850358939315 1014701413502791275538408973)
        ·
          refine ⟨380513030063546728326903365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1014701413502791275538408973 380513030063546728326903365)
          ·
            refine ⟨71346193136915011561294381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380513030063546728326903365 71346193136915011561294381)
            ·
              refine ⟨26754822426343129335485393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71346193136915011561294381 26754822426343129335485393)
              ·
                refine ⟨20066116819757347001614045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26754822426343129335485393 20066116819757347001614045)
                ·
                  refine ⟨7524793807409005125605267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20066116819757347001614045 7524793807409005125605267)
                  ·
                    refine ⟨11287190711113507688407901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7524793807409005125605267 11287190711113507688407901)
                    ·
                      refine ⟨4232696516667565383152963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287190711113507688407901 4232696516667565383152963)
                      ·
                        rfl

theorem cell23_8243147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 3].length) (baseStart_8243147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243147 prefixEnd_8243147 := by exact prefixLift 8243147
  have htrace : WordTrace (prefixWord ++ tailWord_8243147) baseStart_8243147 baseEnd_8243147 := by
    simpa [prefixWord, tailWord_8243147, baseEnd_8243147] using wordTrace_append hprefix tailTrace_8243147
  have hstable : (prefixWord ++ tailWord_8243147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243147).length < 2 ^ (prefixWord ++ tailWord_8243147).sum := by decide
  have hdescent : baseEnd_8243147 < baseStart_8243147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243150 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_8243150 : Nat := 118140960795 + 8243150 * 2 ^ 59
def prefixEnd_8243150 : Nat := 4983230072969 + 3 ^ 40 * 8243150 * 2
def baseEnd_8243150 : Nat := 1410899352369842957138483

theorem tailTrace_8243150 : CollatzResearch.WordTrace tailWord_8243150 prefixEnd_8243150 1410899352369842957138483 := by
  unfold tailWord_8243150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581547510810355347874863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200434920057655228521999269 37581547510810355347874863)
  ·
    refine ⟨56372321266215533021812295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37581547510810355347874863 56372321266215533021812295)
    ·
      refine ⟨84558481899323299532718443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56372321266215533021812295 84558481899323299532718443)
      ·
        refine ⟨126837722848984949299077665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84558481899323299532718443 126837722848984949299077665)
        ·
          refine ⟨95128292136738711974308249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126837722848984949299077665 95128292136738711974308249)
          ·
            refine ⟨71346219102554033980731187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95128292136738711974308249 71346219102554033980731187)
            ·
              refine ⟨107019328653831050971096781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71346219102554033980731187 107019328653831050971096781)
              ·
                refine ⟨40132248245186644114161293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107019328653831050971096781 40132248245186644114161293)
                ·
                  refine ⟨15049593091944991542810485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40132248245186644114161293 15049593091944991542810485)
                  ·
                    refine ⟨1410899352369842957138483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15049593091944991542810485 1410899352369842957138483)
                    ·
                      rfl

theorem cell23_8243150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_8243150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243150 prefixEnd_8243150 := by exact prefixLift 8243150
  have htrace : WordTrace (prefixWord ++ tailWord_8243150) baseStart_8243150 baseEnd_8243150 := by
    simpa [prefixWord, tailWord_8243150, baseEnd_8243150] using wordTrace_append hprefix tailTrace_8243150
  have hstable : (prefixWord ++ tailWord_8243150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243150).length < 2 ^ (prefixWord ++ tailWord_8243150).sum := by decide
  have hdescent : baseEnd_8243150 < baseStart_8243150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243158 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_8243158 : Nat := 118140960795 + 8243158 * 2 ^ 59
def prefixEnd_8243158 : Nat := 4983230072969 + 3 ^ 40 * 8243158 * 2
def baseEnd_8243158 : Nat := 1410900721651588280038471

theorem tailTrace_8243158 : CollatzResearch.WordTrace tailWord_8243158 prefixEnd_8243158 1410900721651588280038471 := by
  unfold tailWord_8243158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790791991903366259330633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200435114580302573432860085 18790791991903366259330633)
  ·
    refine ⟨14093093993927524694497975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18790791991903366259330633 14093093993927524694497975)
    ·
      refine ⟨21139640990891287041746963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14093093993927524694497975 21139640990891287041746963)
      ·
        refine ⟨31709461486336930562620445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21139640990891287041746963 31709461486336930562620445)
        ·
          refine ⟨11891048057376348960982667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31709461486336930562620445 11891048057376348960982667)
          ·
            refine ⟨17836572086064523441474001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891048057376348960982667 17836572086064523441474001)
            ·
              refine ⟨13377429064548392581105501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17836572086064523441474001 13377429064548392581105501)
              ·
                refine ⟨5016535899205647217914563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13377429064548392581105501 5016535899205647217914563)
                ·
                  refine ⟨7524803848808470826871845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016535899205647217914563 7524803848808470826871845)
                  ·
                    refine ⟨1410900721651588280038471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524803848808470826871845 1410900721651588280038471)
                    ·
                      rfl

theorem cell23_8243158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_8243158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243158 prefixEnd_8243158 := by exact prefixLift 8243158
  have htrace : WordTrace (prefixWord ++ tailWord_8243158) baseStart_8243158 baseEnd_8243158 := by
    simpa [prefixWord, tailWord_8243158, baseEnd_8243158] using wordTrace_append hprefix tailTrace_8243158
  have hstable : (prefixWord ++ tailWord_8243158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243158).length < 2 ^ (prefixWord ++ tailWord_8243158).sum := by decide
  have hdescent : baseEnd_8243158 < baseStart_8243158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243167 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 1, 5]
def baseStart_8243167 : Nat := 118140960795 + 8243167 * 2 ^ 59
def prefixEnd_8243167 : Nat := 4983230072969 + 3 ^ 40 * 8243167 * 2
def baseEnd_8243167 : Nat := 1410902262093551768300957

theorem tailTrace_8243167 : CollatzResearch.WordTrace tailWord_8243167 prefixEnd_8243167 1410902262093551768300957 := by
  unfold tailWord_8243167
  simp only [CollatzResearch.WordTrace]
  refine ⟨300653000127421254686367755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200435333418280836457578503 300653000127421254686367755)
  ·
    refine ⟨450979500191131882029551633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300653000127421254686367755 450979500191131882029551633)
    ·
      refine ⟨338234625143348911522163725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450979500191131882029551633 338234625143348911522163725)
      ·
        refine ⟨126837984428755841820811397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338234625143348911522163725 126837984428755841820811397)
        ·
          refine ⟨23782122080391720341402137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126837984428755841820811397 23782122080391720341402137)
          ·
            refine ⟨17836591560293790256051603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23782122080391720341402137 17836591560293790256051603)
            ·
              refine ⟨26754887340440685384077405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836591560293790256051603 26754887340440685384077405)
              ·
                refine ⟨10033082752665257019029027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26754887340440685384077405 10033082752665257019029027)
                ·
                  refine ⟨15049624128997885528543541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033082752665257019029027 15049624128997885528543541)
                  ·
                    refine ⟨1410902262093551768300957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15049624128997885528543541 1410902262093551768300957)
                    ·
                      rfl

theorem cell23_8243167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_8243167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243167 prefixEnd_8243167 := by exact prefixLift 8243167
  have htrace : WordTrace (prefixWord ++ tailWord_8243167) baseStart_8243167 baseEnd_8243167 := by
    simpa [prefixWord, tailWord_8243167, baseEnd_8243167] using wordTrace_append hprefix tailTrace_8243167
  have hstable : (prefixWord ++ tailWord_8243167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243167).length < 2 ^ (prefixWord ++ tailWord_8243167).sum := by decide
  have hdescent : baseEnd_8243167 < baseStart_8243167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243197 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_8243197 : Nat := 118140960795 + 8243197 * 2 ^ 59
def prefixEnd_8243197 : Nat := 4983230072969 + 3 ^ 40 * 8243197 * 2
def baseEnd_8243197 : Nat := 1410907396900096729175911

theorem tailTrace_8243197 : CollatzResearch.WordTrace tailWord_8243197 prefixEnd_8243197 1410907396900096729175911 := by
  unfold tailWord_8243197
  simp only [CollatzResearch.WordTrace]
  refine ⟨300654094317312569809959845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200436062878208379873306563 300654094317312569809959845)
  ·
    refine ⟨56372642684496106839367471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300654094317312569809959845 56372642684496106839367471)
    ·
      refine ⟨84558964026744160259051207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56372642684496106839367471 84558964026744160259051207)
      ·
        refine ⟨126838446040116240388576811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84558964026744160259051207 126838446040116240388576811)
        ·
          refine ⟨190257669060174360582865217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126838446040116240388576811 190257669060174360582865217)
          ·
            refine ⟨142693251795130770437148913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190257669060174360582865217 142693251795130770437148913)
            ·
              refine ⟨107019938846348077827861685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142693251795130770437148913 107019938846348077827861685)
              ·
                refine ⟨10033119266845132296362033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107019938846348077827861685 10033119266845132296362033)
                ·
                  refine ⟨7524839450133849222271525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10033119266845132296362033 7524839450133849222271525)
                  ·
                    refine ⟨1410907396900096729175911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524839450133849222271525 1410907396900096729175911)
                    ·
                      rfl

theorem cell23_8243197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_8243197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243197 prefixEnd_8243197 := by exact prefixLift 8243197
  have htrace : WordTrace (prefixWord ++ tailWord_8243197) baseStart_8243197 baseEnd_8243197 := by
    simpa [prefixWord, tailWord_8243197, baseEnd_8243197] using wordTrace_append hprefix tailTrace_8243197
  have hstable : (prefixWord ++ tailWord_8243197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243197).length < 2 ^ (prefixWord ++ tailWord_8243197).sum := by decide
  have hdescent : baseEnd_8243197 < baseStart_8243197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243200 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_8243200 : Nat := 118140960795 + 8243200 * 2 ^ 59
def prefixEnd_8243200 : Nat := 4983230072969 + 3 ^ 40 * 8243200 * 2
def baseEnd_8243200 : Nat := 4232723731142253675790219

theorem tailTrace_8243200 : CollatzResearch.WordTrace tailWord_8243200 prefixEnd_8243200 4232723731142253675790219 := by
  unfold tailWord_8243200
  simp only [CollatzResearch.WordTrace]
  refine ⟨150327101868150850661159527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200436135824201134214879369 150327101868150850661159527)
  ·
    refine ⟨225490652802226275991739291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150327101868150850661159527 225490652802226275991739291)
    ·
      refine ⟨338235979203339413987608937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225490652802226275991739291 338235979203339413987608937)
      ·
        refine ⟨253676984402504560490706703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338235979203339413987608937 253676984402504560490706703)
        ·
          refine ⟨380515476603756840736060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253676984402504560490706703 380515476603756840736060055)
          ·
            refine ⟨570773214905635261104090083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380515476603756840736060055 570773214905635261104090083)
            ·
              refine ⟨856159822358452891656135125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570773214905635261104090083 856159822358452891656135125)
              ·
                refine ⟨20066245836526239648190667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 856159822358452891656135125 20066245836526239648190667)
                ·
                  refine ⟨30099368754789359472286001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20066245836526239648190667 30099368754789359472286001)
                  ·
                    refine ⟨22574526566092019604214501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30099368754789359472286001 22574526566092019604214501)
                    ·
                      refine ⟨4232723731142253675790219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22574526566092019604214501 4232723731142253675790219)
                      ·
                        rfl

theorem cell23_8243200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_8243200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243200 prefixEnd_8243200 := by exact prefixLift 8243200
  have htrace : WordTrace (prefixWord ++ tailWord_8243200) baseStart_8243200 baseEnd_8243200 := by
    simpa [prefixWord, tailWord_8243200, baseEnd_8243200] using wordTrace_append hprefix tailTrace_8243200
  have hstable : (prefixWord ++ tailWord_8243200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243200).length < 2 ^ (prefixWord ++ tailWord_8243200).sum := by decide
  have hdescent : baseEnd_8243200 < baseStart_8243200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243254 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_8243254 : Nat := 118140960795 + 8243254 * 2 ^ 59
def prefixEnd_8243254 : Nat := 4983230072969 + 3 ^ 40 * 8243254 * 2
def baseEnd_8243254 : Nat := 4232751459097596464514971

theorem tailTrace_8243254 : CollatzResearch.WordTrace tailWord_8243254 prefixEnd_8243254 4232751459097596464514971 := by
  unfold tailWord_8243254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18791010829881629284049051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200437448852070712363189877 18791010829881629284049051)
  ·
    refine ⟨28186516244822443926073577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18791010829881629284049051 28186516244822443926073577)
    ·
      refine ⟨21139887183616832944555183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28186516244822443926073577 21139887183616832944555183)
      ·
        refine ⟨31709830775425249416832775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21139887183616832944555183 31709830775425249416832775)
        ·
          refine ⟨47564746163137874125249163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31709830775425249416832775 47564746163137874125249163)
          ·
            refine ⟨71347119244706811187873745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47564746163137874125249163 71347119244706811187873745)
            ·
              refine ⟨53510339433530108390905309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71347119244706811187873745 53510339433530108390905309)
              ·
                refine ⟨20066377287573790646589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53510339433530108390905309 20066377287573790646589491)
                ·
                  refine ⟨30099565931360685969884237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20066377287573790646589491 30099565931360685969884237)
                  ·
                    refine ⟨11287337224260257238706589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30099565931360685969884237 11287337224260257238706589)
                    ·
                      refine ⟨4232751459097596464514971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287337224260257238706589 4232751459097596464514971)
                      ·
                        rfl

theorem cell23_8243254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_8243254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243254 prefixEnd_8243254 := by exact prefixLift 8243254
  have htrace : WordTrace (prefixWord ++ tailWord_8243254) baseStart_8243254 baseEnd_8243254 := by
    simpa [prefixWord, tailWord_8243254, baseEnd_8243254] using wordTrace_append hprefix tailTrace_8243254
  have hstable : (prefixWord ++ tailWord_8243254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243254).length < 2 ^ (prefixWord ++ tailWord_8243254).sum := by decide
  have hdescent : baseEnd_8243254 < baseStart_8243254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243264 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2]
def baseStart_8243264 : Nat := 118140960795 + 8243264 * 2 ^ 59
def prefixEnd_8243264 : Nat := 4983230072969 + 3 ^ 40 * 8243264 * 2
def baseEnd_8243264 : Nat := 4232756593904141425389925

theorem tailTrace_8243264 : CollatzResearch.WordTrace tailWord_8243264 prefixEnd_8243264 4232756593904141425389925 := by
  unfold tailWord_8243264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150328269004034920126324423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200437692005379893501765897 150328269004034920126324423)
  ·
    refine ⟨225492403506052380189486635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150328269004034920126324423 225492403506052380189486635)
    ·
      refine ⟨338238605259078570284229953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225492403506052380189486635 338238605259078570284229953)
      ·
        refine ⟨253678953944308927713172465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338238605259078570284229953 253678953944308927713172465)
        ·
          refine ⟨190259215458231695784879349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253678953944308927713172465 190259215458231695784879349)
          ·
            refine ⟨17836801449209221479832439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190259215458231695784879349 17836801449209221479832439)
            ·
              refine ⟨26755202173813832219748659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836801449209221479832439 26755202173813832219748659)
              ·
                refine ⟨40132803260720748329622989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26755202173813832219748659 40132803260720748329622989)
                ·
                  refine ⟨15049801222770280623608621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40132803260720748329622989 15049801222770280623608621)
                  ·
                    refine ⟨5643675458538855233853233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15049801222770280623608621 5643675458538855233853233)
                    ·
                      refine ⟨4232756593904141425389925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643675458538855233853233 4232756593904141425389925)
                      ·
                        rfl

theorem cell23_8243264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_8243264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243264 prefixEnd_8243264 := by exact prefixLift 8243264
  have htrace : WordTrace (prefixWord ++ tailWord_8243264) baseStart_8243264 baseEnd_8243264 := by
    simpa [prefixWord, tailWord_8243264, baseEnd_8243264] using wordTrace_append hprefix tailTrace_8243264
  have hstable : (prefixWord ++ tailWord_8243264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243264).length < 2 ^ (prefixWord ++ tailWord_8243264).sum := by decide
  have hdescent : baseEnd_8243264 < baseStart_8243264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243311 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 2, 2, 2]
def baseStart_8243311 : Nat := 118140960795 + 8243311 * 2 ^ 59
def prefixEnd_8243311 : Nat := 4983230072969 + 3 ^ 40 * 8243311 * 2
def baseEnd_8243311 : Nat := 4232780727494902741502209

theorem tailTrace_8243311 : CollatzResearch.WordTrace tailWord_8243311 prefixEnd_8243311 4232780727494902741502209 := by
  unfold tailWord_8243311
  simp only [CollatzResearch.WordTrace]
  refine ⟨300658252238899567279609787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200438834825933044853073191 300658252238899567279609787)
  ·
    refine ⟨450987378358349350919414681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300658252238899567279609787 450987378358349350919414681)
    ·
      refine ⟨338240533768762013189561011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450987378358349350919414681 338240533768762013189561011)
      ·
        refine ⟨507360800653143019784341517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338240533768762013189561011 507360800653143019784341517)
        ·
          refine ⟨190260300244928632419128069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507360800653143019784341517 190260300244928632419128069)
          ·
            refine ⟨35673806295924118578586513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190260300244928632419128069 35673806295924118578586513)
            ·
              refine ⟨26755354721943088933939885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35673806295924118578586513 26755354721943088933939885)
              ·
                refine ⟨10033258020728658350227457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26755354721943088933939885 10033258020728658350227457)
                ·
                  refine ⟨7524943515546493762670593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10033258020728658350227457 7524943515546493762670593)
                  ·
                    refine ⟨5643707636659870322002945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7524943515546493762670593 5643707636659870322002945)
                    ·
                      refine ⟨4232780727494902741502209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643707636659870322002945 4232780727494902741502209)
                      ·
                        rfl

theorem cell23_8243311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2, 2].length) (baseStart_8243311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243311 prefixEnd_8243311 := by exact prefixLift 8243311
  have htrace : WordTrace (prefixWord ++ tailWord_8243311) baseStart_8243311 baseEnd_8243311 := by
    simpa [prefixWord, tailWord_8243311, baseEnd_8243311] using wordTrace_append hprefix tailTrace_8243311
  have hstable : (prefixWord ++ tailWord_8243311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243311).length < 2 ^ (prefixWord ++ tailWord_8243311).sum := by decide
  have hdescent : baseEnd_8243311 < baseStart_8243311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243387 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3]
def baseStart_8243387 : Nat := 118140960795 + 8243387 * 2 ^ 59
def prefixEnd_8243387 : Nat := 4983230072969 + 3 ^ 40 * 8243387 * 2
def baseEnd_8243387 : Nat := 4232819752024644444151859

theorem tailTrace_8243387 : CollatzResearch.WordTrace tailWord_8243387 prefixEnd_8243387 4232819752024644444151859 := by
  unfold tailWord_8243387
  simp only [CollatzResearch.WordTrace]
  refine ⟨300661024186624232259376415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200440682791082821506250943 300661024186624232259376415)
  ·
    refine ⟨450991536279936348389064623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300661024186624232259376415 450991536279936348389064623)
    ·
      refine ⟨676487304419904522583596935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450991536279936348389064623 676487304419904522583596935)
      ·
        refine ⟨1014730956629856783875395403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676487304419904522583596935 1014730956629856783875395403)
        ·
          refine ⟨1522096434944785175813093105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014730956629856783875395403 1522096434944785175813093105)
          ·
            refine ⟨1141572326208588881859819829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522096434944785175813093105 1141572326208588881859819829)
            ·
              refine ⟨107022405582055207674358109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1141572326208588881859819829 107022405582055207674358109)
              ·
                refine ⟨40133402093270702877884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107022405582055207674358109 40133402093270702877884291)
                ·
                  refine ⟨60200103139906054316826437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40133402093270702877884291 60200103139906054316826437)
                  ·
                    refine ⟨11287519338732385184404957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60200103139906054316826437 11287519338732385184404957)
                    ·
                      refine ⟨4232819752024644444151859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287519338732385184404957 4232819752024644444151859)
                      ·
                        rfl

theorem cell23_8243387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].length) (baseStart_8243387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243387 prefixEnd_8243387 := by exact prefixLift 8243387
  have htrace : WordTrace (prefixWord ++ tailWord_8243387) baseStart_8243387 baseEnd_8243387 := by
    simpa [prefixWord, tailWord_8243387, baseEnd_8243387] using wordTrace_append hprefix tailTrace_8243387
  have hstable : (prefixWord ++ tailWord_8243387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243387).length < 2 ^ (prefixWord ++ tailWord_8243387).sum := by decide
  have hdescent : baseEnd_8243387 < baseStart_8243387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243407 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 6]
def baseStart_8243407 : Nat := 118140960795 + 8243407 * 2 ^ 59
def prefixEnd_8243407 : Nat := 4983230072969 + 3 ^ 40 * 8243407 * 2
def baseEnd_8243407 : Nat := 470314446848637151766863

theorem tailTrace_8243407 : CollatzResearch.WordTrace tailWord_8243407 prefixEnd_8243407 470314446848637151766863 := by
  unfold tailWord_8243407
  simp only [CollatzResearch.WordTrace]
  refine ⟨300661753646551775675104475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200441169097701183783402983 300661753646551775675104475)
  ·
    refine ⟨450992630469827663512656713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300661753646551775675104475 450992630469827663512656713)
    ·
      refine ⟨338244472852370747634492535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450992630469827663512656713 338244472852370747634492535)
      ·
        refine ⟨507366709278556121451738803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338244472852370747634492535 507366709278556121451738803)
        ·
          refine ⟨761050063917834182177608205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507366709278556121451738803 761050063917834182177608205)
          ·
            refine ⟨285393773969187818316603077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761050063917834182177608205 285393773969187818316603077)
            ·
              refine ⟨53511332619222715934363077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285393773969187818316603077 53511332619222715934363077)
              ·
                refine ⟨10033374866104259237693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53511332619222715934363077 10033374866104259237693077)
                ·
                  refine ⟨470314446848637151766863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10033374866104259237693077 470314446848637151766863)
                  ·
                    rfl

theorem cell23_8243407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 6].length) (baseStart_8243407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243407 prefixEnd_8243407 := by exact prefixLift 8243407
  have htrace : WordTrace (prefixWord ++ tailWord_8243407) baseStart_8243407 baseEnd_8243407 := by
    simpa [prefixWord, tailWord_8243407, baseEnd_8243407] using wordTrace_append hprefix tailTrace_8243407
  have hstable : (prefixWord ++ tailWord_8243407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243407).length < 2 ^ (prefixWord ++ tailWord_8243407).sum := by decide
  have hdescent : baseEnd_8243407 < baseStart_8243407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243467 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 6]
def baseStart_8243467 : Nat := 118140960795 + 8243467 * 2 ^ 59
def prefixEnd_8243467 : Nat := 4983230072969 + 3 ^ 40 * 8243467 * 2
def baseEnd_8243467 : Nat := 1410953610159001377050497

theorem tailTrace_8243467 : CollatzResearch.WordTrace tailWord_8243467 prefixEnd_8243467 1410953610159001377050497 := by
  unfold tailWord_8243467
  simp only [CollatzResearch.WordTrace]
  refine ⟨300663942026334405922288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200442628017556270614859103 300663942026334405922288655)
  ·
    refine ⟨450995913039501608883432983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300663942026334405922288655 450995913039501608883432983)
    ·
      refine ⟨676493869559252413325149475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450995913039501608883432983 676493869559252413325149475)
      ·
        refine ⟨1014740804338878619987724213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676493869559252413325149475 1014740804338878619987724213)
        ·
          refine ⟨95131950406769870623849145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1014740804338878619987724213 95131950406769870623849145)
          ·
            refine ⟨71348962805077402967886859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95131950406769870623849145 71348962805077402967886859)
            ·
              refine ⟨107023444207616104451830289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71348962805077402967886859 107023444207616104451830289)
              ·
                refine ⟨80267583155712078338872717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107023444207616104451830289 80267583155712078338872717)
                ·
                  refine ⟨30100343683392029377077269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80267583155712078338872717 30100343683392029377077269)
                  ·
                    refine ⟨1410953610159001377050497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30100343683392029377077269 1410953610159001377050497)
                    ·
                      rfl

theorem cell23_8243467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_8243467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243467 prefixEnd_8243467 := by exact prefixLift 8243467
  have htrace : WordTrace (prefixWord ++ tailWord_8243467) baseStart_8243467 baseEnd_8243467 := by
    simpa [prefixWord, tailWord_8243467, baseEnd_8243467] using wordTrace_append hprefix tailTrace_8243467
  have hstable : (prefixWord ++ tailWord_8243467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243467).length < 2 ^ (prefixWord ++ tailWord_8243467).sum := by decide
  have hdescent : baseEnd_8243467 < baseStart_8243467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243468 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_8243468 : Nat := 118140960795 + 8243468 * 2 ^ 59
def prefixEnd_8243468 : Nat := 4983230072969 + 3 ^ 40 * 8243468 * 2
def baseEnd_8243468 : Nat := 4232861343957658627238987

theorem tailTrace_8243468 : CollatzResearch.WordTrace tailWord_8243468 prefixEnd_8243468 4232861343957658627238987 := by
  unfold tailWord_8243468
  simp only [CollatzResearch.WordTrace]
  refine ⟨150331989249665391546537529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200442652332887188728716705 150331989249665391546537529)
  ·
    refine ⟨112748991937249043659903147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150331989249665391546537529 112748991937249043659903147)
    ·
      refine ⟨169123487905873565489854721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112748991937249043659903147 169123487905873565489854721)
      ·
        refine ⟨126842615929405174117391041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169123487905873565489854721 126842615929405174117391041)
        ·
          refine ⟨95131961947053880588043281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126842615929405174117391041 95131961947053880588043281)
          ·
            refine ⟨71348971460290410441032461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95131961947053880588043281 71348971460290410441032461)
            ·
              refine ⟨26755864297608903915387173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71348971460290410441032461 26755864297608903915387173)
              ·
                refine ⟨5016724555801669484135095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26755864297608903915387173 5016724555801669484135095)
                ·
                  refine ⟨7525086833702504226202643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016724555801669484135095 7525086833702504226202643)
                  ·
                    refine ⟨11287630250553756339303965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525086833702504226202643 11287630250553756339303965)
                    ·
                      refine ⟨4232861343957658627238987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287630250553756339303965 4232861343957658627238987)
                      ·
                        rfl

theorem cell23_8243468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_8243468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243468 prefixEnd_8243468 := by exact prefixLift 8243468
  have htrace : WordTrace (prefixWord ++ tailWord_8243468) baseStart_8243468 baseEnd_8243468 := by
    simpa [prefixWord, tailWord_8243468, baseEnd_8243468] using wordTrace_append hprefix tailTrace_8243468
  have hstable : (prefixWord ++ tailWord_8243468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243468).length < 2 ^ (prefixWord ++ tailWord_8243468).sum := by decide
  have hdescent : baseEnd_8243468 < baseStart_8243468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243484 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_8243484 : Nat := 118140960795 + 8243484 * 2 ^ 59
def prefixEnd_8243484 : Nat := 4983230072969 + 3 ^ 40 * 8243484 * 2
def baseEnd_8243484 : Nat := 1410956519882710188212971

theorem tailTrace_8243484 : CollatzResearch.WordTrace tailWord_8243484 prefixEnd_8243484 1410956519882710188212971 := by
  unfold tailWord_8243484
  simp only [CollatzResearch.WordTrace]
  refine ⟨150332281033636408912828753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200443041378181878550438337 150332281033636408912828753)
  ·
    refine ⟨112749210775227306684621565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150332281033636408912828753 112749210775227306684621565)
    ·
      refine ⟨42280954040710240006733087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112749210775227306684621565 42280954040710240006733087)
      ·
        refine ⟨63421431061065360010099631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42280954040710240006733087 63421431061065360010099631)
        ·
          refine ⟨95132146591598040015149447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63421431061065360010099631 95132146591598040015149447)
          ·
            refine ⟨142698219887397060022724171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95132146591598040015149447 142698219887397060022724171)
            ·
              refine ⟨214047329831095590034086257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142698219887397060022724171 214047329831095590034086257)
              ·
                refine ⟨160535497373321692525564693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214047329831095590034086257 160535497373321692525564693)
                ·
                  refine ⟨7525101439374454337135845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160535497373321692525564693 7525101439374454337135845)
                  ·
                    refine ⟨1410956519882710188212971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525101439374454337135845 1410956519882710188212971)
                    ·
                      rfl

theorem cell23_8243484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_8243484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243484 prefixEnd_8243484 := by exact prefixLift 8243484
  have htrace : WordTrace (prefixWord ++ tailWord_8243484) baseStart_8243484 baseEnd_8243484 := by
    simpa [prefixWord, tailWord_8243484, baseEnd_8243484] using wordTrace_append hprefix tailTrace_8243484
  have hstable : (prefixWord ++ tailWord_8243484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243484).length < 2 ^ (prefixWord ++ tailWord_8243484).sum := by decide
  have hdescent : baseEnd_8243484 < baseStart_8243484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243505 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_8243505 : Nat := 118140960795 + 8243505 * 2 ^ 59
def prefixEnd_8243505 : Nat := 4983230072969 + 3 ^ 40 * 8243505 * 2
def baseEnd_8243505 : Nat := 1410960114247291660825439

theorem tailTrace_8243505 : CollatzResearch.WordTrace tailWord_8243505 prefixEnd_8243505 1410960114247291660825439 := by
  unfold tailWord_8243505
  simp only [CollatzResearch.WordTrace]
  refine ⟨300665328000196738412171969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200443552000131158941447979 300665328000196738412171969)
  ·
    refine ⟨225498996000147553809128977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300665328000196738412171969 225498996000147553809128977)
    ·
      refine ⟨169124247000110665356846733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225498996000147553809128977 169124247000110665356846733)
      ·
        refine ⟨63421592625041499508817525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169124247000110665356846733 63421592625041499508817525)
        ·
          refine ⟨5945774308597640578951643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63421592625041499508817525 5945774308597640578951643)
          ·
            refine ⟨8918661462896460868427465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945774308597640578951643 8918661462896460868427465)
            ·
              refine ⟨6688996097172345651320599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8918661462896460868427465 6688996097172345651320599)
              ·
                refine ⟨10033494145758518476980899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688996097172345651320599 10033494145758518476980899)
                ·
                  refine ⟨15050241218637777715471349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033494145758518476980899 15050241218637777715471349)
                  ·
                    refine ⟨1410960114247291660825439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15050241218637777715471349 1410960114247291660825439)
                    ·
                      rfl

theorem cell23_8243505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_8243505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243505 prefixEnd_8243505 := by exact prefixLift 8243505
  have htrace : WordTrace (prefixWord ++ tailWord_8243505) baseStart_8243505 baseEnd_8243505 := by
    simpa [prefixWord, tailWord_8243505, baseEnd_8243505] using wordTrace_append hprefix tailTrace_8243505
  have hstable : (prefixWord ++ tailWord_8243505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243505).length < 2 ^ (prefixWord ++ tailWord_8243505).sum := by decide
  have hdescent : baseEnd_8243505 < baseStart_8243505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243508 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_8243508 : Nat := 118140960795 + 8243508 * 2 ^ 59
def prefixEnd_8243508 : Nat := 4983230072969 + 3 ^ 40 * 8243508 * 2
def baseEnd_8243508 : Nat := 4232881883183838470738803

theorem tailTrace_8243508 : CollatzResearch.WordTrace tailWord_8243508 prefixEnd_8243508 4232881883183838470738803 := by
  unfold tailWord_8243508
  simp only [CollatzResearch.WordTrace]
  refine ⟨150332718709592934962265589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200443624946123913283020785 150332718709592934962265589)
  ·
    refine ⟨14093692379024337652712399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150332718709592934962265589 14093692379024337652712399)
    ·
      refine ⟨21140538568536506479068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14093692379024337652712399 21140538568536506479068599)
      ·
        refine ⟨31710807852804759718602899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21140538568536506479068599 31710807852804759718602899)
        ·
          refine ⟨47566211779207139577904349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710807852804759718602899 47566211779207139577904349)
          ·
            refine ⟨17837329417202677341714131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47566211779207139577904349 17837329417202677341714131)
            ·
              refine ⟨26755994125804016012571197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837329417202677341714131 26755994125804016012571197)
              ·
                refine ⟨10033497797176506004714199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26755994125804016012571197 10033497797176506004714199)
                ·
                  refine ⟨15050246695764759007071299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033497797176506004714199 15050246695764759007071299)
                  ·
                    refine ⟨22575370043647138510606949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15050246695764759007071299 22575370043647138510606949)
                    ·
                      refine ⟨4232881883183838470738803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22575370043647138510606949 4232881883183838470738803)
                      ·
                        rfl

theorem cell23_8243508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_8243508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243508 prefixEnd_8243508 := by exact prefixLift 8243508
  have htrace : WordTrace (prefixWord ++ tailWord_8243508) baseStart_8243508 baseEnd_8243508 := by
    simpa [prefixWord, tailWord_8243508, baseEnd_8243508] using wordTrace_append hprefix tailTrace_8243508
  have hstable : (prefixWord ++ tailWord_8243508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243508).length < 2 ^ (prefixWord ++ tailWord_8243508).sum := by decide
  have hdescent : baseEnd_8243508 < baseStart_8243508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243518 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_8243518 : Nat := 118140960795 + 8243518 * 2 ^ 59
def prefixEnd_8243518 : Nat := 4983230072969 + 3 ^ 40 * 8243518 * 2
def baseEnd_8243518 : Nat := 1410962339330127810537919

theorem tailTrace_8243518 : CollatzResearch.WordTrace tailWord_8243518 prefixEnd_8243518 1410962339330127810537919 := by
  unfold tailWord_8243518
  simp only [CollatzResearch.WordTrace]
  refine ⟨37583225268643705204049401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200443868099433094421596805 37583225268643705204049401)
  ·
    refine ⟨28187418951482778903037051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37583225268643705204049401 28187418951482778903037051)
    ·
      refine ⟨42281128427224168354555577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28187418951482778903037051 42281128427224168354555577)
      ·
        refine ⟨31710846320418126265916683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42281128427224168354555577 31710846320418126265916683)
        ·
          refine ⟨47566269480627189398875025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710846320418126265916683 47566269480627189398875025)
          ·
            refine ⟨35674702110470392049156269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47566269480627189398875025 35674702110470392049156269)
            ·
              refine ⟨13378013291426397018433601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35674702110470392049156269 13378013291426397018433601)
              ·
                refine ⟨10033509968569797763825201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13378013291426397018433601 10033509968569797763825201)
                ·
                  refine ⟨7525132476427348322868901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10033509968569797763825201 7525132476427348322868901)
                  ·
                    refine ⟨1410962339330127810537919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525132476427348322868901 1410962339330127810537919)
                    ·
                      rfl

theorem cell23_8243518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_8243518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243518 prefixEnd_8243518 := by exact prefixLift 8243518
  have htrace : WordTrace (prefixWord ++ tailWord_8243518) baseStart_8243518 baseEnd_8243518 := by
    simpa [prefixWord, tailWord_8243518, baseEnd_8243518] using wordTrace_append hprefix tailTrace_8243518
  have hstable : (prefixWord ++ tailWord_8243518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243518).length < 2 ^ (prefixWord ++ tailWord_8243518).sum := by decide
  have hdescent : baseEnd_8243518 < baseStart_8243518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243551 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 3, 3, 2]
def baseStart_8243551 : Nat := 118140960795 + 8243551 * 2 ^ 59
def prefixEnd_8243551 : Nat := 4983230072969 + 3 ^ 40 * 8243551 * 2
def baseEnd_8243551 : Nat := 4232903962851981802501105

theorem tailTrace_8243551 : CollatzResearch.WordTrace tailWord_8243551 prefixEnd_8243551 4232903962851981802501105 := by
  unfold tailWord_8243551
  simp only [CollatzResearch.WordTrace]
  refine ⟨300667005758030088268346507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200444670505353392178897671 300667005758030088268346507)
  ·
    refine ⟨451000508637045132402519761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300667005758030088268346507 451000508637045132402519761)
    ·
      refine ⟨338250381477783849301889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451000508637045132402519761 338250381477783849301889821)
      ·
        refine ⟨126843893054168943488208683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338250381477783849301889821 126843893054168943488208683)
        ·
          refine ⟨190265839581253415232313025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126843893054168943488208683 190265839581253415232313025)
          ·
            refine ⟨142699379685940061424234769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190265839581253415232313025 142699379685940061424234769)
            ·
              refine ⟨107024534764455046068176077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142699379685940061424234769 107024534764455046068176077)
              ·
                refine ⟨40134200536670642275566029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107024534764455046068176077 40134200536670642275566029)
                ·
                  refine ⟨15050325201251490853337261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40134200536670642275566029 15050325201251490853337261)
                  ·
                    refine ⟨5643871950469309070001473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15050325201251490853337261 5643871950469309070001473)
                    ·
                      refine ⟨4232903962851981802501105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643871950469309070001473 4232903962851981802501105)
                      ·
                        rfl

theorem cell23_8243551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_8243551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243551 prefixEnd_8243551 := by exact prefixLift 8243551
  have htrace : WordTrace (prefixWord ++ tailWord_8243551) baseStart_8243551 baseEnd_8243551 := by
    simpa [prefixWord, tailWord_8243551, baseEnd_8243551] using wordTrace_append hprefix tailTrace_8243551
  have hstable : (prefixWord ++ tailWord_8243551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243551).length < 2 ^ (prefixWord ++ tailWord_8243551).sum := by decide
  have hdescent : baseEnd_8243551 < baseStart_8243551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243568 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2]
def baseStart_8243568 : Nat := 118140960795 + 8243568 * 2 ^ 59
def prefixEnd_8243568 : Nat := 4983230072969 + 3 ^ 40 * 8243568 * 2
def baseEnd_8243568 : Nat := 4232912692023108235988527

theorem tailTrace_8243568 : CollatzResearch.WordTrace tailWord_8243568 prefixEnd_8243568 4232912692023108235988527 := by
  unfold tailWord_8243568
  simp only [CollatzResearch.WordTrace]
  refine ⟨150333812899484250085857679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200445083865979000114476905 150333812899484250085857679)
  ·
    refine ⟨225500719349226375128786519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150333812899484250085857679 225500719349226375128786519)
    ·
      refine ⟨338251079023839562693179779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225500719349226375128786519 338251079023839562693179779)
      ·
        refine ⟨507376618535759344039769669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338251079023839562693179779 507376618535759344039769669)
        ·
          refine ⟨95133115975454877007456813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507376618535759344039769669 95133115975454877007456813)
          ·
            refine ⟨35674918490795578877796305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95133115975454877007456813 35674918490795578877796305)
            ·
              refine ⟨26756188868096684158347229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35674918490795578877796305 26756188868096684158347229)
              ·
                refine ⟨10033570825536256559380211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26756188868096684158347229 10033570825536256559380211)
                ·
                  refine ⟨15050356238304384839070317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033570825536256559380211 15050356238304384839070317)
                  ·
                    refine ⟨5643883589364144314651369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15050356238304384839070317 5643883589364144314651369)
                    ·
                      refine ⟨4232912692023108235988527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643883589364144314651369 4232912692023108235988527)
                      ·
                        rfl

theorem cell23_8243568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 3, 2].length) (baseStart_8243568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243568 prefixEnd_8243568 := by exact prefixLift 8243568
  have htrace : WordTrace (prefixWord ++ tailWord_8243568) baseStart_8243568 baseEnd_8243568 := by
    simpa [prefixWord, tailWord_8243568, baseEnd_8243568] using wordTrace_append hprefix tailTrace_8243568
  have hstable : (prefixWord ++ tailWord_8243568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243568).length < 2 ^ (prefixWord ++ tailWord_8243568).sum := by decide
  have hdescent : baseEnd_8243568 < baseStart_8243568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243621 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 5]
def baseStart_8243621 : Nat := 118140960795 + 8243621 * 2 ^ 59
def prefixEnd_8243621 : Nat := 4983230072969 + 3 ^ 40 * 8243621 * 2
def baseEnd_8243621 : Nat := 470326656277532947625087

theorem tailTrace_8243621 : CollatzResearch.WordTrace tailWord_8243621 prefixEnd_8243621 470326656277532947625087 := by
  unfold tailWord_8243621
  simp only [CollatzResearch.WordTrace]
  refine ⟨300669558867776490223394717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200446372578517660148929811 300669558867776490223394717)
  ·
    refine ⟨112751084575416183833773019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300669558867776490223394717 112751084575416183833773019)
    ·
      refine ⟨169126626863124275750659529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112751084575416183833773019 169126626863124275750659529)
      ·
        refine ⟨126844970147343206812994647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169126626863124275750659529 126844970147343206812994647)
        ·
          refine ⟨190267455221014810219491971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126844970147343206812994647 190267455221014810219491971)
          ·
            refine ⟨285401182831522215329237957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190267455221014810219491971 285401182831522215329237957)
            ·
              refine ⟨53512721780910415374232117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285401182831522215329237957 53512721780910415374232117)
              ·
                refine ⟨5016817666960351441334261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53512721780910415374232117 5016817666960351441334261)
                ·
                  refine ⟨470326656277532947625087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016817666960351441334261 470326656277532947625087)
                  ·
                    rfl

theorem cell23_8243621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_8243621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243621 prefixEnd_8243621 := by exact prefixLift 8243621
  have htrace : WordTrace (prefixWord ++ tailWord_8243621) baseStart_8243621 baseEnd_8243621 := by
    simpa [prefixWord, tailWord_8243621, baseEnd_8243621] using wordTrace_append hprefix tailTrace_8243621
  have hstable : (prefixWord ++ tailWord_8243621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243621).length < 2 ^ (prefixWord ++ tailWord_8243621).sum := by decide
  have hdescent : baseEnd_8243621 < baseStart_8243621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243649 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8243649 : Nat := 118140960795 + 8243649 * 2 ^ 59
def prefixEnd_8243649 : Nat := 4983230072969 + 3 ^ 40 * 8243649 * 2
def baseEnd_8243649 : Nat := 4232954283956122419075655

theorem tailTrace_8243649 : CollatzResearch.WordTrace tailWord_8243649 prefixEnd_8243649 4232954283956122419075655 := by
  unfold tailWord_8243649
  simp only [CollatzResearch.WordTrace]
  refine ⟨300670580111675051005414001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200447053407783367336942667 300670580111675051005414001)
  ·
    refine ⟨225502935083756288254060501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300670580111675051005414001 225502935083756288254060501)
    ·
      refine ⟨5285225041025538005954543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225502935083756288254060501 5285225041025538005954543)
      ·
        refine ⟨7927837561538307008931815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285225041025538005954543 7927837561538307008931815)
        ·
          refine ⟨11891756342307460513397723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927837561538307008931815 11891756342307460513397723)
          ·
            refine ⟨17837634513461190770096585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891756342307460513397723 17837634513461190770096585)
            ·
              refine ⟨13378225885095893077572439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17837634513461190770096585 13378225885095893077572439)
              ·
                refine ⟨20067338827643839616358659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378225885095893077572439 20067338827643839616358659)
                ·
                  refine ⟨30101008241465759424537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20067338827643839616358659 30101008241465759424537989)
                  ·
                    refine ⟨5643939045274829892100873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30101008241465759424537989 5643939045274829892100873)
                    ·
                      refine ⟨4232954283956122419075655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643939045274829892100873 4232954283956122419075655)
                      ·
                        rfl

theorem cell23_8243649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8243649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243649 prefixEnd_8243649 := by exact prefixLift 8243649
  have htrace : WordTrace (prefixWord ++ tailWord_8243649) baseStart_8243649 baseEnd_8243649 := by
    simpa [prefixWord, tailWord_8243649, baseEnd_8243649] using wordTrace_append hprefix tailTrace_8243649
  have hstable : (prefixWord ++ tailWord_8243649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243649).length < 2 ^ (prefixWord ++ tailWord_8243649).sum := by decide
  have hdescent : baseEnd_8243649 < baseStart_8243649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243668 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_8243668 : Nat := 118140960795 + 8243668 * 2 ^ 59
def prefixEnd_8243668 : Nat := 4983230072969 + 3 ^ 40 * 8243668 * 2
def baseEnd_8243668 : Nat := 1410988013362852614912689

theorem tailTrace_8243668 : CollatzResearch.WordTrace tailWord_8243668 prefixEnd_8243668 1410988013362852614912689 := by
  unfold tailWord_8243668
  simp only [CollatzResearch.WordTrace]
  refine ⟨150335636549303108625177829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200447515399070811500237105 150335636549303108625177829)
  ·
    refine ⟨28187931852994332867220843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150335636549303108625177829 28187931852994332867220843)
    ·
      refine ⟨42281897779491499300831265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28187931852994332867220843 42281897779491499300831265)
      ·
        refine ⟨31711423334618624475623449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42281897779491499300831265 31711423334618624475623449)
        ·
          refine ⟨23783567500963968356717587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31711423334618624475623449 23783567500963968356717587)
          ·
            refine ⟨35675351251445952535076381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23783567500963968356717587 35675351251445952535076381)
            ·
              refine ⟨13378256719292232200653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35675351251445952535076381 13378256719292232200653643)
              ·
                refine ⟨20067385078938348300980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378256719292232200653643 20067385078938348300980465)
                ·
                  refine ⟨15050538809203761225735349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20067385078938348300980465 15050538809203761225735349)
                  ·
                    refine ⟨1410988013362852614912689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15050538809203761225735349 1410988013362852614912689)
                    ·
                      rfl

theorem cell23_8243668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_8243668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243668 prefixEnd_8243668 := by exact prefixLift 8243668
  have htrace : WordTrace (prefixWord ++ tailWord_8243668) baseStart_8243668 baseEnd_8243668 := by
    simpa [prefixWord, tailWord_8243668, baseEnd_8243668] using wordTrace_append hprefix tailTrace_8243668
  have hstable : (prefixWord ++ tailWord_8243668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243668).length < 2 ^ (prefixWord ++ tailWord_8243668).sum := by decide
  have hdescent : baseEnd_8243668 < baseStart_8243668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243681 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_8243681 : Nat := 118140960795 + 8243681 * 2 ^ 59
def prefixEnd_8243681 : Nat := 4983230072969 + 3 ^ 40 * 8243681 * 2
def baseEnd_8243681 : Nat := 1410990238445688764625169

theorem tailTrace_8243681 : CollatzResearch.WordTrace tailWord_8243681 prefixEnd_8243681 1410990238445688764625169 := by
  unfold tailWord_8243681
  simp only [CollatzResearch.WordTrace]
  refine ⟨300671747247559120470578897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200447831498372746980385931 300671747247559120470578897)
  ·
    refine ⟨225503810435669340352934173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300671747247559120470578897 225503810435669340352934173)
    ·
      refine ⟨84563928913376002632350315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225503810435669340352934173 84563928913376002632350315)
      ·
        refine ⟨126845893370064003948525473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84563928913376002632350315 126845893370064003948525473)
        ·
          refine ⟨95134420027548002961394105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126845893370064003948525473 95134420027548002961394105)
          ·
            refine ⟨71350815020661002221045579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95134420027548002961394105 71350815020661002221045579)
            ·
              refine ⟨107026222530991503331568369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71350815020661002221045579 107026222530991503331568369)
              ·
                refine ⟨80269666898243627498676277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107026222530991503331568369 80269666898243627498676277)
                ·
                  refine ⟨7525281271710340078000901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80269666898243627498676277 7525281271710340078000901)
                  ·
                    refine ⟨1410990238445688764625169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525281271710340078000901 1410990238445688764625169)
                    ·
                      rfl

theorem cell23_8243681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_8243681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243681 prefixEnd_8243681 := by exact prefixLift 8243681
  have htrace : WordTrace (prefixWord ++ tailWord_8243681) baseStart_8243681 baseEnd_8243681 := by
    simpa [prefixWord, tailWord_8243681, baseEnd_8243681] using wordTrace_append hprefix tailTrace_8243681
  have hstable : (prefixWord ++ tailWord_8243681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243681).length < 2 ^ (prefixWord ++ tailWord_8243681).sum := by decide
  have hdescent : baseEnd_8243681 < baseStart_8243681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243688 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_8243688 : Nat := 118140960795 + 8243688 * 2 ^ 59
def prefixEnd_8243688 : Nat := 4983230072969 + 3 ^ 40 * 8243688 * 2
def baseEnd_8243688 : Nat := 4232974309701647766487975

theorem tailTrace_8243688 : CollatzResearch.WordTrace tailWord_8243688 prefixEnd_8243688 4232974309701647766487975 := by
  unfold tailWord_8243688
  simp only [CollatzResearch.WordTrace]
  refine ⟨150336001279266880333041859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200448001705689173777389145 150336001279266880333041859)
  ·
    refine ⟨225504001918900320499562789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150336001279266880333041859 225504001918900320499562789)
    ·
      refine ⟨42282000359793810093668023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225504001918900320499562789 42282000359793810093668023)
      ·
        refine ⟨63423000539690715140502035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42282000359793810093668023 63423000539690715140502035)
        ·
          refine ⟨95134500809536072710753053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63423000539690715140502035 95134500809536072710753053)
          ·
            refine ⟨35675437803576027266532395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95134500809536072710753053 35675437803576027266532395)
            ·
              refine ⟨53513156705364040899798593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35675437803576027266532395 53513156705364040899798593)
              ·
                refine ⟨40134867529023030674848945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53513156705364040899798593 40134867529023030674848945)
                ·
                  refine ⟨30101150646767273006136709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40134867529023030674848945 30101150646767273006136709)
                  ·
                    refine ⟨5643965746268863688650633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30101150646767273006136709 5643965746268863688650633)
                    ·
                      refine ⟨4232974309701647766487975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5643965746268863688650633 4232974309701647766487975)
                      ·
                        rfl

theorem cell23_8243688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_8243688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243688 prefixEnd_8243688 := by exact prefixLift 8243688
  have htrace : WordTrace (prefixWord ++ tailWord_8243688) baseStart_8243688 baseEnd_8243688 := by
    simpa [prefixWord, tailWord_8243688, baseEnd_8243688] using wordTrace_append hprefix tailTrace_8243688
  have hstable : (prefixWord ++ tailWord_8243688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243688).length < 2 ^ (prefixWord ++ tailWord_8243688).sum := by decide
  have hdescent : baseEnd_8243688 < baseStart_8243688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243691 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3]
def baseStart_8243691 : Nat := 118140960795 + 8243691 * 2 ^ 59
def prefixEnd_8243691 : Nat := 4983230072969 + 3 ^ 40 * 8243691 * 2
def baseEnd_8243691 : Nat := 4232975850143611254750461

theorem tailTrace_8243691 : CollatzResearch.WordTrace tailWord_8243691 prefixEnd_8243691 4232975850143611254750461 := by
  unfold tailWord_8243691
  simp only [CollatzResearch.WordTrace]
  refine ⟨300672111977522892178442927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200448074651681928118961951 300672111977522892178442927)
  ·
    refine ⟨451008167966284338267664391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300672111977522892178442927 451008167966284338267664391)
    ·
      refine ⟨676512251949426507401496587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451008167966284338267664391 676512251949426507401496587)
      ·
        refine ⟨1014768377924139761102244881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676512251949426507401496587 1014768377924139761102244881)
        ·
          refine ⟨761076283443104820826683661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014768377924139761102244881 761076283443104820826683661)
          ·
            refine ⟨285403606291164307810006373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761076283443104820826683661 285403606291164307810006373)
            ·
              refine ⟨53513176179593307714376195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285403606291164307810006373 53513176179593307714376195)
              ·
                refine ⟨80269764269389961571564293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53513176179593307714376195 80269764269389961571564293)
                ·
                  refine ⟨15050580800510617794668305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80269764269389961571564293 15050580800510617794668305)
                  ·
                    refine ⟨11287935600382963346001229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15050580800510617794668305 11287935600382963346001229)
                    ·
                      refine ⟨4232975850143611254750461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287935600382963346001229 4232975850143611254750461)
                      ·
                        rfl

theorem cell23_8243691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].length) (baseStart_8243691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243691 prefixEnd_8243691 := by exact prefixLift 8243691
  have htrace : WordTrace (prefixWord ++ tailWord_8243691) baseStart_8243691 baseEnd_8243691 := by
    simpa [prefixWord, tailWord_8243691, baseEnd_8243691] using wordTrace_append hprefix tailTrace_8243691
  have hstable : (prefixWord ++ tailWord_8243691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243691).length < 2 ^ (prefixWord ++ tailWord_8243691).sum := by decide
  have hdescent : baseEnd_8243691 < baseStart_8243691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243738 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_8243738 : Nat := 118140960795 + 8243738 * 2 ^ 59
def prefixEnd_8243738 : Nat := 4983230072969 + 3 ^ 40 * 8243738 * 2
def baseEnd_8243738 : Nat := 4232999983734372570862745

theorem tailTrace_8243738 : CollatzResearch.WordTrace tailWord_8243738 prefixEnd_8243738 4232999983734372570862745 := by
  unfold tailWord_8243738
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168456552088154801350967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200449217472235079470269245 75168456552088154801350967)
  ·
    refine ⟨112752684828132232202026451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75168456552088154801350967 112752684828132232202026451)
    ·
      refine ⟨169129027242198348303039677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112752684828132232202026451 169129027242198348303039677)
      ·
        refine ⟨63423385215824380613639879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169129027242198348303039677 63423385215824380613639879)
        ·
          refine ⟨95135077823736570920459819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63423385215824380613639879 95135077823736570920459819)
          ·
            refine ⟨142702616735604856380689729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95135077823736570920459819 142702616735604856380689729)
            ·
              refine ⟨107026962551703642285517297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142702616735604856380689729 107026962551703642285517297)
              ·
                refine ⟨80270221913777731714137973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107026962551703642285517297 80270221913777731714137973)
                ·
                  refine ⟨7525333304416662348200435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80270221913777731714137973 7525333304416662348200435)
                  ·
                    refine ⟨11287999956624993522300653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525333304416662348200435 11287999956624993522300653)
                    ·
                      refine ⟨4232999983734372570862745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11287999956624993522300653 4232999983734372570862745)
                      ·
                        rfl

theorem cell23_8243738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_8243738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243738 prefixEnd_8243738 := by exact prefixLift 8243738
  have htrace : WordTrace (prefixWord ++ tailWord_8243738) baseStart_8243738 baseEnd_8243738 := by
    simpa [prefixWord, tailWord_8243738, baseEnd_8243738] using wordTrace_append hprefix tailTrace_8243738
  have hstable : (prefixWord ++ tailWord_8243738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243738).length < 2 ^ (prefixWord ++ tailWord_8243738).sum := by decide
  have hdescent : baseEnd_8243738 < baseStart_8243738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 1, 1, 3]
def baseStart_8243755 : Nat := 118140960795 + 8243755 * 2 ^ 59
def prefixEnd_8243755 : Nat := 4983230072969 + 3 ^ 40 * 8243755 * 2
def baseEnd_8243755 : Nat := 4233008712905499004350167

theorem tailTrace_8243755 : CollatzResearch.WordTrace tailWord_8243755 prefixEnd_8243755 4233008712905499004350167 := by
  unfold tailWord_8243755
  simp only [CollatzResearch.WordTrace]
  refine ⟨300674446249291031108772719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200449630832860687405848479 300674446249291031108772719)
  ·
    refine ⟨451011669373936546663159079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300674446249291031108772719 451011669373936546663159079)
    ·
      refine ⟨676517504060904819994738619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451011669373936546663159079 676517504060904819994738619)
      ·
        refine ⟨1014776256091357229992107929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676517504060904819994738619 1014776256091357229992107929)
        ·
          refine ⟨761082192068517922494080947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014776256091357229992107929 761082192068517922494080947)
          ·
            refine ⟨1141623288102776883741121421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761082192068517922494080947 1141623288102776883741121421)
            ·
              refine ⟨428108733038541331402920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141623288102776883741121421 428108733038541331402920533)
              ·
                refine ⟨5016899215295406227377975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 428108733038541331402920533 5016899215295406227377975)
                ·
                  refine ⟨7525348822943109341066963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016899215295406227377975 7525348822943109341066963)
                  ·
                    refine ⟨11288023234414664011600445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525348822943109341066963 11288023234414664011600445)
                    ·
                      refine ⟨4233008712905499004350167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11288023234414664011600445 4233008712905499004350167)
                      ·
                        rfl

theorem cell23_8243755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 1, 3].length) (baseStart_8243755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243755 prefixEnd_8243755 := by exact prefixLift 8243755
  have htrace : WordTrace (prefixWord ++ tailWord_8243755) baseStart_8243755 baseEnd_8243755 := by
    simpa [prefixWord, tailWord_8243755, baseEnd_8243755] using wordTrace_append hprefix tailTrace_8243755
  have hstable : (prefixWord ++ tailWord_8243755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243755).length < 2 ^ (prefixWord ++ tailWord_8243755).sum := by decide
  have hdescent : baseEnd_8243755 < baseStart_8243755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243791 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_8243791 : Nat := 118140960795 + 8243791 * 2 ^ 59
def prefixEnd_8243791 : Nat := 4983230072969 + 3 ^ 40 * 8243791 * 2
def baseEnd_8243791 : Nat := 4233027198209060863500001

theorem tailTrace_8243791 : CollatzResearch.WordTrace tailWord_8243791 prefixEnd_8243791 4233027198209060863500001 := by
  unfold tailWord_8243791
  simp only [CollatzResearch.WordTrace]
  refine ⟨300675759277160609257083227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200450506184773739504722151 300675759277160609257083227)
  ·
    refine ⟨451013638915740913885624841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300675759277160609257083227 451013638915740913885624841)
    ·
      refine ⟨338260229186805685414218631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451013638915740913885624841 338260229186805685414218631)
      ·
        refine ⟨507390343780208528121327947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338260229186805685414218631 507390343780208528121327947)
        ·
          refine ⟨761085515670312792181991921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507390343780208528121327947 761085515670312792181991921)
          ·
            refine ⟨570814136752734594136493941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761085515670312792181991921 570814136752734594136493941)
            ·
              refine ⟨53513825320568868200296307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 570814136752734594136493941 53513825320568868200296307)
              ·
                refine ⟨80270737980853302300444461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53513825320568868200296307 80270737980853302300444461)
                ·
                  refine ⟨30101526742819988362666673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80270737980853302300444461 30101526742819988362666673)
                  ·
                    refine ⟨22576145057114991272000005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30101526742819988362666673 22576145057114991272000005)
                    ·
                      refine ⟨4233027198209060863500001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22576145057114991272000005 4233027198209060863500001)
                      ·
                        rfl

theorem cell23_8243791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_8243791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243791 prefixEnd_8243791 := by exact prefixLift 8243791
  have htrace : WordTrace (prefixWord ++ tailWord_8243791) baseStart_8243791 baseEnd_8243791 := by
    simpa [prefixWord, tailWord_8243791, baseEnd_8243791] using wordTrace_append hprefix tailTrace_8243791
  have hstable : (prefixWord ++ tailWord_8243791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243791).length < 2 ^ (prefixWord ++ tailWord_8243791).sum := by decide
  have hdescent : baseEnd_8243791 < baseStart_8243791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243829 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8243829 : Nat := 118140960795 + 8243829 * 2 ^ 59
def prefixEnd_8243829 : Nat := 4983230072969 + 3 ^ 40 * 8243829 * 2
def baseEnd_8243829 : Nat := 4233046710473931714824827

theorem tailTrace_8243829 : CollatzResearch.WordTrace tailWord_8243829 prefixEnd_8243829 4233046710473931714824827 := by
  unfold tailWord_8243829
  simp only [CollatzResearch.WordTrace]
  refine ⟨300677145251022941746966541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200451430167348627831311027 300677145251022941746966541)
  ·
    refine ⟨112753929469133603155112453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300677145251022941746966541 112753929469133603155112453)
    ·
      refine ⟨21141361775462550591583585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112753929469133603155112453 21141361775462550591583585)
      ·
        refine ⟨15856021331596912943687689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21141361775462550591583585 15856021331596912943687689)
        ·
          refine ⟨11892015998697684707765767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15856021331596912943687689 11892015998697684707765767)
          ·
            refine ⟨17838023998046527061648651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11892015998697684707765767 17838023998046527061648651)
            ·
              refine ⟨26757035997069790592472977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17838023998046527061648651 26757035997069790592472977)
              ·
                refine ⟨20067776997802342944354733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26757035997069790592472977 20067776997802342944354733)
                ·
                  refine ⟨7525416374175878604133025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20067776997802342944354733 7525416374175878604133025)
                  ·
                    refine ⟨5644062280631908953099769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7525416374175878604133025 5644062280631908953099769)
                    ·
                      refine ⟨4233046710473931714824827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644062280631908953099769 4233046710473931714824827)
                      ·
                        rfl

theorem cell23_8243829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8243829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243829 prefixEnd_8243829 := by exact prefixLift 8243829
  have htrace : WordTrace (prefixWord ++ tailWord_8243829) baseStart_8243829 baseEnd_8243829 := by
    simpa [prefixWord, tailWord_8243829, baseEnd_8243829] using wordTrace_append hprefix tailTrace_8243829
  have hstable : (prefixWord ++ tailWord_8243829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243829).length < 2 ^ (prefixWord ++ tailWord_8243829).sum := by decide
  have hdescent : baseEnd_8243829 < baseStart_8243829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243851 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_8243851 : Nat := 118140960795 + 8243851 * 2 ^ 59
def prefixEnd_8243851 : Nat := 4983230072969 + 3 ^ 40 * 8243851 * 2
def baseEnd_8243851 : Nat := 4233058007048330628749725

theorem tailTrace_8243851 : CollatzResearch.WordTrace tailWord_8243851 prefixEnd_8243851 4233058007048330628749725 := by
  unfold tailWord_8243851
  simp only [CollatzResearch.WordTrace]
  refine ⟨300677947656943239504267407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200451965104628826336178271 300677947656943239504267407)
  ·
    refine ⟨451016921485414859256401111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300677947656943239504267407 451016921485414859256401111)
    ·
      refine ⟨676525382228122288884601667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451016921485414859256401111 676525382228122288884601667)
      ·
        refine ⟨1014788073342183433326902501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676525382228122288884601667 1014788073342183433326902501)
        ·
          refine ⟨190272763751659393748794219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1014788073342183433326902501 190272763751659393748794219)
          ·
            refine ⟨285409145627489090623191329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190272763751659393748794219 285409145627489090623191329)
            ·
              refine ⟨214056859220616817967393497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285409145627489090623191329 214056859220616817967393497)
              ·
                refine ⟨160542644415462613475545123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214056859220616817967393497 160542644415462613475545123)
                ·
                  refine ⟨240813966623193920213317685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160542644415462613475545123 240813966623193920213317685)
                  ·
                    refine ⟨22576309370924430019998533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240813966623193920213317685 22576309370924430019998533)
                    ·
                      refine ⟨4233058007048330628749725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22576309370924430019998533 4233058007048330628749725)
                      ·
                        rfl

theorem cell23_8243851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_8243851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243851 prefixEnd_8243851 := by exact prefixLift 8243851
  have htrace : WordTrace (prefixWord ++ tailWord_8243851) baseStart_8243851 baseEnd_8243851 := by
    simpa [prefixWord, tailWord_8243851, baseEnd_8243851] using wordTrace_append hprefix tailTrace_8243851
  have hstable : (prefixWord ++ tailWord_8243851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243851).length < 2 ^ (prefixWord ++ tailWord_8243851).sum := by decide
  have hdescent : baseEnd_8243851 < baseStart_8243851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243855 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 1, 3, 2]
def baseStart_8243855 : Nat := 118140960795 + 8243855 * 2 ^ 59
def prefixEnd_8243855 : Nat := 4983230072969 + 3 ^ 40 * 8243855 * 2
def baseEnd_8243855 : Nat := 4233060060970948613099707

theorem tailTrace_8243855 : CollatzResearch.WordTrace tailWord_8243855 prefixEnd_8243855 4233060060970948613099707 := by
  unfold tailWord_8243855
  simp only [CollatzResearch.WordTrace]
  refine ⟨300678093548928748187413019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200452062365952498791608679 300678093548928748187413019)
  ·
    refine ⟨451017140323393122281119529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300678093548928748187413019 451017140323393122281119529)
    ·
      refine ⟨338262855242544841710839647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451017140323393122281119529 338262855242544841710839647)
      ·
        refine ⟨507394282863817262566259471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338262855242544841710839647 507394282863817262566259471)
        ·
          refine ⟨761091424295725893849389207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507394282863817262566259471 761091424295725893849389207)
          ·
            refine ⟨1141637136443588840774083811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761091424295725893849389207 1141637136443588840774083811)
            ·
              refine ⟨1712455704665383261161125717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141637136443588840774083811 1712455704665383261161125717)
              ·
                refine ⟨10033920144523730045865971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1712455704665383261161125717 10033920144523730045865971)
                ·
                  refine ⟨15050880216785595068798957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10033920144523730045865971 15050880216785595068798957)
                  ·
                    refine ⟨5644080081294598150799609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15050880216785595068798957 5644080081294598150799609)
                    ·
                      refine ⟨4233060060970948613099707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644080081294598150799609 4233060060970948613099707)
                      ·
                        rfl

theorem cell23_8243855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3, 2].length) (baseStart_8243855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243855 prefixEnd_8243855 := by exact prefixLift 8243855
  have htrace : WordTrace (prefixWord ++ tailWord_8243855) baseStart_8243855 baseEnd_8243855 := by
    simpa [prefixWord, tailWord_8243855, baseEnd_8243855] using wordTrace_append hprefix tailTrace_8243855
  have hstable : (prefixWord ++ tailWord_8243855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243855).length < 2 ^ (prefixWord ++ tailWord_8243855).sum := by decide
  have hdescent : baseEnd_8243855 < baseStart_8243855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243879 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_8243879 : Nat := 118140960795 + 8243879 * 2 ^ 59
def prefixEnd_8243879 : Nat := 4983230072969 + 3 ^ 40 * 8243879 * 2
def baseEnd_8243879 : Nat := 4233072384506656519199597

theorem tailTrace_8243879 : CollatzResearch.WordTrace tailWord_8243879 prefixEnd_8243879 4233072384506656519199597 := by
  unfold tailWord_8243879
  simp only [CollatzResearch.WordTrace]
  refine ⟨300678968900841800286286691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200452645933894533524191127 300678968900841800286286691)
  ·
    refine ⟨451018453351262700429430037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300678968900841800286286691 451018453351262700429430037)
    ·
      refine ⟨21141490000840439082629533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 451018453351262700429430037 21141490000840439082629533)
      ·
        refine ⟨7928058750315164655986075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21141490000840439082629533 7928058750315164655986075)
        ·
          refine ⟨11892088125472746983979113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928058750315164655986075 11892088125472746983979113)
          ·
            refine ⟨8919066094104560237984335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11892088125472746983979113 8919066094104560237984335)
            ·
              refine ⟨13378599141156840356976503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919066094104560237984335 13378599141156840356976503)
              ·
                refine ⟨20067898711735260535464755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378599141156840356976503 20067898711735260535464755)
                ·
                  refine ⟨30101848067602890803197133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20067898711735260535464755 30101848067602890803197133)
                  ·
                    refine ⟨11288193025351084051198925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30101848067602890803197133 11288193025351084051198925)
                    ·
                      refine ⟨4233072384506656519199597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11288193025351084051198925 4233072384506656519199597)
                      ·
                        rfl

theorem cell23_8243879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_8243879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243879 prefixEnd_8243879 := by exact prefixLift 8243879
  have htrace : WordTrace (prefixWord ++ tailWord_8243879) baseStart_8243879 baseEnd_8243879 := by
    simpa [prefixWord, tailWord_8243879, baseEnd_8243879] using wordTrace_append hprefix tailTrace_8243879
  have hstable : (prefixWord ++ tailWord_8243879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243879).length < 2 ^ (prefixWord ++ tailWord_8243879).sum := by decide
  have hdescent : baseEnd_8243879 < baseStart_8243879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243902 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_8243902 : Nat := 118140960795 + 8243902 * 2 ^ 59
def prefixEnd_8243902 : Nat := 4983230072969 + 3 ^ 40 * 8243902 * 2
def baseEnd_8243902 : Nat := 4233084194561709929211991

theorem tailTrace_8243902 : CollatzResearch.WordTrace tailWord_8243902 prefixEnd_8243902 4233084194561709929211991 := by
  unfold tailWord_8243902
  simp only [CollatzResearch.WordTrace]
  refine ⟨37584975972469809401796745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200453205186505650142915973 37584975972469809401796745)
  ·
    refine ⟨28188731979352357051347559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37584975972469809401796745 28188731979352357051347559)
    ·
      refine ⟨42283097969028535577021339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28188731979352357051347559 42283097969028535577021339)
      ·
        refine ⟨63424646953542803365532009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42283097969028535577021339 63424646953542803365532009)
        ·
          refine ⟨47568485215157102524149007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63424646953542803365532009 47568485215157102524149007)
          ·
            refine ⟨71352727822735653786223511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47568485215157102524149007 71352727822735653786223511)
            ·
              refine ⟨107029091734103480679335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71352727822735653786223511 107029091734103480679335267)
              ·
                refine ⟨160543637601155221019002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107029091734103480679335267 160543637601155221019002901)
                ·
                  refine ⟨7525483012554150985265761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160543637601155221019002901 7525483012554150985265761)
                  ·
                    refine ⟨5644112259415613238949321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7525483012554150985265761 5644112259415613238949321)
                    ·
                      refine ⟨4233084194561709929211991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644112259415613238949321 4233084194561709929211991)
                      ·
                        rfl

theorem cell23_8243902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_8243902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243902 prefixEnd_8243902 := by exact prefixLift 8243902
  have htrace : WordTrace (prefixWord ++ tailWord_8243902) baseStart_8243902 baseEnd_8243902 := by
    simpa [prefixWord, tailWord_8243902, baseEnd_8243902] using wordTrace_append hprefix tailTrace_8243902
  have hstable : (prefixWord ++ tailWord_8243902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243902).length < 2 ^ (prefixWord ++ tailWord_8243902).sum := by decide
  have hdescent : baseEnd_8243902 < baseStart_8243902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243978 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_8243978 : Nat := 118140960795 + 8243978 * 2 ^ 59
def prefixEnd_8243978 : Nat := 4983230072969 + 3 ^ 40 * 8243978 * 2
def baseEnd_8243978 : Nat := 4233123219091451631861641

theorem tailTrace_8243978 : CollatzResearch.WordTrace tailWord_8243978 prefixEnd_8243978 4233123219091451631861641 := by
  unfold tailWord_8243978
  simp only [CollatzResearch.WordTrace]
  refine ⟨75170644931870785048535147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200455053151655426796093725 75170644931870785048535147)
  ·
    refine ⟨112755967397806177572802721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75170644931870785048535147 112755967397806177572802721)
    ·
      refine ⟨84566975548354633179602041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112755967397806177572802721 84566975548354633179602041)
      ·
        refine ⟨63425231661265974884701531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84566975548354633179602041 63425231661265974884701531)
        ·
          refine ⟨95137847491898962327052297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63425231661265974884701531 95137847491898962327052297)
          ·
            refine ⟨71353385618924221745289223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95137847491898962327052297 71353385618924221745289223)
            ·
              refine ⟨107030078428386332617933835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71353385618924221745289223 107030078428386332617933835)
              ·
                refine ⟨160545117642579498926900753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107030078428386332617933835 160545117642579498926900753)
                ·
                  refine ⟨120408838231934624195175565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160545117642579498926900753 120408838231934624195175565)
                  ·
                    refine ⟨45153314336975484073190837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120408838231934624195175565 45153314336975484073190837)
                    ·
                      refine ⟨4233123219091451631861641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45153314336975484073190837 4233123219091451631861641)
                      ·
                        rfl

theorem cell23_8243978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_8243978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243978 prefixEnd_8243978 := by exact prefixLift 8243978
  have htrace : WordTrace (prefixWord ++ tailWord_8243978) baseStart_8243978 baseEnd_8243978 := by
    simpa [prefixWord, tailWord_8243978, baseEnd_8243978] using wordTrace_append hprefix tailTrace_8243978
  have hstable : (prefixWord ++ tailWord_8243978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243978).length < 2 ^ (prefixWord ++ tailWord_8243978).sum := by decide
  have hdescent : baseEnd_8243978 < baseStart_8243978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244002 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_8244002 : Nat := 118140960795 + 8244002 * 2 ^ 59
def prefixEnd_8244002 : Nat := 4983230072969 + 3 ^ 40 * 8244002 * 2
def baseEnd_8244002 : Nat := 1411045180875719845987177

theorem tailTrace_8244002 : CollatzResearch.WordTrace tailWord_8244002 prefixEnd_8244002 1411045180875719845987177 := by
  unfold tailWord_8244002
  simp only [CollatzResearch.WordTrace]
  refine ⟨75170863769849048073253565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200455636719597461528676173 75170863769849048073253565)
  ·
    refine ⟨28189073913693393027470087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75170863769849048073253565 28189073913693393027470087)
    ·
      refine ⟨42283610870540089541205131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28189073913693393027470087 42283610870540089541205131)
      ·
        refine ⟨63425416305810134311807697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42283610870540089541205131 63425416305810134311807697)
        ·
          refine ⟨47569062229357600733855773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63425416305810134311807697 47569062229357600733855773)
          ·
            refine ⟨17838398336009100275195915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47569062229357600733855773 17838398336009100275195915)
            ·
              refine ⟨26757597504013650412793873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17838398336009100275195915 26757597504013650412793873)
              ·
                refine ⟨20068198128010237809595405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26757597504013650412793873 20068198128010237809595405)
                ·
                  refine ⟨7525574298003839178598277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20068198128010237809595405 7525574298003839178598277)
                  ·
                    refine ⟨1411045180875719845987177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525574298003839178598277 1411045180875719845987177)
                    ·
                      rfl

theorem cell23_8244002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_8244002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244002 prefixEnd_8244002 := by exact prefixLift 8244002
  have htrace : WordTrace (prefixWord ++ tailWord_8244002) baseStart_8244002 baseEnd_8244002 := by
    simpa [prefixWord, tailWord_8244002, baseEnd_8244002] using wordTrace_append hprefix tailTrace_8244002
  have hstable : (prefixWord ++ tailWord_8244002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244002).length < 2 ^ (prefixWord ++ tailWord_8244002).sum := by decide
  have hdescent : baseEnd_8244002 < baseStart_8244002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244019 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 1, 4]
def baseStart_8244019 : Nat := 118140960795 + 8244019 * 2 ^ 59
def prefixEnd_8244019 : Nat := 4983230072969 + 3 ^ 40 * 8244019 * 2
def baseEnd_8244019 : Nat := 1411048090599428657149651

theorem tailTrace_8244019 : CollatzResearch.WordTrace tailWord_8244019 prefixEnd_8244019 1411048090599428657149651 := by
  unfold tailWord_8244019
  simp only [CollatzResearch.WordTrace]
  refine ⟨300684075120334604196383111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200456050080223069464255407 300684075120334604196383111)
  ·
    refine ⟨451026112680501906294574667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300684075120334604196383111 451026112680501906294574667)
    ·
      refine ⟨676539169020752859441862001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451026112680501906294574667 676539169020752859441862001)
      ·
        refine ⟨507404376765564644581396501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676539169020752859441862001 507404376765564644581396501)
        ·
          refine ⟨23784580160885842714752961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 507404376765564644581396501 23784580160885842714752961)
          ·
            refine ⟨17838435120664382036064721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23784580160885842714752961 17838435120664382036064721)
            ·
              refine ⟨13378826340498286527048541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17838435120664382036064721 13378826340498286527048541)
              ·
                refine ⟨5017059877686857447643203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13378826340498286527048541 5017059877686857447643203)
                ·
                  refine ⟨7525589816530286171464805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017059877686857447643203 7525589816530286171464805)
                  ·
                    refine ⟨1411048090599428657149651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525589816530286171464805 1411048090599428657149651)
                    ·
                      rfl

theorem cell23_8244019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 4].length) (baseStart_8244019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244019 prefixEnd_8244019 := by exact prefixLift 8244019
  have htrace : WordTrace (prefixWord ++ tailWord_8244019) baseStart_8244019 baseEnd_8244019 := by
    simpa [prefixWord, tailWord_8244019, baseEnd_8244019] using wordTrace_append hprefix tailTrace_8244019
  have hstable : (prefixWord ++ tailWord_8244019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244019).length < 2 ^ (prefixWord ++ tailWord_8244019).sum := by decide
  have hdescent : baseEnd_8244019 < baseStart_8244019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244036 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_8244036 : Nat := 118140960795 + 8244036 * 2 ^ 59
def prefixEnd_8244036 : Nat := 4983230072969 + 3 ^ 40 * 8244036 * 2
def baseEnd_8244036 : Nat := 1411051000323137468312125

theorem tailTrace_8244036 : CollatzResearch.WordTrace tailWord_8244036 prefixEnd_8244036 1411051000323137468312125 := by
  unfold tailWord_8244036
  simp only [CollatzResearch.WordTrace]
  refine ⟨150342347580636508049875981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200456463440848677399834641 150342347580636508049875981)
  ·
    refine ⟨56378380342738690518703493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150342347580636508049875981 56378380342738690518703493)
    ·
      refine ⟨10570946314263504472256905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56378380342738690518703493 10570946314263504472256905)
      ·
        refine ⟨7928209735697628354192679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10570946314263504472256905 7928209735697628354192679)
        ·
          refine ⟨11892314603546442531289019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928209735697628354192679 11892314603546442531289019)
          ·
            refine ⟨17838471905319663796933529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11892314603546442531289019 17838471905319663796933529)
            ·
              refine ⟨13378853928989747847700147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17838471905319663796933529 13378853928989747847700147)
              ·
                refine ⟨20068280893484621771550221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13378853928989747847700147 20068280893484621771550221)
                ·
                  refine ⟨7525605335056733164331333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20068280893484621771550221 7525605335056733164331333)
                  ·
                    refine ⟨1411051000323137468312125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525605335056733164331333 1411051000323137468312125)
                    ·
                      rfl

theorem cell23_8244036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_8244036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244036 prefixEnd_8244036 := by exact prefixLift 8244036
  have htrace : WordTrace (prefixWord ++ tailWord_8244036) baseStart_8244036 baseEnd_8244036 := by
    simpa [prefixWord, tailWord_8244036, baseEnd_8244036] using wordTrace_append hprefix tailTrace_8244036
  have hstable : (prefixWord ++ tailWord_8244036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244036).length < 2 ^ (prefixWord ++ tailWord_8244036).sum := by decide
  have hdescent : baseEnd_8244036 < baseStart_8244036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244075 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 4, 4]
def baseStart_8244075 : Nat := 118140960795 + 8244075 * 2 ^ 59
def prefixEnd_8244075 : Nat := 4983230072969 + 3 ^ 40 * 8244075 * 2
def baseEnd_8244075 : Nat := 1411057675571645917449565

theorem tailTrace_8244075 : CollatzResearch.WordTrace tailWord_8244075 prefixEnd_8244075 1411057675571645917449565 := by
  unfold tailWord_8244075
  simp only [CollatzResearch.WordTrace]
  refine ⟨300686117608131725760421679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200457411738754483840281119 300686117608131725760421679)
  ·
    refine ⟨451029176412197588640632519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300686117608131725760421679 451029176412197588640632519)
    ·
      refine ⟨676543764618296382960948779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451029176412197588640632519 676543764618296382960948779)
      ·
        refine ⟨1014815646927444574441423169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676543764618296382960948779 1014815646927444574441423169)
        ·
          refine ⟨761111735195583430831067377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014815646927444574441423169 761111735195583430831067377)
          ·
            refine ⟨570833801396687573123300533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761111735195583430831067377 570833801396687573123300533)
            ·
              refine ⟨53515668880939459980309425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 570833801396687573123300533 53515668880939459980309425)
              ·
                refine ⟨40136751660704594985232069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53515668880939459980309425 40136751660704594985232069)
                ·
                  refine ⟨7525640936382111559731013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40136751660704594985232069 7525640936382111559731013)
                  ·
                    refine ⟨1411057675571645917449565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7525640936382111559731013 1411057675571645917449565)
                    ·
                      rfl

theorem cell23_8244075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 4].length) (baseStart_8244075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244075 prefixEnd_8244075 := by exact prefixLift 8244075
  have htrace : WordTrace (prefixWord ++ tailWord_8244075) baseStart_8244075 baseEnd_8244075 := by
    simpa [prefixWord, tailWord_8244075, baseEnd_8244075] using wordTrace_append hprefix tailTrace_8244075
  have hstable : (prefixWord ++ tailWord_8244075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244075).length < 2 ^ (prefixWord ++ tailWord_8244075).sum := by decide
  have hdescent : baseEnd_8244075 < baseStart_8244075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244082 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_8244082 : Nat := 118140960795 + 8244082 * 2 ^ 59
def prefixEnd_8244082 : Nat := 4983230072969 + 3 ^ 40 * 8244082 * 2
def baseEnd_8244082 : Nat := 4233176621079519224961163

theorem tailTrace_8244082 : CollatzResearch.WordTrace tailWord_8244082 prefixEnd_8244082 4233176621079519224961163 := by
  unfold tailWord_8244082
  simp only [CollatzResearch.WordTrace]
  refine ⟨75171593229776591488981625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200457581946070910637284333 75171593229776591488981625)
  ·
    refine ⟨56378694922332443616736219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75171593229776591488981625 56378694922332443616736219)
    ·
      refine ⟨84568042383498665425104329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56378694922332443616736219 84568042383498665425104329)
      ·
        refine ⟨63426031787623999068828247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84568042383498665425104329 63426031787623999068828247)
        ·
          refine ⟨95139047681435998603242371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63426031787623999068828247 95139047681435998603242371)
          ·
            refine ⟨142708571522153997904863557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95139047681435998603242371 142708571522153997904863557)
            ·
              refine ⟨26757857160403874607161917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142708571522153997904863557 26757857160403874607161917)
              ·
                refine ⟨10034196435151452977685719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26757857160403874607161917 10034196435151452977685719)
                ·
                  refine ⟨15051294652727179466528579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10034196435151452977685719 15051294652727179466528579)
                  ·
                    refine ⟨22576941979090769199792869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15051294652727179466528579 22576941979090769199792869)
                    ·
                      refine ⟨4233176621079519224961163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22576941979090769199792869 4233176621079519224961163)
                      ·
                        rfl

theorem cell23_8244082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_8244082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244082 prefixEnd_8244082 := by exact prefixLift 8244082
  have htrace : WordTrace (prefixWord ++ tailWord_8244082) baseStart_8244082 baseEnd_8244082 := by
    simpa [prefixWord, tailWord_8244082, baseEnd_8244082] using wordTrace_append hprefix tailTrace_8244082
  have hstable : (prefixWord ++ tailWord_8244082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244082).length < 2 ^ (prefixWord ++ tailWord_8244082).sum := by decide
  have hdescent : baseEnd_8244082 < baseStart_8244082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244086 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_8244086 : Nat := 118140960795 + 8244086 * 2 ^ 59
def prefixEnd_8244086 : Nat := 4983230072969 + 3 ^ 40 * 8244086 * 2
def baseEnd_8244086 : Nat := 4233178675002137209311145

theorem tailTrace_8244086 : CollatzResearch.WordTrace tailWord_8244086 prefixEnd_8244086 4233178675002137209311145 := by
  unfold tailWord_8244086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792907425693242164942007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200457679207394583092714741 18792907425693242164942007)
  ·
    refine ⟨28189361138539863247413011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18792907425693242164942007 28189361138539863247413011)
    ·
      refine ⟨42284041707809794871119517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28189361138539863247413011 42284041707809794871119517)
      ·
        refine ⟨15856515640428673076669819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42284041707809794871119517 15856515640428673076669819)
        ·
          refine ⟨23784773460643009615004729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15856515640428673076669819 23784773460643009615004729)
          ·
            refine ⟨17838580095482257211253547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23784773460643009615004729 17838580095482257211253547)
            ·
              refine ⟨26757870143223385816880321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17838580095482257211253547 26757870143223385816880321)
              ·
                refine ⟨20068402607417539362660241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26757870143223385816880321 20068402607417539362660241)
                ·
                  refine ⟨15051301955563154521995181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20068402607417539362660241 15051301955563154521995181)
                  ·
                    refine ⟨5644238233336182945748193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15051301955563154521995181 5644238233336182945748193)
                    ·
                      refine ⟨4233178675002137209311145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644238233336182945748193 4233178675002137209311145)
                      ·
                        rfl

theorem cell23_8244086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_8244086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244086 prefixEnd_8244086 := by exact prefixLift 8244086
  have htrace : WordTrace (prefixWord ++ tailWord_8244086) baseStart_8244086 baseEnd_8244086 := by
    simpa [prefixWord, tailWord_8244086, baseEnd_8244086] using wordTrace_append hprefix tailTrace_8244086
  have hstable : (prefixWord ++ tailWord_8244086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244086).length < 2 ^ (prefixWord ++ tailWord_8244086).sum := by decide
  have hdescent : baseEnd_8244086 < baseStart_8244086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244105 : List Nat := [1, 2, 1, 1, 5, 3, 2, 8]
def baseStart_8244105 : Nat := 118140960795 + 8244105 * 2 ^ 59
def prefixEnd_8244105 : Nat := 4983230072969 + 3 ^ 40 * 8244105 * 2
def baseEnd_8244105 : Nat := 156784756708687875369391

theorem tailTrace_8244105 : CollatzResearch.WordTrace tailWord_8244105 prefixEnd_8244105 156784756708687875369391 := by
  unfold tailWord_8244105
  simp only [CollatzResearch.WordTrace]
  refine ⟨300687211798023040884013769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200458141198682027256009179 300687211798023040884013769)
  ·
    refine ⟨225515408848517280663010327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300687211798023040884013769 225515408848517280663010327)
    ·
      refine ⟨338273113272775920994515491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225515408848517280663010327 338273113272775920994515491)
      ·
        refine ⟨507409669909163881491773237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338273113272775920994515491 507409669909163881491773237)
        ·
          refine ⟨47569656553984113889853741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 507409669909163881491773237 47569656553984113889853741)
          ·
            refine ⟨17838621207744042708695153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47569656553984113889853741 17838621207744042708695153)
            ·
              refine ⟨13378965905808032031521365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17838621207744042708695153 13378965905808032031521365)
              ·
                refine ⟨156784756708687875369391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13378965905808032031521365 156784756708687875369391)
                ·
                  rfl

theorem cell23_8244105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 8].length) (baseStart_8244105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244105 prefixEnd_8244105 := by exact prefixLift 8244105
  have htrace : WordTrace (prefixWord ++ tailWord_8244105) baseStart_8244105 baseEnd_8244105 := by
    simpa [prefixWord, tailWord_8244105, baseEnd_8244105] using wordTrace_append hprefix tailTrace_8244105
  have hstable : (prefixWord ++ tailWord_8244105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244105).length < 2 ^ (prefixWord ++ tailWord_8244105).sum := by decide
  have hdescent : baseEnd_8244105 < baseStart_8244105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244132 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_8244132 : Nat := 118140960795 + 8244132 * 2 ^ 59
def prefixEnd_8244132 : Nat := 4983230072969 + 3 ^ 40 * 8244132 * 2
def baseEnd_8244132 : Nat := 4233202295112244029335933

theorem tailTrace_8244132 : CollatzResearch.WordTrace tailWord_8244132 prefixEnd_8244132 4233202295112244029335933 := by
  unfold tailWord_8244132
  simp only [CollatzResearch.WordTrace]
  refine ⟨150344098284462612247623325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200458797712616816330164433 150344098284462612247623325)
  ·
    refine ⟨56379036856673479592858747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150344098284462612247623325 56379036856673479592858747)
    ·
      refine ⟨84568555285010219389288121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56379036856673479592858747 84568555285010219389288121)
      ·
        refine ⟨63426416463757664541966091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84568555285010219389288121 63426416463757664541966091)
        ·
          refine ⟨95139624695636496812949137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63426416463757664541966091 95139624695636496812949137)
          ·
            refine ⟨71354718521727372609711853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95139624695636496812949137 71354718521727372609711853)
            ·
              refine ⟨26758019445647764728641945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71354718521727372609711853 26758019445647764728641945)
              ·
                refine ⟨20068514584235823546481459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26758019445647764728641945 20068514584235823546481459)
                ·
                  refine ⟨30102771876353735319722189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20068514584235823546481459 30102771876353735319722189)
                  ·
                    refine ⟨11288539453632650744895821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30102771876353735319722189 11288539453632650744895821)
                    ·
                      refine ⟨4233202295112244029335933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11288539453632650744895821 4233202295112244029335933)
                      ·
                        rfl

theorem cell23_8244132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_8244132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244132 prefixEnd_8244132 := by exact prefixLift 8244132
  have htrace : WordTrace (prefixWord ++ tailWord_8244132) baseStart_8244132 baseEnd_8244132 := by
    simpa [prefixWord, tailWord_8244132, baseEnd_8244132] using wordTrace_append hprefix tailTrace_8244132
  have hstable : (prefixWord ++ tailWord_8244132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244132).length < 2 ^ (prefixWord ++ tailWord_8244132).sum := by decide
  have hdescent : baseEnd_8244132 < baseStart_8244132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244173 : List Nat := [1, 6, 3, 1, 1, 1, 3, 7]
def baseStart_8244173 : Nat := 118140960795 + 8244173 * 2 ^ 59
def prefixEnd_8244173 : Nat := 4983230072969 + 3 ^ 40 * 8244173 * 2
def baseEnd_8244173 : Nat := 156786049919225124774935

theorem tailTrace_8244173 : CollatzResearch.WordTrace tailWord_8244173 prefixEnd_8244173 156786049919225124774935 := by
  unfold tailWord_8244173
  simp only [CollatzResearch.WordTrace]
  refine ⟨300689691961776688497489173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200459794641184458998326115 300689691961776688497489173)
  ·
    refine ⟨14094829310708282273319805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300689691961776688497489173 14094829310708282273319805)
    ·
      refine ⟨5285560991515605852494927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14094829310708282273319805 5285560991515605852494927)
      ·
        refine ⟨7928341487273408778742391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285560991515605852494927 7928341487273408778742391)
        ·
          refine ⟨11892512230910113168113587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928341487273408778742391 11892512230910113168113587)
          ·
            refine ⟨17838768346365169752170381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11892512230910113168113587 17838768346365169752170381)
            ·
              refine ⟨6689538129886938657063893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17838768346365169752170381 6689538129886938657063893)
              ·
                refine ⟨156786049919225124774935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6689538129886938657063893 156786049919225124774935)
                ·
                  rfl

theorem cell23_8244173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 7].length) (baseStart_8244173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244173 prefixEnd_8244173 := by exact prefixLift 8244173
  have htrace : WordTrace (prefixWord ++ tailWord_8244173) baseStart_8244173 baseEnd_8244173 := by
    simpa [prefixWord, tailWord_8244173, baseEnd_8244173] using wordTrace_append hprefix tailTrace_8244173
  have hstable : (prefixWord ++ tailWord_8244173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244173).length < 2 ^ (prefixWord ++ tailWord_8244173).sum := by decide
  have hdescent : baseEnd_8244173 < baseStart_8244173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244195 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 9]
def baseStart_8244195 : Nat := 118140960795 + 8244195 * 2 ^ 59
def prefixEnd_8244195 : Nat := 4983230072969 + 3 ^ 40 * 8244195 * 2
def baseEnd_8244195 : Nat := 470359404932608586983127

theorem tailTrace_8244195 : CollatzResearch.WordTrace tailWord_8244195 prefixEnd_8244195 470359404932608586983127 := by
  unfold tailWord_8244195
  simp only [CollatzResearch.WordTrace]
  refine ⟨300690494367696986254790039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200460329578464657503193359 300690494367696986254790039)
  ·
    refine ⟨451035741551545479382185059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300690494367696986254790039 451035741551545479382185059)
    ·
      refine ⟨676553612327318219073277589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451035741551545479382185059 676553612327318219073277589)
      ·
        refine ⟨31713450577843041519059887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 676553612327318219073277589 31713450577843041519059887)
        ·
          refine ⟨47570175866764562278589831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31713450577843041519059887 47570175866764562278589831)
          ·
            refine ⟨71355263800146843417884747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47570175866764562278589831 71355263800146843417884747)
            ·
              refine ⟨107032895700220265126827121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71355263800146843417884747 107032895700220265126827121)
              ·
                refine ⟨80274671775165198845120341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107032895700220265126827121 80274671775165198845120341)
                ·
                  refine ⟨470359404932608586983127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80274671775165198845120341 470359404932608586983127)
                  ·
                    rfl

theorem cell23_8244195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 9].length) (baseStart_8244195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244195 prefixEnd_8244195 := by exact prefixLift 8244195
  have htrace : WordTrace (prefixWord ++ tailWord_8244195) baseStart_8244195 baseEnd_8244195 := by
    simpa [prefixWord, tailWord_8244195, baseEnd_8244195] using wordTrace_append hprefix tailTrace_8244195
  have hstable : (prefixWord ++ tailWord_8244195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244195).length < 2 ^ (prefixWord ++ tailWord_8244195).sum := by decide
  have hdescent : baseEnd_8244195 < baseStart_8244195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244202 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_8244202 : Nat := 118140960795 + 8244202 * 2 ^ 59
def prefixEnd_8244202 : Nat := 4983230072969 + 3 ^ 40 * 8244202 * 2
def baseEnd_8244202 : Nat := 4233238238758058755460611

theorem tailTrace_8244202 : CollatzResearch.WordTrace tailWord_8244202 prefixEnd_8244202 4233238238758058755460611 := by
  unfold tailWord_8244202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75172687419667906612573715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200460499785781084300196573 75172687419667906612573715)
  ·
    refine ⟨112759031129501859918860573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75172687419667906612573715 112759031129501859918860573)
    ·
      refine ⟨42284636673563197469572715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112759031129501859918860573 42284636673563197469572715)
      ·
        refine ⟨63426955010344796204359073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42284636673563197469572715 63426955010344796204359073)
        ·
          refine ⟨47570216257758597153269305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63426955010344796204359073 47570216257758597153269305)
          ·
            refine ⟨35677662193318947864951979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47570216257758597153269305 35677662193318947864951979)
            ·
              refine ⟨53516493289978421797427969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35677662193318947864951979 53516493289978421797427969)
              ·
                refine ⟨40137369967483816348070977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53516493289978421797427969 40137369967483816348070977)
                ·
                  refine ⟨30103027475612862261053233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40137369967483816348070977 30103027475612862261053233)
                  ·
                    refine ⟨22577270606709646695789925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30103027475612862261053233 22577270606709646695789925)
                    ·
                      refine ⟨4233238238758058755460611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22577270606709646695789925 4233238238758058755460611)
                      ·
                        rfl

theorem cell23_8244202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_8244202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244202 prefixEnd_8244202 := by exact prefixLift 8244202
  have htrace : WordTrace (prefixWord ++ tailWord_8244202) baseStart_8244202 baseEnd_8244202 := by
    simpa [prefixWord, tailWord_8244202, baseEnd_8244202] using wordTrace_append hprefix tailTrace_8244202
  have hstable : (prefixWord ++ tailWord_8244202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244202).length < 2 ^ (prefixWord ++ tailWord_8244202).sum := by decide
  have hdescent : baseEnd_8244202 < baseStart_8244202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244263 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 5]
def baseStart_8244263 : Nat := 118140960795 + 8244263 * 2 ^ 59
def prefixEnd_8244263 : Nat := 4983230072969 + 3 ^ 40 * 8244263 * 2
def baseEnd_8244263 : Nat := 470363284564220335199759

theorem tailTrace_8244263 : CollatzResearch.WordTrace tailWord_8244263 prefixEnd_8244263 470363284564220335199759 := by
  unfold tailWord_8244263
  simp only [CollatzResearch.WordTrace]
  refine ⟨300692974531450633868265443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200461983020967089245510295 300692974531450633868265443)
  ·
    refine ⟨451039461797175950802398165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300692974531450633868265443 451039461797175950802398165)
    ·
      refine ⟨10571237385871311346931207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 451039461797175950802398165 10571237385871311346931207)
      ·
        refine ⟨15856856078806967020396811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10571237385871311346931207 15856856078806967020396811)
        ·
          refine ⟨23785284118210450530595217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15856856078806967020396811 23785284118210450530595217)
          ·
            refine ⟨17838963088657837897946413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785284118210450530595217 17838963088657837897946413)
            ·
              refine ⟨6689611158246689211729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17838963088657837897946413 6689611158246689211729905)
              ·
                refine ⟨5017208368685016908797429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689611158246689211729905 5017208368685016908797429)
                ·
                  refine ⟨470363284564220335199759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017208368685016908797429 470363284564220335199759)
                  ·
                    rfl

theorem cell23_8244263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 5].length) (baseStart_8244263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244263 prefixEnd_8244263 := by exact prefixLift 8244263
  have htrace : WordTrace (prefixWord ++ tailWord_8244263) baseStart_8244263 baseEnd_8244263 := by
    simpa [prefixWord, tailWord_8244263, baseEnd_8244263] using wordTrace_append hprefix tailTrace_8244263
  have hstable : (prefixWord ++ tailWord_8244263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244263).length < 2 ^ (prefixWord ++ tailWord_8244263).sum := by decide
  have hdescent : baseEnd_8244263 < baseStart_8244263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244282 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_8244282 : Nat := 118140960795 + 8244282 * 2 ^ 59
def prefixEnd_8244282 : Nat := 4983230072969 + 3 ^ 40 * 8244282 * 2
def baseEnd_8244282 : Nat := 4233279317210418442460243

theorem tailTrace_8244282 : CollatzResearch.WordTrace tailWord_8244282 prefixEnd_8244282 4233279317210418442460243 := by
  unfold tailWord_8244282
  simp only [CollatzResearch.WordTrace]
  refine ⟨75173416879595450028301775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200462445012254533408804733 75173416879595450028301775)
  ·
    refine ⟨112760125319393175042452663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75173416879595450028301775 112760125319393175042452663)
    ·
      refine ⟨169140187979089762563678995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112760125319393175042452663 169140187979089762563678995)
      ·
        refine ⟨253710281968634643845518493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169140187979089762563678995 253710281968634643845518493)
        ·
          refine ⟨95141355738237991442069435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253710281968634643845518493 95141355738237991442069435)
          ·
            refine ⟨142712033607356987163104153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95141355738237991442069435 142712033607356987163104153)
            ·
              refine ⟨107034025205517740372328115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142712033607356987163104153 107034025205517740372328115)
              ·
                refine ⟨160551037808276610558492173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107034025205517740372328115 160551037808276610558492173)
                ·
                  refine ⟨60206639178103728959434565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160551037808276610558492173 60206639178103728959434565)
                  ·
                    refine ⟨11288744845894449179893981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60206639178103728959434565 11288744845894449179893981)
                    ·
                      refine ⟨4233279317210418442460243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11288744845894449179893981 4233279317210418442460243)
                      ·
                        rfl

theorem cell23_8244282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_8244282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244282 prefixEnd_8244282 := by exact prefixLift 8244282
  have htrace : WordTrace (prefixWord ++ tailWord_8244282) baseStart_8244282 baseEnd_8244282 := by
    simpa [prefixWord, tailWord_8244282, baseEnd_8244282] using wordTrace_append hprefix tailTrace_8244282
  have hstable : (prefixWord ++ tailWord_8244282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244282).length < 2 ^ (prefixWord ++ tailWord_8244282).sum := by decide
  have hdescent : baseEnd_8244282 < baseStart_8244282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244332 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_8244332 : Nat := 118140960795 + 8244332 * 2 ^ 59
def prefixEnd_8244332 : Nat := 4983230072969 + 3 ^ 40 * 8244332 * 2
def baseEnd_8244332 : Nat := 1411101663747714415611671

theorem tailTrace_8244332 : CollatzResearch.WordTrace tailWord_8244332 prefixEnd_8244332 1411101663747714415611671 := by
  unfold tailWord_8244332
  simp only [CollatzResearch.WordTrace]
  refine ⟨150347745584100329326263625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200463660778800439101684833 150347745584100329326263625)
  ·
    refine ⟨112760809188075246994697719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150347745584100329326263625 112760809188075246994697719)
    ·
      refine ⟨169141213782112870492046579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112760809188075246994697719 169141213782112870492046579)
      ·
        refine ⟨253711820673169305738069869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169141213782112870492046579 253711820673169305738069869)
        ·
          refine ⟨95141932752438489651776201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253711820673169305738069869 95141932752438489651776201)
          ·
            refine ⟨71356449564328867238832151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95141932752438489651776201 71356449564328867238832151)
            ·
              refine ⟨107034674346493300858248227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71356449564328867238832151 107034674346493300858248227)
              ·
                refine ⟨160552011519739951287372341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107034674346493300858248227 160552011519739951287372341)
                ·
                  refine ⟨15051751079975620433191157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160552011519739951287372341 15051751079975620433191157)
                  ·
                    refine ⟨1411101663747714415611671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15051751079975620433191157 1411101663747714415611671)
                    ·
                      rfl

theorem cell23_8244332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_8244332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244332 prefixEnd_8244332 := by exact prefixLift 8244332
  have htrace : WordTrace (prefixWord ++ tailWord_8244332) baseStart_8244332 baseEnd_8244332 := by
    simpa [prefixWord, tailWord_8244332, baseEnd_8244332] using wordTrace_append hprefix tailTrace_8244332
  have hstable : (prefixWord ++ tailWord_8244332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244332).length < 2 ^ (prefixWord ++ tailWord_8244332).sum := by decide
  have hdescent : baseEnd_8244332 < baseStart_8244332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244349 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_8244349 : Nat := 118140960795 + 8244349 * 2 ^ 59
def prefixEnd_8244349 : Nat := 4983230072969 + 3 ^ 40 * 8244349 * 2
def baseEnd_8244349 : Nat := 1411104573471423226774145

theorem tailTrace_8244349 : CollatzResearch.WordTrace tailWord_8244349 prefixEnd_8244349 1411104573471423226774145 := by
  unfold tailWord_8244349
  simp only [CollatzResearch.WordTrace]
  refine ⟨300696111209139070555896101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200464074139426047037264067 300696111209139070555896101)
  ·
    refine ⟨56380520851713575729230519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300696111209139070555896101 56380520851713575729230519)
    ·
      refine ⟨84570781277570363593845779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56380520851713575729230519 84570781277570363593845779)
      ·
        refine ⟨126856171916355545390768669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84570781277570363593845779 126856171916355545390768669)
        ·
          refine ⟨47571064468633329521538251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126856171916355545390768669 47571064468633329521538251)
          ·
            refine ⟨71356596702949994282307377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47571064468633329521538251 71356596702949994282307377)
            ·
              refine ⟨53517447527212495711730533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71356596702949994282307377 53517447527212495711730533)
              ·
                refine ⟨10034521411352342945949475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53517447527212495711730533 10034521411352342945949475)
                ·
                  refine ⟨15051782117028514418924213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10034521411352342945949475 15051782117028514418924213)
                  ·
                    refine ⟨1411104573471423226774145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15051782117028514418924213 1411104573471423226774145)
                    ·
                      rfl

theorem cell23_8244349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_8244349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244349 prefixEnd_8244349 := by exact prefixLift 8244349
  have htrace : WordTrace (prefixWord ++ tailWord_8244349) baseStart_8244349 baseEnd_8244349 := by
    simpa [prefixWord, tailWord_8244349, baseEnd_8244349] using wordTrace_append hprefix tailTrace_8244349
  have hstable : (prefixWord ++ tailWord_8244349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244349).length < 2 ^ (prefixWord ++ tailWord_8244349).sum := by decide
  have hdescent : baseEnd_8244349 < baseStart_8244349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244350 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8244350 : Nat := 118140960795 + 8244350 * 2 ^ 59
def prefixEnd_8244350 : Nat := 4983230072969 + 3 ^ 40 * 8244350 * 2
def baseEnd_8244350 : Nat := 4233314233894924176409931

theorem tailTrace_8244350 : CollatzResearch.WordTrace tailWord_8244350 prefixEnd_8244350 4233314233894924176409931 := by
  unfold tailWord_8244350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587018460266930965835313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200464098454756965151121669 37587018460266930965835313)
  ·
    refine ⟨28190263845200198224376485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37587018460266930965835313 28190263845200198224376485)
    ·
      refine ⟨5285674470975037167070591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28190263845200198224376485 5285674470975037167070591)
      ·
        refine ⟨7928511706462555750605887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285674470975037167070591 7928511706462555750605887)
        ·
          refine ⟨11892767559693833625908831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928511706462555750605887 11892767559693833625908831)
          ·
            refine ⟨17839151339540750438863247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11892767559693833625908831 17839151339540750438863247)
            ·
              refine ⟨26758727009311125658294871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839151339540750438863247 26758727009311125658294871)
              ·
                refine ⟨40138090513966688487442307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26758727009311125658294871 40138090513966688487442307)
                ·
                  refine ⟨60207135770950032731163461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40138090513966688487442307 60207135770950032731163461)
                  ·
                    refine ⟨11288837957053131137093149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60207135770950032731163461 11288837957053131137093149)
                    ·
                      refine ⟨4233314233894924176409931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11288837957053131137093149 4233314233894924176409931)
                      ·
                        rfl

theorem cell23_8244350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8244350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244350 prefixEnd_8244350 := by exact prefixLift 8244350
  have htrace : WordTrace (prefixWord ++ tailWord_8244350) baseStart_8244350 baseEnd_8244350 := by
    simpa [prefixWord, tailWord_8244350, baseEnd_8244350] using wordTrace_append hprefix tailTrace_8244350
  have hstable : (prefixWord ++ tailWord_8244350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244350).length < 2 ^ (prefixWord ++ tailWord_8244350).sum := by decide
  have hdescent : baseEnd_8244350 < baseStart_8244350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244356 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_8244356 : Nat := 118140960795 + 8244356 * 2 ^ 59
def prefixEnd_8244356 : Nat := 4983230072969 + 3 ^ 40 * 8244356 * 2
def baseEnd_8244356 : Nat := 4233317314778851152934903

theorem tailTrace_8244356 : CollatzResearch.WordTrace tailWord_8244356 prefixEnd_8244356 4233317314778851152934903 := by
  unfold tailWord_8244356
  simp only [CollatzResearch.WordTrace]
  refine ⟨150348183260056855375700461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200464244346742473834267281 150348183260056855375700461)
  ·
    refine ⟨56380568722521320765887673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150348183260056855375700461 56380568722521320765887673)
    ·
      refine ⟨42285426541890990574415755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56380568722521320765887673 42285426541890990574415755)
      ·
        refine ⟨63428139812836485861623633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42285426541890990574415755 63428139812836485861623633)
        ·
          refine ⟨47571104859627364396217725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63428139812836485861623633 47571104859627364396217725)
          ·
            refine ⟨17839164322360261648581647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47571104859627364396217725 17839164322360261648581647)
            ·
              refine ⟨26758746483540392472872471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839164322360261648581647 26758746483540392472872471)
              ·
                refine ⟨40138119725310588709308707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26758746483540392472872471 40138119725310588709308707)
                ·
                  refine ⟨60207179587965883063963061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40138119725310588709308707 60207179587965883063963061)
                  ·
                    refine ⟨5644423086371801537246537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60207179587965883063963061 5644423086371801537246537)
                    ·
                      refine ⟨4233317314778851152934903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644423086371801537246537 4233317314778851152934903)
                      ·
                        rfl

theorem cell23_8244356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_8244356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244356 prefixEnd_8244356 := by exact prefixLift 8244356
  have htrace : WordTrace (prefixWord ++ tailWord_8244356) baseStart_8244356 baseEnd_8244356 := by
    simpa [prefixWord, tailWord_8244356, baseEnd_8244356] using wordTrace_append hprefix tailTrace_8244356
  have hstable : (prefixWord ++ tailWord_8244356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244356).length < 2 ^ (prefixWord ++ tailWord_8244356).sum := by decide
  have hdescent : baseEnd_8244356 < baseStart_8244356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244366 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_8244366 : Nat := 118140960795 + 8244366 * 2 ^ 59
def prefixEnd_8244366 : Nat := 4983230072969 + 3 ^ 40 * 8244366 * 2
def baseEnd_8244366 : Nat := 1411107483195132037936619

theorem tailTrace_8244366 : CollatzResearch.WordTrace tailWord_8244366 prefixEnd_8244366 1411107483195132037936619 := by
  unfold tailWord_8244366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587091406259685307408119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200464487500051654972843301 37587091406259685307408119)
  ·
    refine ⟨56380637109389527961112179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37587091406259685307408119 56380637109389527961112179)
    ·
      refine ⟨84570955664084291941668269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56380637109389527961112179 84570955664084291941668269)
      ·
        refine ⟨31714108374031609478125601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84570955664084291941668269 31714108374031609478125601)
        ·
          refine ⟨23785581280523707108594201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31714108374031609478125601 23785581280523707108594201)
          ·
            refine ⟨17839185960392780331445651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785581280523707108594201 17839185960392780331445651)
            ·
              refine ⟨26758778940589170497168477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839185960392780331445651 26758778940589170497168477)
              ·
                refine ⟨10034542102720938936438179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26758778940589170497168477 10034542102720938936438179)
                ·
                  refine ⟨15051813154081408404657269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10034542102720938936438179 15051813154081408404657269)
                  ·
                    refine ⟨1411107483195132037936619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15051813154081408404657269 1411107483195132037936619)
                    ·
                      rfl

theorem cell23_8244366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_8244366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244366 prefixEnd_8244366 := by exact prefixLift 8244366
  have htrace : WordTrace (prefixWord ++ tailWord_8244366) baseStart_8244366 baseEnd_8244366 := by
    simpa [prefixWord, tailWord_8244366, baseEnd_8244366] using wordTrace_append hprefix tailTrace_8244366
  have hstable : (prefixWord ++ tailWord_8244366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244366).length < 2 ^ (prefixWord ++ tailWord_8244366).sum := by decide
  have hdescent : baseEnd_8244366 < baseStart_8244366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244389 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_8244389 : Nat := 118140960795 + 8244389 * 2 ^ 59
def prefixEnd_8244389 : Nat := 4983230072969 + 3 ^ 40 * 8244389 * 2
def baseEnd_8244389 : Nat := 4233334259640449523822251

theorem tailTrace_8244389 : CollatzResearch.WordTrace tailWord_8244389 prefixEnd_8244389 4233334259640449523822251 := by
  unfold tailWord_8244389
  simp only [CollatzResearch.WordTrace]
  refine ⟨300697570128994157387352221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200465046752662771591568147 300697570128994157387352221)
  ·
    refine ⟨112761588798372809020257083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300697570128994157387352221 112761588798372809020257083)
    ·
      refine ⟨169142383197559213530385625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112761588798372809020257083 169142383197559213530385625)
      ·
        refine ⟨126856787398169410147789219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169142383197559213530385625 126856787398169410147789219)
        ·
          refine ⟨190285181097254115221683829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126856787398169410147789219 190285181097254115221683829)
          ·
            refine ⟨17839235727867573302032859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190285181097254115221683829 17839235727867573302032859)
            ·
              refine ⟨26758853591801359953049289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839235727867573302032859 26758853591801359953049289)
              ·
                refine ⟨20069140193851019964786967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26758853591801359953049289 20069140193851019964786967)
                ·
                  refine ⟨30103710290776529947180451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20069140193851019964786967 30103710290776529947180451)
                  ·
                    refine ⟨45155565436164794920770677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30103710290776529947180451 45155565436164794920770677)
                    ·
                      refine ⟨4233334259640449523822251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45155565436164794920770677 4233334259640449523822251)
                      ·
                        rfl

theorem cell23_8244389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_8244389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244389 prefixEnd_8244389 := by exact prefixLift 8244389
  have htrace : WordTrace (prefixWord ++ tailWord_8244389) baseStart_8244389 baseEnd_8244389 := by
    simpa [prefixWord, tailWord_8244389, baseEnd_8244389] using wordTrace_append hprefix tailTrace_8244389
  have hstable : (prefixWord ++ tailWord_8244389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244389).length < 2 ^ (prefixWord ++ tailWord_8244389).sum := by decide
  have hdescent : baseEnd_8244389 < baseStart_8244389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244399 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_8244399 : Nat := 118140960795 + 8244399 * 2 ^ 59
def prefixEnd_8244399 : Nat := 4983230072969 + 3 ^ 40 * 8244399 * 2
def baseEnd_8244399 : Nat := 4233339394446994484697205

theorem tailTrace_8244399 : CollatzResearch.WordTrace tailWord_8244399 prefixEnd_8244399 4233339394446994484697205 := by
  unfold tailWord_8244399
  simp only [CollatzResearch.WordTrace]
  refine ⟨300697934858957929095216251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200465289905971952730144167 300697934858957929095216251)
  ·
    refine ⟨451046902288436893642824377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300697934858957929095216251 451046902288436893642824377)
    ·
      refine ⟨338285176716327670232118283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451046902288436893642824377 338285176716327670232118283)
      ·
        refine ⟨507427765074491505348177425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338285176716327670232118283 507427765074491505348177425)
        ·
          refine ⟨380570823805868629011133069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507427765074491505348177425 380570823805868629011133069)
          ·
            refine ⟨142714058927200735879174901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380570823805868629011133069 142714058927200735879174901)
            ·
              refine ⟨13379443024425068988672647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142714058927200735879174901 13379443024425068988672647)
              ·
                refine ⟨20069164536637603483008971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379443024425068988672647 20069164536637603483008971)
                ·
                  refine ⟨30103746804956405224513457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20069164536637603483008971 30103746804956405224513457)
                  ·
                    refine ⟨22577810103717303918385093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30103746804956405224513457 22577810103717303918385093)
                    ·
                      refine ⟨4233339394446994484697205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22577810103717303918385093 4233339394446994484697205)
                      ·
                        rfl

theorem cell23_8244399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_8244399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244399 prefixEnd_8244399 := by exact prefixLift 8244399
  have htrace : WordTrace (prefixWord ++ tailWord_8244399) baseStart_8244399 baseEnd_8244399 := by
    simpa [prefixWord, tailWord_8244399, baseEnd_8244399] using wordTrace_append hprefix tailTrace_8244399
  have hstable : (prefixWord ++ tailWord_8244399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244399).length < 2 ^ (prefixWord ++ tailWord_8244399).sum := by decide
  have hdescent : baseEnd_8244399 < baseStart_8244399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244409 : List Nat := [1, 2, 1, 4, 1, 3, 4, 7]
def baseStart_8244409 : Nat := 118140960795 + 8244409 * 2 ^ 59
def prefixEnd_8244409 : Nat := 4983230072969 + 3 ^ 40 * 8244409 * 2
def baseEnd_8244409 : Nat := 156790538120501460947117

theorem tailTrace_8244409 : CollatzResearch.WordTrace tailWord_8244409 prefixEnd_8244409 156790538120501460947117 := by
  unfold tailWord_8244409
  simp only [CollatzResearch.WordTrace]
  refine ⟨300698299588921700803080281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200465533059281133868720187 300698299588921700803080281)
  ·
    refine ⟨225523724691691275602310211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300698299588921700803080281 225523724691691275602310211)
    ·
      refine ⟨338285587037536913403465317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225523724691691275602310211 338285587037536913403465317)
      ·
        refine ⟨63428547569538171263149747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338285587037536913403465317 63428547569538171263149747)
        ·
          refine ⟨95142821354307256894724621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63428547569538171263149747 95142821354307256894724621)
          ·
            refine ⟨35678558007865221335521733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95142821354307256894724621 35678558007865221335521733)
            ·
              refine ⟨6689729626474729000410325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35678558007865221335521733 6689729626474729000410325)
              ·
                refine ⟨156790538120501460947117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6689729626474729000410325 156790538120501460947117)
                ·
                  rfl

theorem cell23_8244409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 7].length) (baseStart_8244409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244409 prefixEnd_8244409 := by exact prefixLift 8244409
  have htrace : WordTrace (prefixWord ++ tailWord_8244409) baseStart_8244409 baseEnd_8244409 := by
    simpa [prefixWord, tailWord_8244409, baseEnd_8244409] using wordTrace_append hprefix tailTrace_8244409
  have hstable : (prefixWord ++ tailWord_8244409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244409).length < 2 ^ (prefixWord ++ tailWord_8244409).sum := by decide
  have hdescent : baseEnd_8244409 < baseStart_8244409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244463 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 3, 3, 2]
def baseStart_8244463 : Nat := 118140960795 + 8244463 * 2 ^ 59
def prefixEnd_8244463 : Nat := 4983230072969 + 3 ^ 40 * 8244463 * 2
def baseEnd_8244463 : Nat := 4233372257208882234296911

theorem tailTrace_8244463 : CollatzResearch.WordTrace tailWord_8244463 prefixEnd_8244463 4233372257208882234296911 := by
  unfold tailWord_8244463
  simp only [CollatzResearch.WordTrace]
  refine ⟨300700269130726068025546043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200466846087150712017030695 300700269130726068025546043)
  ·
    refine ⟨451050403696089102038319065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300700269130726068025546043 451050403696089102038319065)
    ·
      refine ⟨338287802772066826528739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451050403696089102038319065 338287802772066826528739299)
      ·
        refine ⟨507431704158100239793108949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338287802772066826528739299 507431704158100239793108949)
        ·
          refine ⟨11892930566205474370150991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 507431704158100239793108949 11892930566205474370150991)
          ·
            refine ⟨17839395849308211555226487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11892930566205474370150991 17839395849308211555226487)
            ·
              refine ⟨26759093773962317332839731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839395849308211555226487 26759093773962317332839731)
              ·
                refine ⟨40138640660943475999259597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26759093773962317332839731 40138640660943475999259597)
                ·
                  refine ⟨15051990247853803499722349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40138640660943475999259597 15051990247853803499722349)
                  ·
                    refine ⟨5644496342945176312395881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15051990247853803499722349 5644496342945176312395881)
                    ·
                      refine ⟨4233372257208882234296911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644496342945176312395881 4233372257208882234296911)
                      ·
                        rfl

theorem cell23_8244463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3, 2].length) (baseStart_8244463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244463 prefixEnd_8244463 := by exact prefixLift 8244463
  have htrace : WordTrace (prefixWord ++ tailWord_8244463) baseStart_8244463 baseEnd_8244463 := by
    simpa [prefixWord, tailWord_8244463, baseEnd_8244463] using wordTrace_append hprefix tailTrace_8244463
  have hstable : (prefixWord ++ tailWord_8244463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244463).length < 2 ^ (prefixWord ++ tailWord_8244463).sum := by decide
  have hdescent : baseEnd_8244463 < baseStart_8244463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244479 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_8244479 : Nat := 118140960795 + 8244479 * 2 ^ 59
def prefixEnd_8244479 : Nat := 4983230072969 + 3 ^ 40 * 8244479 * 2
def baseEnd_8244479 : Nat := 4233380472899354171696837

theorem tailTrace_8244479 : CollatzResearch.WordTrace tailWord_8244479 prefixEnd_8244479 4233380472899354171696837 := by
  unfold tailWord_8244479
  simp only [CollatzResearch.WordTrace]
  refine ⟨300700852698668102758128491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200467235132445401838752327 300700852698668102758128491)
  ·
    refine ⟨451051279048002154137192737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300700852698668102758128491 451051279048002154137192737)
    ·
      refine ⟨338288459286001615602894553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451051279048002154137192737 338288459286001615602894553)
      ·
        refine ⟨253716344464501211702170915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338288459286001615602894553 253716344464501211702170915)
        ·
          refine ⟨380574516696751817553256373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253716344464501211702170915 380574516696751817553256373)
          ·
            refine ⟨35678860940320482895617785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380574516696751817553256373 35678860940320482895617785)
            ·
              refine ⟨26759145705240362171713339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35678860940320482895617785 26759145705240362171713339)
              ·
                refine ⟨40138718557860543257570009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26759145705240362171713339 40138718557860543257570009)
                ·
                  refine ⟨30104038918395407443177507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40138718557860543257570009 30104038918395407443177507)
                  ·
                    refine ⟨45156058377593111164766261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30104038918395407443177507 45156058377593111164766261)
                    ·
                      refine ⟨4233380472899354171696837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45156058377593111164766261 4233380472899354171696837)
                      ·
                        rfl

theorem cell23_8244479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_8244479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244479 prefixEnd_8244479 := by exact prefixLift 8244479
  have htrace : WordTrace (prefixWord ++ tailWord_8244479) baseStart_8244479 baseEnd_8244479 := by
    simpa [prefixWord, tailWord_8244479, baseEnd_8244479] using wordTrace_append hprefix tailTrace_8244479
  have hstable : (prefixWord ++ tailWord_8244479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244479).length < 2 ^ (prefixWord ++ tailWord_8244479).sum := by decide
  have hdescent : baseEnd_8244479 < baseStart_8244479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244489 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_8244489 : Nat := 118140960795 + 8244489 * 2 ^ 59
def prefixEnd_8244489 : Nat := 4983230072969 + 3 ^ 40 * 8244489 * 2
def baseEnd_8244489 : Nat := 4233385607705899132571791

theorem tailTrace_8244489 : CollatzResearch.WordTrace tailWord_8244489 prefixEnd_8244489 4233385607705899132571791 := by
  unfold tailWord_8244489
  simp only [CollatzResearch.WordTrace]
  refine ⟨300701217428631874465992521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200467478285754582977328347 300701217428631874465992521)
  ·
    refine ⟨225525913071473905849494391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300701217428631874465992521 225525913071473905849494391)
    ·
      refine ⟨338288869607210858774241587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225525913071473905849494391 338288869607210858774241587)
      ·
        refine ⟨507433304410816288161362381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338288869607210858774241587 507433304410816288161362381)
        ·
          refine ⟨190287489154056108060510893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507433304410816288161362381 190287489154056108060510893)
          ·
            refine ⟨71357808432771040522691585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190287489154056108060510893 71357808432771040522691585)
            ·
              refine ⟨53518356324578280392018689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71357808432771040522691585 53518356324578280392018689)
              ·
                refine ⟨40138767243433710294014017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53518356324578280392018689 40138767243433710294014017)
                ·
                  refine ⟨30104075432575282720510513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40138767243433710294014017 30104075432575282720510513)
                  ·
                    refine ⟨22578056574431462040382885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30104075432575282720510513 22578056574431462040382885)
                    ·
                      refine ⟨4233385607705899132571791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22578056574431462040382885 4233385607705899132571791)
                      ·
                        rfl

theorem cell23_8244489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_8244489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244489 prefixEnd_8244489 := by exact prefixLift 8244489
  have htrace : WordTrace (prefixWord ++ tailWord_8244489) baseStart_8244489 baseEnd_8244489 := by
    simpa [prefixWord, tailWord_8244489, baseEnd_8244489] using wordTrace_append hprefix tailTrace_8244489
  have hstable : (prefixWord ++ tailWord_8244489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244489).length < 2 ^ (prefixWord ++ tailWord_8244489).sum := by decide
  have hdescent : baseEnd_8244489 < baseStart_8244489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244506 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_8244506 : Nat := 118140960795 + 8244506 * 2 ^ 59
def prefixEnd_8244506 : Nat := 4983230072969 + 3 ^ 40 * 8244506 * 2
def baseEnd_8244506 : Nat := 4233394336877025566059213

theorem tailTrace_8244506 : CollatzResearch.WordTrace tailWord_8244506 prefixEnd_8244506 4233394336877025566059213 := by
  unfold tailWord_8244506
  simp only [CollatzResearch.WordTrace]
  refine ⟨75175459367392571592340343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200467891646380190912907581 75175459367392571592340343)
  ·
    refine ⟨112763189051088857388510515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75175459367392571592340343 112763189051088857388510515)
    ·
      refine ⟨169144783576633286082765773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112763189051088857388510515 169144783576633286082765773)
      ·
        refine ⟨63429293841237482281037165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169144783576633286082765773 63429293841237482281037165)
        ·
          refine ⟨23785985190464055855388937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63429293841237482281037165 23785985190464055855388937)
          ·
            refine ⟨17839488892848041891541703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785985190464055855388937 17839488892848041891541703)
            ·
              refine ⟨26759233339272062837312555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839488892848041891541703 26759233339272062837312555)
              ·
                refine ⟨40138850008908094255968833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26759233339272062837312555 40138850008908094255968833)
                ·
                  refine ⟨30104137506681070691976625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40138850008908094255968833 30104137506681070691976625)
                  ·
                    refine ⟨22578103130010803018982469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30104137506681070691976625 22578103130010803018982469)
                    ·
                      refine ⟨4233394336877025566059213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22578103130010803018982469 4233394336877025566059213)
                      ·
                        rfl

theorem cell23_8244506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_8244506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244506 prefixEnd_8244506 := by exact prefixLift 8244506
  have htrace : WordTrace (prefixWord ++ tailWord_8244506) baseStart_8244506 baseEnd_8244506 := by
    simpa [prefixWord, tailWord_8244506, baseEnd_8244506] using wordTrace_append hprefix tailTrace_8244506
  have hstable : (prefixWord ++ tailWord_8244506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244506).length < 2 ^ (prefixWord ++ tailWord_8244506).sum := by decide
  have hdescent : baseEnd_8244506 < baseStart_8244506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244533 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 5]
def baseStart_8244533 : Nat := 118140960795 + 8244533 * 2 ^ 59
def prefixEnd_8244533 : Nat := 4983230072969 + 3 ^ 40 * 8244533 * 2
def baseEnd_8244533 : Nat := 470378688983855217824621

theorem tailTrace_8244533 : CollatzResearch.WordTrace tailWord_8244533 prefixEnd_8244533 470378688983855217824621 := by
  unfold tailWord_8244533
  simp only [CollatzResearch.WordTrace]
  refine ⟨300702822240472469980594253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200468548160314979987062835 300702822240472469980594253)
  ·
    refine ⟨112763558340177176242722845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300702822240472469980594253 112763558340177176242722845)
    ·
      refine ⟨42286334377566441091021067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112763558340177176242722845 42286334377566441091021067)
      ·
        refine ⟨63429501566349661636531601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42286334377566441091021067 63429501566349661636531601)
        ·
          refine ⟨47572126174762246227398701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63429501566349661636531601 47572126174762246227398701)
          ·
            refine ⟨17839547315535842335274513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47572126174762246227398701 17839547315535842335274513)
            ·
              refine ⟨13379660486651881751455885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17839547315535842335274513 13379660486651881751455885)
              ·
                refine ⟨5017372682494455656795957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13379660486651881751455885 5017372682494455656795957)
                ·
                  refine ⟨470378688983855217824621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017372682494455656795957 470378688983855217824621)
                  ·
                    rfl

theorem cell23_8244533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_8244533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244533 prefixEnd_8244533 := by exact prefixLift 8244533
  have htrace : WordTrace (prefixWord ++ tailWord_8244533) baseStart_8244533 baseEnd_8244533 := by
    simpa [prefixWord, tailWord_8244533, baseEnd_8244533] using wordTrace_append hprefix tailTrace_8244533
  have hstable : (prefixWord ++ tailWord_8244533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244533).length < 2 ^ (prefixWord ++ tailWord_8244533).sum := by decide
  have hdescent : baseEnd_8244533 < baseStart_8244533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244683 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 2, 4]
def baseStart_8244683 : Nat := 118140960795 + 8244683 * 2 ^ 59
def prefixEnd_8244683 : Nat := 4983230072969 + 3 ^ 40 * 8244683 * 2
def baseEnd_8244683 : Nat := 1411161740984290457848633

theorem tailTrace_8244683 : CollatzResearch.WordTrace tailWord_8244683 prefixEnd_8244683 1411161740984290457848633 := by
  unfold tailWord_8244683
  simp only [CollatzResearch.WordTrace]
  refine ⟨300708293189929045598554703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200472195459952697065703135 300708293189929045598554703)
  ·
    refine ⟨451062439784893568397832055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300708293189929045598554703 451062439784893568397832055)
    ·
      refine ⟨676593659677340352596748083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451062439784893568397832055 676593659677340352596748083)
      ·
        refine ⟨1014890489516010528895122125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676593659677340352596748083 1014890489516010528895122125)
        ·
          refine ⟨380583933568503948335670797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1014890489516010528895122125 380583933568503948335670797)
          ·
            refine ⟨142718975088188980625876549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380583933568503948335670797 142718975088188980625876549)
            ·
              refine ⟨26759807829035433867351853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142718975088188980625876549 26759807829035433867351853)
              ·
                refine ⟨10034927935888287700256945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26759807829035433867351853 10034927935888287700256945)
                ·
                  refine ⟨7526195951916215775192709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10034927935888287700256945 7526195951916215775192709)
                  ·
                    refine ⟨1411161740984290457848633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526195951916215775192709 1411161740984290457848633)
                    ·
                      rfl

theorem cell23_8244683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 4].length) (baseStart_8244683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244683 prefixEnd_8244683 := by exact prefixLift 8244683
  have htrace : WordTrace (prefixWord ++ tailWord_8244683) baseStart_8244683 baseEnd_8244683 := by
    simpa [prefixWord, tailWord_8244683, baseEnd_8244683] using wordTrace_append hprefix tailTrace_8244683
  have hstable : (prefixWord ++ tailWord_8244683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244683).length < 2 ^ (prefixWord ++ tailWord_8244683).sum := by decide
  have hdescent : baseEnd_8244683 < baseStart_8244683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244686 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_8244686 : Nat := 118140960795 + 8244686 * 2 ^ 59
def prefixEnd_8244686 : Nat := 4983230072969 + 3 ^ 40 * 8244686 * 2
def baseEnd_8244686 : Nat := 4233486763394834861808385

theorem tailTrace_8244686 : CollatzResearch.WordTrace tailWord_8244686 prefixEnd_8244686 4233486763394834861808385 := by
  unfold tailWord_8244686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588550326114772138864239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200472268405945451407275941 37588550326114772138864239)
  ·
    refine ⟨56382825489172158208296359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37588550326114772138864239 56382825489172158208296359)
    ·
      refine ⟨84574238233758237312444539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56382825489172158208296359 84574238233758237312444539)
      ·
        refine ⟨126861357350637355968666809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84574238233758237312444539 126861357350637355968666809)
        ·
          refine ⟨95146018012978016976500107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126861357350637355968666809 95146018012978016976500107)
          ·
            refine ⟨142719027019467025464750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95146018012978016976500107 142719027019467025464750161)
            ·
              refine ⟨107039270264600269098562621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142719027019467025464750161 107039270264600269098562621)
              ·
                refine ⟨40139726349225100911960983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107039270264600269098562621 40139726349225100911960983)
                ·
                  refine ⟨60209589523837651367941475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40139726349225100911960983 60209589523837651367941475)
                  ·
                    refine ⟨90314384285756477051912213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60209589523837651367941475 90314384285756477051912213)
                    ·
                      refine ⟨4233486763394834861808385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90314384285756477051912213 4233486763394834861808385)
                      ·
                        rfl

theorem cell23_8244686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_8244686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244686 prefixEnd_8244686 := by exact prefixLift 8244686
  have htrace : WordTrace (prefixWord ++ tailWord_8244686) baseStart_8244686 baseEnd_8244686 := by
    simpa [prefixWord, tailWord_8244686, baseEnd_8244686] using wordTrace_append hprefix tailTrace_8244686
  have hstable : (prefixWord ++ tailWord_8244686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244686).length < 2 ^ (prefixWord ++ tailWord_8244686).sum := by decide
  have hdescent : baseEnd_8244686 < baseStart_8244686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244693 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_8244693 : Nat := 118140960795 + 8244693 * 2 ^ 59
def prefixEnd_8244693 : Nat := 4983230072969 + 3 ^ 40 * 8244693 * 2
def baseEnd_8244693 : Nat := 4233490357759416334420853

theorem tailTrace_8244693 : CollatzResearch.WordTrace tailWord_8244693 prefixEnd_8244693 4233490357759416334420853 := by
  unfold tailWord_8244693
  simp only [CollatzResearch.WordTrace]
  refine ⟨300708657919892817306418733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200472438613261878204279155 300708657919892817306418733)
  ·
    refine ⟨112765746719959806489907025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300708657919892817306418733 112765746719959806489907025)
    ·
      refine ⟨84574310039969854867430269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112765746719959806489907025 84574310039969854867430269)
      ·
        refine ⟨31715366264988695575286351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84574310039969854867430269 31715366264988695575286351)
        ·
          refine ⟨47573049397483043362929527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31715366264988695575286351 47573049397483043362929527)
          ·
            refine ⟨71359574096224565044394291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47573049397483043362929527 71359574096224565044394291)
            ·
              refine ⟨107039361144336847566591437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71359574096224565044394291 107039361144336847566591437)
              ·
                refine ⟨40139760429126317837471789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107039361144336847566591437 40139760429126317837471789)
                ·
                  refine ⟨15052410160922369189051921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40139760429126317837471789 15052410160922369189051921)
                  ·
                    refine ⟨11289307620691776891788941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15052410160922369189051921 11289307620691776891788941)
                    ·
                      refine ⟨4233490357759416334420853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11289307620691776891788941 4233490357759416334420853)
                      ·
                        rfl

theorem cell23_8244693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_8244693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244693 prefixEnd_8244693 := by exact prefixLift 8244693
  have htrace : WordTrace (prefixWord ++ tailWord_8244693) baseStart_8244693 baseEnd_8244693 := by
    simpa [prefixWord, tailWord_8244693, baseEnd_8244693] using wordTrace_append hprefix tailTrace_8244693
  have hstable : (prefixWord ++ tailWord_8244693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244693).length < 2 ^ (prefixWord ++ tailWord_8244693).sum := by decide
  have hdescent : baseEnd_8244693 < baseStart_8244693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244694 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_8244694 : Nat := 118140960795 + 8244694 * 2 ^ 59
def prefixEnd_8244694 : Nat := 4983230072969 + 3 ^ 40 * 8244694 * 2
def baseEnd_8244694 : Nat := 4233490871240070830508349

theorem tailTrace_8244694 : CollatzResearch.WordTrace tailWord_8244694 prefixEnd_8244694 4233490871240070830508349 := by
  unfold tailWord_8244694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794293399555574654825321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200472462928592796318136757 18794293399555574654825321)
  ·
    refine ⟨14095720049666680991118991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18794293399555574654825321 14095720049666680991118991)
    ·
      refine ⟨21143580074500021486678487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14095720049666680991118991 21143580074500021486678487)
      ·
        refine ⟨31715370111750032230017731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21143580074500021486678487 31715370111750032230017731)
        ·
          refine ⟨47573055167625048345026597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31715370111750032230017731 47573055167625048345026597)
          ·
            refine ⟨8919947843929696564692487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47573055167625048345026597 8919947843929696564692487)
            ·
              refine ⟨13379921765894544847038731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919947843929696564692487 13379921765894544847038731)
              ·
                refine ⟨20069882648841817270558097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379921765894544847038731 20069882648841817270558097)
                ·
                  refine ⟨15052411986631362952918573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20069882648841817270558097 15052411986631362952918573)
                  ·
                    refine ⟨5644654494986761107344465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15052411986631362952918573 5644654494986761107344465)
                    ·
                      refine ⟨4233490871240070830508349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644654494986761107344465 4233490871240070830508349)
                      ·
                        rfl

theorem cell23_8244694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_8244694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244694 prefixEnd_8244694 := by exact prefixLift 8244694
  have htrace : WordTrace (prefixWord ++ tailWord_8244694) baseStart_8244694 baseEnd_8244694 := by
    simpa [prefixWord, tailWord_8244694, baseEnd_8244694] using wordTrace_append hprefix tailTrace_8244694
  have hstable : (prefixWord ++ tailWord_8244694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244694).length < 2 ^ (prefixWord ++ tailWord_8244694).sum := by decide
  have hdescent : baseEnd_8244694 < baseStart_8244694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244707 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 1, 1, 4]
def baseStart_8244707 : Nat := 118140960795 + 8244707 * 2 ^ 59
def prefixEnd_8244707 : Nat := 4983230072969 + 3 ^ 40 * 8244707 * 2
def baseEnd_8244707 : Nat := 4233497546488579279645789

theorem tailTrace_8244707 : CollatzResearch.WordTrace tailWord_8244707 prefixEnd_8244707 4233497546488579279645789 := by
  unfold tailWord_8244707
  simp only [CollatzResearch.WordTrace]
  refine ⟨300709168541842097697428375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200472779027894731798285583 300709168541842097697428375)
  ·
    refine ⟨451063752812763146546142563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300709168541842097697428375 451063752812763146546142563)
    ·
      refine ⟨676595629219144719819213845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451063752812763146546142563 676595629219144719819213845)
      ·
        refine ⟨31715420119647408741525649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 676595629219144719819213845 31715420119647408741525649)
        ·
          refine ⟨23786565089735556556144237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31715420119647408741525649 23786565089735556556144237)
          ·
            refine ⟨8919961908650833708554089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23786565089735556556144237 8919961908650833708554089)
            ·
              refine ⟨6689971431488125281415567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8919961908650833708554089 6689971431488125281415567)
              ·
                refine ⟨10034957147232187922123351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689971431488125281415567 10034957147232187922123351)
                ·
                  refine ⟨15052435720848281883185027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10034957147232187922123351 15052435720848281883185027)
                  ·
                    refine ⟨22578653581272422824777541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15052435720848281883185027 22578653581272422824777541)
                    ·
                      refine ⟨4233497546488579279645789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22578653581272422824777541 4233497546488579279645789)
                      ·
                        rfl

theorem cell23_8244707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_8244707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244707 prefixEnd_8244707 := by exact prefixLift 8244707
  have htrace : WordTrace (prefixWord ++ tailWord_8244707) baseStart_8244707 baseEnd_8244707 := by
    simpa [prefixWord, tailWord_8244707, baseEnd_8244707] using wordTrace_append hprefix tailTrace_8244707
  have hstable : (prefixWord ++ tailWord_8244707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244707).length < 2 ^ (prefixWord ++ tailWord_8244707).sum := by decide
  have hdescent : baseEnd_8244707 < baseStart_8244707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244734 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_8244734 : Nat := 118140960795 + 8244734 * 2 ^ 59
def prefixEnd_8244734 : Nat := 4983230072969 + 3 ^ 40 * 8244734 * 2
def baseEnd_8244734 : Nat := 1411170470155416891336055

theorem tailTrace_8244734 : CollatzResearch.WordTrace tailWord_8244734 prefixEnd_8244734 1411170470155416891336055 := by
  unfold tailWord_8244734
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588769164093035163582657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200473435541829520872440837 37588769164093035163582657)
  ·
    refine ⟨28191576873069776372686993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37588769164093035163582657 28191576873069776372686993)
    ·
      refine ⟨21143682654802332279515245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28191576873069776372686993 21143682654802332279515245)
      ·
        refine ⟨7928880995550874604818217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21143682654802332279515245 7928880995550874604818217)
        ·
          refine ⟨5946660746663155953613663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7928880995550874604818217 5946660746663155953613663)
          ·
            refine ⟨8919991119994733930420495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946660746663155953613663 8919991119994733930420495)
            ·
              refine ⟨13379986679992100895630743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919991119994733930420495 13379986679992100895630743)
              ·
                refine ⟨20069980019988151343446115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379986679992100895630743 20069980019988151343446115)
                ·
                  refine ⟨30104970029982227015169173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20069980019988151343446115 30104970029982227015169173)
                  ·
                    refine ⟨1411170470155416891336055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30104970029982227015169173 1411170470155416891336055)
                    ·
                      rfl

theorem cell23_8244734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_8244734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244734 prefixEnd_8244734 := by exact prefixLift 8244734
  have htrace : WordTrace (prefixWord ++ tailWord_8244734) baseStart_8244734 baseEnd_8244734 := by
    simpa [prefixWord, tailWord_8244734, baseEnd_8244734] using wordTrace_append hprefix tailTrace_8244734
  have hstable : (prefixWord ++ tailWord_8244734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244734).length < 2 ^ (prefixWord ++ tailWord_8244734).sum := by decide
  have hdescent : baseEnd_8244734 < baseStart_8244734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244737 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_8244737 : Nat := 118140960795 + 8244737 * 2 ^ 59
def prefixEnd_8244737 : Nat := 4983230072969 + 3 ^ 40 * 8244737 * 2
def baseEnd_8244737 : Nat := 4233512950908214162270651

theorem tailTrace_8244737 : CollatzResearch.WordTrace tailWord_8244737 prefixEnd_8244737 4233512950908214162270651 := by
  unfold tailWord_8244737
  simp only [CollatzResearch.WordTrace]
  refine ⟨300710262731733412821020465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200473508487822275214013643 300710262731733412821020465)
  ·
    refine ⟨225532697048800059615765349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300710262731733412821020465 225532697048800059615765349)
    ·
      refine ⟨42287380696650011177956003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225532697048800059615765349 42287380696650011177956003)
      ·
        refine ⟨63431071044975016766934005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42287380696650011177956003 63431071044975016766934005)
        ·
          refine ⟨5946662910466407821900063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63431071044975016766934005 5946662910466407821900063)
          ·
            refine ⟨8919994365699611732850095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946662910466407821900063 8919994365699611732850095)
            ·
              refine ⟨13379991548549417599275143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919994365699611732850095 13379991548549417599275143)
              ·
                refine ⟨20069987322824126398912715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379991548549417599275143 20069987322824126398912715)
                ·
                  refine ⟨30104980984236189598369073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20069987322824126398912715 30104980984236189598369073)
                  ·
                    refine ⟨22578735738177142198776805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30104980984236189598369073 22578735738177142198776805)
                    ·
                      refine ⟨4233512950908214162270651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22578735738177142198776805 4233512950908214162270651)
                      ·
                        rfl

theorem cell23_8244737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_8244737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244737 prefixEnd_8244737 := by exact prefixLift 8244737
  have htrace : WordTrace (prefixWord ++ tailWord_8244737) baseStart_8244737 baseEnd_8244737 := by
    simpa [prefixWord, tailWord_8244737, baseEnd_8244737] using wordTrace_append hprefix tailTrace_8244737
  have hstable : (prefixWord ++ tailWord_8244737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244737).length < 2 ^ (prefixWord ++ tailWord_8244737).sum := by decide
  have hdescent : baseEnd_8244737 < baseStart_8244737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244820 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 5]
def baseStart_8244820 : Nat := 118140960795 + 8244820 * 2 ^ 59
def prefixEnd_8244820 : Nat := 4983230072969 + 3 ^ 40 * 8244820 * 2
def baseEnd_8244820 : Nat := 470395063311393037503641

theorem tailTrace_8244820 : CollatzResearch.WordTrace tailWord_8244820 prefixEnd_8244820 470395063311393037503641 := by
  unfold tailWord_8244820
  simp only [CollatzResearch.WordTrace]
  refine ⟨150356644995216358998145957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200475526660288478664194609 150356644995216358998145957)
  ·
    refine ⟨28191870936603067312152367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150356644995216358998145957 28191870936603067312152367)
    ·
      refine ⟨42287806404904600968228551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28191870936603067312152367 42287806404904600968228551)
      ·
        refine ⟨63431709607356901452342827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42287806404904600968228551 63431709607356901452342827)
        ·
          refine ⟨95147564411035352178514241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63431709607356901452342827 95147564411035352178514241)
          ·
            refine ⟨71360673308276514133885681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95147564411035352178514241 71360673308276514133885681)
            ·
              refine ⟨53520504981207385600414261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71360673308276514133885681 53520504981207385600414261)
              ·
                refine ⟨5017547341988192400038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53520504981207385600414261 5017547341988192400038837)
                ·
                  refine ⟨470395063311393037503641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017547341988192400038837 470395063311393037503641)
                  ·
                    rfl

theorem cell23_8244820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_8244820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244820 prefixEnd_8244820 := by exact prefixLift 8244820
  have htrace : WordTrace (prefixWord ++ tailWord_8244820) baseStart_8244820 baseEnd_8244820 := by
    simpa [prefixWord, tailWord_8244820, baseEnd_8244820] using wordTrace_append hprefix tailTrace_8244820
  have hstable : (prefixWord ++ tailWord_8244820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244820).length < 2 ^ (prefixWord ++ tailWord_8244820).sum := by decide
  have hdescent : baseEnd_8244820 < baseStart_8244820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244833 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_8244833 : Nat := 118140960795 + 8244833 * 2 ^ 59
def prefixEnd_8244833 : Nat := 4983230072969 + 3 ^ 40 * 8244833 * 2
def baseEnd_8244833 : Nat := 1411187415017015262223403

theorem tailTrace_8244833 : CollatzResearch.WordTrace tailWord_8244833 prefixEnd_8244833 1411187415017015262223403 := by
  unfold tailWord_8244833
  simp only [CollatzResearch.WordTrace]
  refine ⟨300713764139385621216515153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200475842759590414144343435 300713764139385621216515153)
  ·
    refine ⟨225535323104539215912386365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300713764139385621216515153 225535323104539215912386365)
    ·
      refine ⟨84575746164202205967144887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225535323104539215912386365 84575746164202205967144887)
      ·
        refine ⟨126863619246303308950717331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84575746164202205967144887 126863619246303308950717331)
        ·
          refine ⟨190295428869454963426075997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126863619246303308950717331 190295428869454963426075997)
          ·
            refine ⟨71360785826045611284778499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190295428869454963426075997 71360785826045611284778499)
            ·
              refine ⟨107041178739068416927167749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71360785826045611284778499 107041178739068416927167749)
              ·
                refine ⟨20070221013575328173843953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107041178739068416927167749 20070221013575328173843953)
                ·
                  refine ⟨15052665760181496130382965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20070221013575328173843953 15052665760181496130382965)
                  ·
                    refine ⟨1411187415017015262223403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15052665760181496130382965 1411187415017015262223403)
                    ·
                      rfl

theorem cell23_8244833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_8244833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244833 prefixEnd_8244833 := by exact prefixLift 8244833
  have htrace : WordTrace (prefixWord ++ tailWord_8244833) baseStart_8244833 baseEnd_8244833 := by
    simpa [prefixWord, tailWord_8244833, baseEnd_8244833] using wordTrace_append hprefix tailTrace_8244833
  have hstable : (prefixWord ++ tailWord_8244833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244833).length < 2 ^ (prefixWord ++ tailWord_8244833).sum := by decide
  have hdescent : baseEnd_8244833 < baseStart_8244833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244837 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 5]
def baseStart_8244837 : Nat := 118140960795 + 8244837 * 2 ^ 59
def prefixEnd_8244837 : Nat := 4983230072969 + 3 ^ 40 * 8244837 * 2
def baseEnd_8244837 : Nat := 470396033219295974557799

theorem tailTrace_8244837 : CollatzResearch.WordTrace tailWord_8244837 prefixEnd_8244837 470396033219295974557799 := by
  unfold tailWord_8244837
  simp only [CollatzResearch.WordTrace]
  refine ⟨300713910031371129899660765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200475940020914086599773843 300713910031371129899660765)
  ·
    refine ⟨112767716261764173712372787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300713910031371129899660765 112767716261764173712372787)
    ·
      refine ⟨169151574392646260568559181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112767716261764173712372787 169151574392646260568559181)
      ·
        refine ⟨63431840397242347713209693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169151574392646260568559181 63431840397242347713209693)
        ·
          refine ⟨23786940148965880392453635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63431840397242347713209693 23786940148965880392453635)
          ·
            refine ⟨35680410223448820588680453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23786940148965880392453635 35680410223448820588680453)
            ·
              refine ⟨6690076916896653860377585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35680410223448820588680453 6690076916896653860377585)
              ·
                refine ⟨5017557687672490395283189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6690076916896653860377585 5017557687672490395283189)
                ·
                  refine ⟨470396033219295974557799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017557687672490395283189 470396033219295974557799)
                  ·
                    rfl

theorem cell23_8244837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_8244837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244837 prefixEnd_8244837 := by exact prefixLift 8244837
  have htrace : WordTrace (prefixWord ++ tailWord_8244837) baseStart_8244837 baseEnd_8244837 := by
    simpa [prefixWord, tailWord_8244837, baseEnd_8244837] using wordTrace_append hprefix tailTrace_8244837
  have hstable : (prefixWord ++ tailWord_8244837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244837).length < 2 ^ (prefixWord ++ tailWord_8244837).sum := by decide
  have hdescent : baseEnd_8244837 < baseStart_8244837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244897 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_8244897 : Nat := 118140960795 + 8244897 * 2 ^ 59
def prefixEnd_8244897 : Nat := 4983230072969 + 3 ^ 40 * 8244897 * 2
def baseEnd_8244897 : Nat := 1411198369270977845423305

theorem tailTrace_8244897 : CollatzResearch.WordTrace tailWord_8244897 prefixEnd_8244897 1411198369270977845423305 := by
  unfold tailWord_8244897
  simp only [CollatzResearch.WordTrace]
  refine ⟨300716098411153760146844945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200477398940769173431229963 300716098411153760146844945)
  ·
    refine ⟨225537073808365320110133709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300716098411153760146844945 225537073808365320110133709)
    ·
      refine ⟨84576402678136995041300141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225537073808365320110133709 84576402678136995041300141)
      ·
        refine ⟨31716151004301373140487553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84576402678136995041300141 31716151004301373140487553)
        ·
          refine ⟨23787113253226029855365665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31716151004301373140487553 23787113253226029855365665)
          ·
            refine ⟨17840334939919522391524249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23787113253226029855365665 17840334939919522391524249)
            ·
              refine ⟨13380251204939641793643187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17840334939919522391524249 13380251204939641793643187)
              ·
                refine ⟨20070376807409462690464781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380251204939641793643187 20070376807409462690464781)
                ·
                  refine ⟨7526391302778548508924293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20070376807409462690464781 7526391302778548508924293)
                  ·
                    refine ⟨1411198369270977845423305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526391302778548508924293 1411198369270977845423305)
                    ·
                      rfl

theorem cell23_8244897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_8244897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244897 prefixEnd_8244897 := by exact prefixLift 8244897
  have htrace : WordTrace (prefixWord ++ tailWord_8244897) baseStart_8244897 baseEnd_8244897 := by
    simpa [prefixWord, tailWord_8244897, baseEnd_8244897] using wordTrace_append hprefix tailTrace_8244897
  have hstable : (prefixWord ++ tailWord_8244897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244897).length < 2 ^ (prefixWord ++ tailWord_8244897).sum := by decide
  have hdescent : baseEnd_8244897 < baseStart_8244897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244923 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 3, 5]
def baseStart_8244923 : Nat := 118140960795 + 8244923 * 2 ^ 59
def prefixEnd_8244923 : Nat := 4983230072969 + 3 ^ 40 * 8244923 * 2
def baseEnd_8244923 : Nat := 1411202819436650144848265

theorem tailTrace_8244923 : CollatzResearch.WordTrace tailWord_8244923 prefixEnd_8244923 1411202819436650144848265 := by
  unfold tailWord_8244923
  simp only [CollatzResearch.WordTrace]
  refine ⟨300717046709059566587291423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200478031139373044391527615 300717046709059566587291423)
  ·
    refine ⟨451075570063589349880937135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300717046709059566587291423 451075570063589349880937135)
    ·
      refine ⟨676613355095384024821405703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451075570063589349880937135 676613355095384024821405703)
      ·
        refine ⟨1014920032643076037232108555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676613355095384024821405703 1014920032643076037232108555)
        ·
          refine ⟨1522380048964614055848162833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014920032643076037232108555 1522380048964614055848162833)
          ·
            refine ⟨1141785036723460541886122125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522380048964614055848162833 1141785036723460541886122125)
            ·
              refine ⟨428169388771297703207295797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141785036723460541886122125 428169388771297703207295797)
              ·
                refine ⟨40140880197309159675683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428169388771297703207295797 40140880197309159675683981)
                ·
                  refine ⟨15052830073990934878381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40140880197309159675683981 15052830073990934878381493)
                  ·
                    refine ⟨1411202819436650144848265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15052830073990934878381493 1411202819436650144848265)
                    ·
                      rfl

theorem cell23_8244923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].length) (baseStart_8244923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244923 prefixEnd_8244923 := by exact prefixLift 8244923
  have htrace : WordTrace (prefixWord ++ tailWord_8244923) baseStart_8244923 baseEnd_8244923 := by
    simpa [prefixWord, tailWord_8244923, baseEnd_8244923] using wordTrace_append hprefix tailTrace_8244923
  have hstable : (prefixWord ++ tailWord_8244923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244923).length < 2 ^ (prefixWord ++ tailWord_8244923).sum := by decide
  have hdescent : baseEnd_8244923 < baseStart_8244923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244954 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_8244954 : Nat := 118140960795 + 8244954 * 2 ^ 59
def prefixEnd_8244954 : Nat := 4983230072969 + 3 ^ 40 * 8244954 * 2
def baseEnd_8244954 : Nat := 4233624376210239813257153

theorem tailTrace_8244954 : CollatzResearch.WordTrace tailWord_8244954 prefixEnd_8244954 4233624376210239813257153 := by
  unfold tailWord_8244954
  simp only [CollatzResearch.WordTrace]
  refine ⟨75179544342986814720417479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200478784914631505921113277 75179544342986814720417479)
  ·
    refine ⟨112769316514480222080626219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75179544342986814720417479 112769316514480222080626219)
    ·
      refine ⟨169153974771720333120939329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112769316514480222080626219 169153974771720333120939329)
      ·
        refine ⟨126865481078790249840704497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169153974771720333120939329 126865481078790249840704497)
        ·
          refine ⟨95149110809092687380528373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126865481078790249840704497 95149110809092687380528373)
          ·
            refine ⟨8920229138352439441924535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95149110809092687380528373 8920229138352439441924535)
            ·
              refine ⟨13380343707528659162886803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920229138352439441924535 13380343707528659162886803)
              ·
                refine ⟨20070515561292988744330205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380343707528659162886803 20070515561292988744330205)
                ·
                  refine ⟨7526443335484870779123827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20070515561292988744330205 7526443335484870779123827)
                  ·
                    refine ⟨11289665003227306168685741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526443335484870779123827 11289665003227306168685741)
                    ·
                      refine ⟨4233624376210239813257153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11289665003227306168685741 4233624376210239813257153)
                      ·
                        rfl

theorem cell23_8244954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_8244954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244954 prefixEnd_8244954 := by exact prefixLift 8244954
  have htrace : WordTrace (prefixWord ++ tailWord_8244954) baseStart_8244954 baseEnd_8244954 := by
    simpa [prefixWord, tailWord_8244954, baseEnd_8244954] using wordTrace_append hprefix tailTrace_8244954
  have hstable : (prefixWord ++ tailWord_8244954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244954).length < 2 ^ (prefixWord ++ tailWord_8244954).sum := by decide
  have hdescent : baseEnd_8244954 < baseStart_8244954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244977 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_8244977 : Nat := 118140960795 + 8244977 * 2 ^ 59
def prefixEnd_8244977 : Nat := 4983230072969 + 3 ^ 40 * 8244977 * 2
def baseEnd_8244977 : Nat := 4233636186265293223269547

theorem tailTrace_8244977 : CollatzResearch.WordTrace tailWord_8244977 prefixEnd_8244977 4233636186265293223269547 := by
  unfold tailWord_8244977
  simp only [CollatzResearch.WordTrace]
  refine ⟨300719016250863933809757185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200479344167242622539838123 300719016250863933809757185)
  ·
    refine ⟨225539262188147950357317889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300719016250863933809757185 225539262188147950357317889)
    ·
      refine ⟨169154446641110962767988417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225539262188147950357317889 169154446641110962767988417)
      ·
        refine ⟨126865834980833222075991313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169154446641110962767988417 126865834980833222075991313)
        ·
          refine ⟨95149376235624916556993485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126865834980833222075991313 95149376235624916556993485)
          ·
            refine ⟨35681016088359343708872557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95149376235624916556993485 35681016088359343708872557)
            ·
              refine ⟨13380381033134753890827209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35681016088359343708872557 13380381033134753890827209)
              ·
                refine ⟨10035285774851065418120407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13380381033134753890827209 10035285774851065418120407)
                ·
                  refine ⟨15052928662276598127180611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10035285774851065418120407 15052928662276598127180611)
                  ·
                    refine ⟨22579392993414897190770917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15052928662276598127180611 22579392993414897190770917)
                    ·
                      refine ⟨4233636186265293223269547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22579392993414897190770917 4233636186265293223269547)
                      ·
                        rfl

theorem cell23_8244977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_8244977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244977 prefixEnd_8244977 := by exact prefixLift 8244977
  have htrace : WordTrace (prefixWord ++ tailWord_8244977) baseStart_8244977 baseEnd_8244977 := by
    simpa [prefixWord, tailWord_8244977, baseEnd_8244977] using wordTrace_append hprefix tailTrace_8244977
  have hstable : (prefixWord ++ tailWord_8244977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244977).length < 2 ^ (prefixWord ++ tailWord_8244977).sum := by decide
  have hdescent : baseEnd_8244977 < baseStart_8244977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8244983 : List Nat := [1, 1, 3, 1, 1, 1, 6, 9]
def baseStart_8244983 : Nat := 118140960795 + 8244983 * 2 ^ 59
def prefixEnd_8244983 : Nat := 4983230072969 + 3 ^ 40 * 8244983 * 2
def baseEnd_8244983 : Nat := 156801454338860007399797

theorem tailTrace_8244983 : CollatzResearch.WordTrace tailWord_8244983 prefixEnd_8244983 156801454338860007399797 := by
  unfold tailWord_8244983
  simp only [CollatzResearch.WordTrace]
  refine ⟨300719235088842196834475603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200479490059228131222983735 300719235088842196834475603)
  ·
    refine ⟨451078852633263295251713405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300719235088842196834475603 451078852633263295251713405)
    ·
      refine ⟨169154569737473735719392527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451078852633263295251713405 169154569737473735719392527)
      ·
        refine ⟨253731854606210603579088791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169154569737473735719392527 253731854606210603579088791)
        ·
          refine ⟨380597781909315905368633187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253731854606210603579088791 380597781909315905368633187)
          ·
            refine ⟨570896672863973858052949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380597781909315905368633187 570896672863973858052949781)
            ·
              refine ⟨26760781540498774596232021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 570896672863973858052949781 26760781540498774596232021)
              ·
                refine ⟨156801454338860007399797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26760781540498774596232021 156801454338860007399797)
                ·
                  rfl

theorem cell23_8244983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 9].length) (baseStart_8244983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8244983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8244983 prefixEnd_8244983 := by exact prefixLift 8244983
  have htrace : WordTrace (prefixWord ++ tailWord_8244983) baseStart_8244983 baseEnd_8244983 := by
    simpa [prefixWord, tailWord_8244983, baseEnd_8244983] using wordTrace_append hprefix tailTrace_8244983
  have hstable : (prefixWord ++ tailWord_8244983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8244983).length < 2 ^ (prefixWord ++ tailWord_8244983).sum := by decide
  have hdescent : baseEnd_8244983 < baseStart_8244983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8244983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_8245033 : Nat := 118140960795 + 8245033 * 2 ^ 59
def prefixEnd_8245033 : Nat := 4983230072969 + 3 ^ 40 * 8245033 * 2
def baseEnd_8245033 : Nat := 4233664941181945004169289

theorem tailTrace_8245033 : CollatzResearch.WordTrace tailWord_8245033 prefixEnd_8245033 4233664941181945004169289 := by
  unfold tailWord_8245033
  simp only [CollatzResearch.WordTrace]
  refine ⟨300721058738661055373795753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200480705825774036915863835 300721058738661055373795753)
  ·
    refine ⟨225540794053995791530346815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300721058738661055373795753 225540794053995791530346815)
    ·
      refine ⟨338311191080993687295520223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225540794053995791530346815 338311191080993687295520223)
      ·
        refine ⟨507466786621490530943280335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338311191080993687295520223 507466786621490530943280335)
        ·
          refine ⟨761200179932235796414920503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507466786621490530943280335 761200179932235796414920503)
          ·
            refine ⟨1141800269898353694622380755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761200179932235796414920503 1141800269898353694622380755)
            ·
              refine ⟨1712700404847530541933571133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141800269898353694622380755 1712700404847530541933571133)
              ·
                refine ⟨642262651817823953225089175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712700404847530541933571133 642262651817823953225089175)
                ·
                  refine ⟨963393977726735929837633763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642262651817823953225089175 963393977726735929837633763)
                  ·
                    refine ⟨1445090966590103894756450645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963393977726735929837633763 1445090966590103894756450645)
                    ·
                      refine ⟨4233664941181945004169289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1445090966590103894756450645 4233664941181945004169289)
                      ·
                        rfl

theorem cell23_8245033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_8245033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245033 prefixEnd_8245033 := by exact prefixLift 8245033
  have htrace : WordTrace (prefixWord ++ tailWord_8245033) baseStart_8245033 baseEnd_8245033 := by
    simpa [prefixWord, tailWord_8245033, baseEnd_8245033] using wordTrace_append hprefix tailTrace_8245033
  have hstable : (prefixWord ++ tailWord_8245033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245033).length < 2 ^ (prefixWord ++ tailWord_8245033).sum := by decide
  have hdescent : baseEnd_8245033 < baseStart_8245033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
