import V185TrunkScan23Chunk0858

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5083717 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_5083717 : Nat := 118140960795 + 5083717 * 2 ^ 59
def prefixEnd_5083717 : Nat := 4983230072969 + 3 ^ 40 * 5083717 * 2
def baseEnd_5083717 : Nat := 2610390332432991667557917

theorem tailTrace_5083717 : CollatzResearch.WordTrace tailWord_5083717 prefixEnd_5083717 2610390332432991667557917 := by
  unfold tailWord_5083717
  simp only [CollatzResearch.WordTrace]
  refine ⟨185418391723569013585409405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123612261149046009056939603 185418391723569013585409405)
  ·
    refine ⟨69531896896338380094528527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185418391723569013585409405 69531896896338380094528527)
    ·
      refine ⟨104297845344507570141792791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69531896896338380094528527 104297845344507570141792791)
      ·
        refine ⟨156446768016761355212689187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104297845344507570141792791 156446768016761355212689187)
        ·
          refine ⟨234670152025142032819033781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156446768016761355212689187 234670152025142032819033781)
          ·
            refine ⟨22000326752357065576784417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234670152025142032819033781 22000326752357065576784417)
            ·
              refine ⟨16500245064267799182588313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22000326752357065576784417 16500245064267799182588313)
              ·
                refine ⟨12375183798200849386941235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16500245064267799182588313 12375183798200849386941235)
                ·
                  refine ⟨18562775697301274080411853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12375183798200849386941235 18562775697301274080411853)
                  ·
                    refine ⟨6961040886487977780154445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18562775697301274080411853 6961040886487977780154445)
                    ·
                      refine ⟨2610390332432991667557917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961040886487977780154445 2610390332432991667557917)
                      ·
                        rfl

theorem cell23_5083717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_5083717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083717 prefixEnd_5083717 := by exact prefixLift 5083717
  have htrace : WordTrace (prefixWord ++ tailWord_5083717) baseStart_5083717 baseEnd_5083717 := by
    simpa [prefixWord, tailWord_5083717, baseEnd_5083717] using wordTrace_append hprefix tailTrace_5083717
  have hstable : (prefixWord ++ tailWord_5083717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083717).length < 2 ^ (prefixWord ++ tailWord_5083717).sum := by decide
  have hdescent : baseEnd_5083717 < baseStart_5083717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083718 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5083718 : Nat := 118140960795 + 5083718 * 2 ^ 59
def prefixEnd_5083718 : Nat := 4983230072969 + 3 ^ 40 * 5083718 * 2
def baseEnd_5083718 : Nat := 2610390845913646163645413

theorem tailTrace_5083718 : CollatzResearch.WordTrace tailWord_5083718 prefixEnd_5083718 2610390845913646163645413 := by
  unfold tailWord_5083718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794325881142668461131119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123612285464376927170797205 5794325881142668461131119)
  ·
    refine ⟨8691488821714002691696679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5794325881142668461131119 8691488821714002691696679)
    ·
      refine ⟨13037233232571004037545019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8691488821714002691696679 13037233232571004037545019)
      ·
        refine ⟨19555849848856506056317529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13037233232571004037545019 19555849848856506056317529)
        ·
          refine ⟨14666887386642379542238147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555849848856506056317529 14666887386642379542238147)
          ·
            refine ⟨22000331079963569313357221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14666887386642379542238147 22000331079963569313357221)
            ·
              refine ⟨4125062077493169246254479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22000331079963569313357221 4125062077493169246254479)
              ·
                refine ⟨6187593116239753869381719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125062077493169246254479 6187593116239753869381719)
                ·
                  refine ⟨9281389674359630804072579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6187593116239753869381719 9281389674359630804072579)
                  ·
                    refine ⟨13922084511539446206108869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9281389674359630804072579 13922084511539446206108869)
                    ·
                      refine ⟨2610390845913646163645413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13922084511539446206108869 2610390845913646163645413)
                      ·
                        rfl

theorem cell23_5083718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5083718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083718 prefixEnd_5083718 := by exact prefixLift 5083718
  have htrace : WordTrace (prefixWord ++ tailWord_5083718) baseStart_5083718 baseEnd_5083718 := by
    simpa [prefixWord, tailWord_5083718, baseEnd_5083718] using wordTrace_append hprefix tailTrace_5083718
  have hstable : (prefixWord ++ tailWord_5083718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083718).length < 2 ^ (prefixWord ++ tailWord_5083718).sum := by decide
  have hdescent : baseEnd_5083718 < baseStart_5083718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083777 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5083777 : Nat := 118140960795 + 5083777 * 2 ^ 59
def prefixEnd_5083777 : Nat := 4983230072969 + 3 ^ 40 * 5083777 * 2
def baseEnd_5083777 : Nat := 2610421141272261432807641

theorem tailTrace_5083777 : CollatzResearch.WordTrace tailWord_5083777 prefixEnd_5083777 2610421141272261432807641 := by
  unfold tailWord_5083777
  simp only [CollatzResearch.WordTrace]
  refine ⟨185420580103351643832593585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123613720068901095888395723 185420580103351643832593585)
  ·
    refine ⟨139065435077513732874445189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185420580103351643832593585 139065435077513732874445189)
    ·
      refine ⟨26074769077033824913958473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139065435077513732874445189 26074769077033824913958473)
      ·
        refine ⟨19556076807775368685468855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26074769077033824913958473 19556076807775368685468855)
        ·
          refine ⟨29334115211663053028203283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19556076807775368685468855 29334115211663053028203283)
          ·
            refine ⟨44001172817494579542304925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29334115211663053028203283 44001172817494579542304925)
            ·
              refine ⟨16500439806560467328364347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44001172817494579542304925 16500439806560467328364347)
              ·
                refine ⟨24750659709840700992546521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16500439806560467328364347 24750659709840700992546521)
                ·
                  refine ⟨18562994782380525744409891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24750659709840700992546521 18562994782380525744409891)
                  ·
                    refine ⟨27844492173570788616614837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18562994782380525744409891 27844492173570788616614837)
                    ·
                      refine ⟨2610421141272261432807641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27844492173570788616614837 2610421141272261432807641)
                      ·
                        rfl

theorem cell23_5083777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5083777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083777 prefixEnd_5083777 := by exact prefixLift 5083777
  have htrace : WordTrace (prefixWord ++ tailWord_5083777) baseStart_5083777 baseEnd_5083777 := by
    simpa [prefixWord, tailWord_5083777, baseEnd_5083777] using wordTrace_append hprefix tailTrace_5083777
  have hstable : (prefixWord ++ tailWord_5083777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083777).length < 2 ^ (prefixWord ++ tailWord_5083777).sum := by decide
  have hdescent : baseEnd_5083777 < baseStart_5083777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083802 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5083802 : Nat := 118140960795 + 5083802 * 2 ^ 59
def prefixEnd_5083802 : Nat := 4983230072969 + 3 ^ 40 * 5083802 * 2
def baseEnd_5083802 : Nat := 2610433978288623834995027

theorem tailTrace_5083802 : CollatzResearch.WordTrace tailWord_5083802 prefixEnd_5083802 2610433978288623834995027 := by
  unfold tailWord_5083802
  simp only [CollatzResearch.WordTrace]
  refine ⟨46355372982065268275563415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123614327952174048734835773 46355372982065268275563415)
  ·
    refine ⟨69533059473097902413345123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46355372982065268275563415 69533059473097902413345123)
    ·
      refine ⟨104299589209646853620017685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69533059473097902413345123 104299589209646853620017685)
      ·
        refine ⟨4889043244202196263438329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104299589209646853620017685 4889043244202196263438329)
        ·
          refine ⟨3666782433151647197578747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889043244202196263438329 3666782433151647197578747)
          ·
            refine ⟨5500173649727470796368121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666782433151647197578747 5500173649727470796368121)
            ·
              refine ⟨4125130237295603097276091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500173649727470796368121 4125130237295603097276091)
              ·
                refine ⟨6187695355943404645914137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125130237295603097276091 6187695355943404645914137)
                ·
                  refine ⟨4640771516957553484435603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6187695355943404645914137 4640771516957553484435603)
                  ·
                    refine ⟨6961157275436330226653405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640771516957553484435603 6961157275436330226653405)
                    ·
                      refine ⟨2610433978288623834995027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961157275436330226653405 2610433978288623834995027)
                      ·
                        rfl

theorem cell23_5083802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5083802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083802 prefixEnd_5083802 := by exact prefixLift 5083802
  have htrace : WordTrace (prefixWord ++ tailWord_5083802) baseStart_5083802 baseEnd_5083802 := by
    simpa [prefixWord, tailWord_5083802, baseEnd_5083802] using wordTrace_append hprefix tailTrace_5083802
  have hstable : (prefixWord ++ tailWord_5083802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083802).length < 2 ^ (prefixWord ++ tailWord_5083802).sum := by decide
  have hdescent : baseEnd_5083802 < baseStart_5083802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083808 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2]
def baseStart_5083808 : Nat := 118140960795 + 5083808 * 2 ^ 59
def prefixEnd_5083808 : Nat := 4983230072969 + 3 ^ 40 * 5083808 * 2
def baseEnd_5083808 : Nat := 2610437059172550811519999

theorem tailTrace_5083808 : CollatzResearch.WordTrace tailWord_5083808 prefixEnd_5083808 2610437059172550811519999 := by
  unfold tailWord_5083808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92710855383119668063486039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123614473844159557417981385 92710855383119668063486039)
  ·
    refine ⟨139066283074679502095229059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92710855383119668063486039 139066283074679502095229059)
    ·
      refine ⟨208599424612019253142843589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139066283074679502095229059 208599424612019253142843589)
      ·
        refine ⟨39112392114753609964283173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208599424612019253142843589 39112392114753609964283173)
        ·
          refine ⟨7333573521516301868303095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39112392114753609964283173 7333573521516301868303095)
          ·
            refine ⟨11000360282274452802454643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7333573521516301868303095 11000360282274452802454643)
            ·
              refine ⟨16500540423411679203681965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11000360282274452802454643 16500540423411679203681965)
              ·
                refine ⟨6187702658779379701380737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16500540423411679203681965 6187702658779379701380737)
                ·
                  refine ⟨4640776994084534776035553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6187702658779379701380737 4640776994084534776035553)
                  ·
                    refine ⟨3480582745563401082026665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4640776994084534776035553 3480582745563401082026665)
                    ·
                      refine ⟨2610437059172550811519999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480582745563401082026665 2610437059172550811519999)
                      ·
                        rfl

theorem cell23_5083808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_5083808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083808 prefixEnd_5083808 := by exact prefixLift 5083808
  have htrace : WordTrace (prefixWord ++ tailWord_5083808) baseStart_5083808 baseEnd_5083808 := by
    simpa [prefixWord, tailWord_5083808, baseEnd_5083808] using wordTrace_append hprefix tailTrace_5083808
  have hstable : (prefixWord ++ tailWord_5083808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083808).length < 2 ^ (prefixWord ++ tailWord_5083808).sum := by decide
  have hdescent : baseEnd_5083808 < baseStart_5083808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083827 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 2, 5]
def baseStart_5083827 : Nat := 118140960795 + 5083827 * 2 ^ 59
def prefixEnd_5083827 : Nat := 4983230072969 + 3 ^ 40 * 5083827 * 2
def baseEnd_5083827 : Nat := 870148938434995412394137

theorem tailTrace_5083827 : CollatzResearch.WordTrace tailWord_5083827 prefixEnd_5083827 870148938434995412394137 := by
  unfold tailWord_5083827
  simp only [CollatzResearch.WordTrace]
  refine ⟨185422403753170502371913735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123614935835447001581275823 185422403753170502371913735)
  ·
    refine ⟨278133605629755753557870603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185422403753170502371913735 278133605629755753557870603)
    ·
      refine ⟨417200408444633630336805905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278133605629755753557870603 417200408444633630336805905)
      ·
        refine ⟨312900306333475222752604429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417200408444633630336805905 312900306333475222752604429)
        ·
          refine ⟨117337614875053208532226661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312900306333475222752604429 117337614875053208532226661)
          ·
            refine ⟨22000802789072476599792499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117337614875053208532226661 22000802789072476599792499)
            ·
              refine ⟨33001204183608714899688749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22000802789072476599792499 33001204183608714899688749)
              ·
                refine ⟨12375451568853268087383281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33001204183608714899688749 12375451568853268087383281)
                ·
                  refine ⟨9281588676639951065537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375451568853268087383281 9281588676639951065537461)
                  ·
                    refine ⟨870148938434995412394137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9281588676639951065537461 870148938434995412394137)
                    ·
                      rfl

theorem cell23_5083827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].length) (baseStart_5083827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083827 prefixEnd_5083827 := by exact prefixLift 5083827
  have htrace : WordTrace (prefixWord ++ tailWord_5083827) baseStart_5083827 baseEnd_5083827 := by
    simpa [prefixWord, tailWord_5083827, baseEnd_5083827] using wordTrace_append hprefix tailTrace_5083827
  have hstable : (prefixWord ++ tailWord_5083827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083827).length < 2 ^ (prefixWord ++ tailWord_5083827).sum := by decide
  have hdescent : baseEnd_5083827 < baseStart_5083827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083837 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5083837 : Nat := 118140960795 + 5083837 * 2 ^ 59
def prefixEnd_5083837 : Nat := 4983230072969 + 3 ^ 40 * 5083837 * 2
def baseEnd_5083837 : Nat := 2610451950111531198057365

theorem tailTrace_5083837 : CollatzResearch.WordTrace tailWord_5083837 prefixEnd_5083837 2610451950111531198057365 := by
  unfold tailWord_5083837
  simp only [CollatzResearch.WordTrace]
  refine ⟨185422768483134274079777765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123615178988756182719851843 185422768483134274079777765)
  ·
    refine ⟨34766769090587676389958331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185422768483134274079777765 34766769090587676389958331)
    ·
      refine ⟨52150153635881514584937497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34766769090587676389958331 52150153635881514584937497)
      ·
        refine ⟨39112615226911135938703123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52150153635881514584937497 39112615226911135938703123)
        ·
          refine ⟨58668922840366703908054685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39112615226911135938703123 58668922840366703908054685)
          ·
            refine ⟨22000846065137513965520507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58668922840366703908054685 22000846065137513965520507)
            ·
              refine ⟨33001269097706270948280761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22000846065137513965520507 33001269097706270948280761)
              ·
                refine ⟨24750951823279703211210571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33001269097706270948280761 24750951823279703211210571)
                ·
                  refine ⟨37126427734919554816815857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24750951823279703211210571 37126427734919554816815857)
                  ·
                    refine ⟨27844820801189666112611893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37126427734919554816815857 27844820801189666112611893)
                    ·
                      refine ⟨2610451950111531198057365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27844820801189666112611893 2610451950111531198057365)
                      ·
                        rfl

theorem cell23_5083837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5083837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083837 prefixEnd_5083837 := by exact prefixLift 5083837
  have htrace : WordTrace (prefixWord ++ tailWord_5083837) baseStart_5083837 baseEnd_5083837 := by
    simpa [prefixWord, tailWord_5083837, baseEnd_5083837] using wordTrace_append hprefix tailTrace_5083837
  have hstable : (prefixWord ++ tailWord_5083837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083837).length < 2 ^ (prefixWord ++ tailWord_5083837).sum := by decide
  have hdescent : baseEnd_5083837 < baseStart_5083837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083844 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5083844 : Nat := 118140960795 + 5083844 * 2 ^ 59
def prefixEnd_5083844 : Nat := 4983230072969 + 3 ^ 40 * 5083844 * 2
def baseEnd_5083844 : Nat := 870151848158704223556611

theorem tailTrace_5083844 : CollatzResearch.WordTrace tailWord_5083844 prefixEnd_5083844 870151848158704223556611 := by
  unfold tailWord_5083844
  simp only [CollatzResearch.WordTrace]
  refine ⟨92711511897054457137641293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123615349196072609516855057 92711511897054457137641293)
  ·
    refine ⟨34766816961395421426615485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92711511897054457137641293 34766816961395421426615485)
    ·
      refine ⟨13037556360523283034980807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34766816961395421426615485 13037556360523283034980807)
      ·
        refine ⟨19556334540784924552471211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13037556360523283034980807 19556334540784924552471211)
        ·
          refine ⟨29334501811177386828706817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19556334540784924552471211 29334501811177386828706817)
          ·
            refine ⟨22000876358383040121530113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29334501811177386828706817 22000876358383040121530113)
            ·
              refine ⟨16500657268787280091147585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22000876358383040121530113 16500657268787280091147585)
              ·
                refine ⟨12375492951590460068360689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16500657268787280091147585 12375492951590460068360689)
                ·
                  refine ⟨9281619713692845051270517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375492951590460068360689 9281619713692845051270517)
                  ·
                    refine ⟨870151848158704223556611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9281619713692845051270517 870151848158704223556611)
                    ·
                      rfl

theorem cell23_5083844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5083844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083844 prefixEnd_5083844 := by exact prefixLift 5083844
  have htrace : WordTrace (prefixWord ++ tailWord_5083844) baseStart_5083844 baseEnd_5083844 := by
    simpa [prefixWord, tailWord_5083844, baseEnd_5083844] using wordTrace_append hprefix tailTrace_5083844
  have hstable : (prefixWord ++ tailWord_5083844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083844).length < 2 ^ (prefixWord ++ tailWord_5083844).sum := by decide
  have hdescent : baseEnd_5083844 < baseStart_5083844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083847 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_5083847 : Nat := 118140960795 + 5083847 * 2 ^ 59
def prefixEnd_5083847 : Nat := 4983230072969 + 3 ^ 40 * 5083847 * 2
def baseEnd_5083847 : Nat := 2610457084918076158932319

theorem tailTrace_5083847 : CollatzResearch.WordTrace tailWord_5083847 prefixEnd_5083847 2610457084918076158932319 := by
  unfold tailWord_5083847
  simp only [CollatzResearch.WordTrace]
  refine ⟨185423133213098045787641795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123615422142065363858427863 185423133213098045787641795)
  ·
    refine ⟨278134699819647068681462693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185423133213098045787641795 278134699819647068681462693)
    ·
      refine ⟨52150256216183825377774255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278134699819647068681462693 52150256216183825377774255)
      ·
        refine ⟨78225384324275738066661383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52150256216183825377774255 78225384324275738066661383)
        ·
          refine ⟨117338076486413607099992075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78225384324275738066661383 117338076486413607099992075)
          ·
            refine ⟨176007114729620410649988113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117338076486413607099992075 176007114729620410649988113)
            ·
              refine ⟨132005336047215307987491085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176007114729620410649988113 132005336047215307987491085)
              ·
                refine ⟨49502001017705740495309157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132005336047215307987491085 49502001017705740495309157)
                ·
                  refine ⟨9281625190819826342870467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49502001017705740495309157 9281625190819826342870467)
                  ·
                    refine ⟨13922437786229739514305701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9281625190819826342870467 13922437786229739514305701)
                    ·
                      refine ⟨2610457084918076158932319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13922437786229739514305701 2610457084918076158932319)
                      ·
                        rfl

theorem cell23_5083847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_5083847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083847 prefixEnd_5083847 := by exact prefixLift 5083847
  have htrace : WordTrace (prefixWord ++ tailWord_5083847) baseStart_5083847 baseEnd_5083847 := by
    simpa [prefixWord, tailWord_5083847, baseEnd_5083847] using wordTrace_append hprefix tailTrace_5083847
  have hstable : (prefixWord ++ tailWord_5083847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083847).length < 2 ^ (prefixWord ++ tailWord_5083847).sum := by decide
  have hdescent : baseEnd_5083847 < baseStart_5083847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083864 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_5083864 : Nat := 118140960795 + 5083864 * 2 ^ 59
def prefixEnd_5083864 : Nat := 4983230072969 + 3 ^ 40 * 5083864 * 2
def baseEnd_5083864 : Nat := 2610465814089202592419741

theorem tailTrace_5083864 : CollatzResearch.WordTrace tailWord_5083864 prefixEnd_5083864 2610465814089202592419741 := by
  unfold tailWord_5083864
  simp only [CollatzResearch.WordTrace]
  refine ⟨92711876627018228845505323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123615835502690971794007097 92711876627018228845505323)
  ·
    refine ⟨139067814940527343268257985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92711876627018228845505323 139067814940527343268257985)
    ·
      refine ⟨104300861205395507451193489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139067814940527343268257985 104300861205395507451193489)
      ·
        refine ⟨78225645904046630588395117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104300861205395507451193489 78225645904046630588395117)
        ·
          refine ⟨29334617214017486470648169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78225645904046630588395117 29334617214017486470648169)
          ·
            refine ⟨22000962910513114852986127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29334617214017486470648169 22000962910513114852986127)
            ·
              refine ⟨33001444365769672279479191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22000962910513114852986127 33001444365769672279479191)
              ·
                refine ⟨49502166548654508419218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33001444365769672279479191 49502166548654508419218787)
                ·
                  refine ⟨74253249822981762628828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49502166548654508419218787 74253249822981762628828181)
                  ·
                    refine ⟨3480621085452270123226321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74253249822981762628828181 3480621085452270123226321)
                    ·
                      refine ⟨2610465814089202592419741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480621085452270123226321 2610465814089202592419741)
                      ·
                        rfl

theorem cell23_5083864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_5083864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083864 prefixEnd_5083864 := by exact prefixLift 5083864
  have htrace : WordTrace (prefixWord ++ tailWord_5083864) baseStart_5083864 baseEnd_5083864 := by
    simpa [prefixWord, tailWord_5083864, baseEnd_5083864] using wordTrace_append hprefix tailTrace_5083864
  have hstable : (prefixWord ++ tailWord_5083864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083864).length < 2 ^ (prefixWord ++ tailWord_5083864).sum := by decide
  have hdescent : baseEnd_5083864 < baseStart_5083864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083897 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_5083897 : Nat := 118140960795 + 5083897 * 2 ^ 59
def prefixEnd_5083897 : Nat := 4983230072969 + 3 ^ 40 * 5083897 * 2
def baseEnd_5083897 : Nat := 2610482758950800963307089

theorem tailTrace_5083897 : CollatzResearch.WordTrace tailWord_5083897 prefixEnd_5083897 2610482758950800963307089 := by
  unfold tailWord_5083897
  simp only [CollatzResearch.WordTrace]
  refine ⟨185424956862916904326961945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123616637908611269551307963 185424956862916904326961945)
  ·
    refine ⟨139068717647187678245221459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185424956862916904326961945 139068717647187678245221459)
    ·
      refine ⟨208603076470781517367832189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139068717647187678245221459 208603076470781517367832189)
      ·
        refine ⟨78226153676543069012937071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208603076470781517367832189 78226153676543069012937071)
        ·
          refine ⟨117339230514814603519405607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78226153676543069012937071 117339230514814603519405607)
          ·
            refine ⟨176008845772221905279108411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117339230514814603519405607 176008845772221905279108411)
            ·
              refine ⟨264013268658332857918662617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176008845772221905279108411 264013268658332857918662617)
              ·
                refine ⟨198009951493749643438996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264013268658332857918662617 198009951493749643438996963)
                ·
                  refine ⟨297014927240624465158495445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198009951493749643438996963 297014927240624465158495445)
                  ·
                    refine ⟨6961287357202135902152237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 297014927240624465158495445 6961287357202135902152237)
                    ·
                      refine ⟨2610482758950800963307089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961287357202135902152237 2610482758950800963307089)
                      ·
                        rfl

theorem cell23_5083897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_5083897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083897 prefixEnd_5083897 := by exact prefixLift 5083897
  have htrace : WordTrace (prefixWord ++ tailWord_5083897) baseStart_5083897 baseEnd_5083897 := by
    simpa [prefixWord, tailWord_5083897, baseEnd_5083897] using wordTrace_append hprefix tailTrace_5083897
  have hstable : (prefixWord ++ tailWord_5083897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083897).length < 2 ^ (prefixWord ++ tailWord_5083897).sum := by decide
  have hdescent : baseEnd_5083897 < baseStart_5083897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083941 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_5083941 : Nat := 118140960795 + 5083941 * 2 ^ 59
def prefixEnd_5083941 : Nat := 4983230072969 + 3 ^ 40 * 5083941 * 2
def baseEnd_5083941 : Nat := 2610505352099598791156887

theorem tailTrace_5083941 : CollatzResearch.WordTrace tailWord_5083941 prefixEnd_5083941 2610505352099598791156887 := by
  unfold tailWord_5083941
  simp only [CollatzResearch.WordTrace]
  refine ⟨185426561674757499841563677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123617707783171666561042451 185426561674757499841563677)
  ·
    refine ⟨69534960628034062440586379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185426561674757499841563677 69534960628034062440586379)
    ·
      refine ⟨104302440942051093660879569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69534960628034062440586379 104302440942051093660879569)
      ·
        refine ⟨78226830706538320245659677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104302440942051093660879569 78226830706538320245659677)
        ·
          refine ⟨29335061514951870092122379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78226830706538320245659677 29335061514951870092122379)
          ·
            refine ⟨44002592272427805138183569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29335061514951870092122379 44002592272427805138183569)
            ·
              refine ⟨33001944204320853853637677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44002592272427805138183569 33001944204320853853637677)
              ·
                refine ⟨12375729076620320195114129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33001944204320853853637677 12375729076620320195114129)
                ·
                  refine ⟨9281796807465240146335597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375729076620320195114129 9281796807465240146335597)
                  ·
                    refine ⟨3480673802799465054875849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9281796807465240146335597 3480673802799465054875849)
                    ·
                      refine ⟨2610505352099598791156887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480673802799465054875849 2610505352099598791156887)
                      ·
                        rfl

theorem cell23_5083941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_5083941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083941 prefixEnd_5083941 := by exact prefixLift 5083941
  have htrace : WordTrace (prefixWord ++ tailWord_5083941) baseStart_5083941 baseEnd_5083941 := by
    simpa [prefixWord, tailWord_5083941, baseEnd_5083941] using wordTrace_append hprefix tailTrace_5083941
  have hstable : (prefixWord ++ tailWord_5083941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083941).length < 2 ^ (prefixWord ++ tailWord_5083941).sum := by decide
  have hdescent : baseEnd_5083941 < baseStart_5083941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083965 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5083965 : Nat := 118140960795 + 5083965 * 2 ^ 59
def prefixEnd_5083965 : Nat := 4983230072969 + 3 ^ 40 * 5083965 * 2
def baseEnd_5083965 : Nat := 2610517675635306697256777

theorem tailTrace_5083965 : CollatzResearch.WordTrace tailWord_5083965 prefixEnd_5083965 2610517675635306697256777 := by
  unfold tailWord_5083965
  simp only [CollatzResearch.WordTrace]
  refine ⟨185427437026670551940437349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123618291351113701293624899 185427437026670551940437349)
  ·
    refine ⟨34767644442500728488832003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185427437026670551940437349 34767644442500728488832003)
    ·
      refine ⟨52151466663751092733248005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34767644442500728488832003 52151466663751092733248005)
      ·
        refine ⟨9778399999453329887484001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52151466663751092733248005 9778399999453329887484001)
        ·
          refine ⟨7333799999589997415613001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9778399999453329887484001 7333799999589997415613001)
          ·
            refine ⟨5500349999692498061709751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333799999589997415613001 5500349999692498061709751)
            ·
              refine ⟨8250524999538747092564627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500349999692498061709751 8250524999538747092564627)
              ·
                refine ⟨12375787499308120638846941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250524999538747092564627 12375787499308120638846941)
                ·
                  refine ⟨4640920312240545239567603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12375787499308120638846941 4640920312240545239567603)
                  ·
                    refine ⟨6961380468360817859351405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640920312240545239567603 6961380468360817859351405)
                    ·
                      refine ⟨2610517675635306697256777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961380468360817859351405 2610517675635306697256777)
                      ·
                        rfl

theorem cell23_5083965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5083965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083965 prefixEnd_5083965 := by exact prefixLift 5083965
  have htrace : WordTrace (prefixWord ++ tailWord_5083965) baseStart_5083965 baseEnd_5083965 := by
    simpa [prefixWord, tailWord_5083965, baseEnd_5083965] using wordTrace_append hprefix tailTrace_5083965
  have hstable : (prefixWord ++ tailWord_5083965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083965).length < 2 ^ (prefixWord ++ tailWord_5083965).sum := by decide
  have hdescent : baseEnd_5083965 < baseStart_5083965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083972 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 6]
def baseStart_5083972 : Nat := 118140960795 + 5083972 * 2 ^ 59
def prefixEnd_5083972 : Nat := 4983230072969 + 3 ^ 40 * 5083972 * 2
def baseEnd_5083972 : Nat := 290057918888876463318805

theorem tailTrace_5083972 : CollatzResearch.WordTrace tailWord_5083972 prefixEnd_5083972 290057918888876463318805 := by
  unfold tailWord_5083972
  simp only [CollatzResearch.WordTrace]
  refine ⟨92713846168822596067971085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123618461558430128090628113 92713846168822596067971085)
  ·
    refine ⟨34767692313308473525489157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92713846168822596067971085 34767692313308473525489157)
    ·
      refine ⟨6518942308745338786029217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34767692313308473525489157 6518942308745338786029217)
      ·
        refine ⟨4889206731559004089521913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518942308745338786029217 4889206731559004089521913)
        ·
          refine ⟨3666905048669253067141435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889206731559004089521913 3666905048669253067141435)
          ·
            refine ⟨5500357573003879600712153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666905048669253067141435 5500357573003879600712153)
            ·
              refine ⟨4125268179752909700534115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500357573003879600712153 4125268179752909700534115)
              ·
                refine ⟨6187902269629364550801173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125268179752909700534115 6187902269629364550801173)
                ·
                  refine ⟨290057918888876463318805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6187902269629364550801173 290057918888876463318805)
                  ·
                    rfl

theorem cell23_5083972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_5083972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083972 prefixEnd_5083972 := by exact prefixLift 5083972
  have htrace : WordTrace (prefixWord ++ tailWord_5083972) baseStart_5083972 baseEnd_5083972 := by
    simpa [prefixWord, tailWord_5083972, baseEnd_5083972] using wordTrace_append hprefix tailTrace_5083972
  have hstable : (prefixWord ++ tailWord_5083972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083972).length < 2 ^ (prefixWord ++ tailWord_5083972).sum := by decide
  have hdescent : baseEnd_5083972 < baseStart_5083972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083977 : List Nat := [1, 2, 1, 1, 2, 5, 1, 10]
def baseStart_5083977 : Nat := 118140960795 + 5083977 * 2 ^ 59
def prefixEnd_5083977 : Nat := 4983230072969 + 3 ^ 40 * 5083977 * 2
def baseEnd_5083977 : Nat := 96686068051968912974323

theorem tailTrace_5083977 : CollatzResearch.WordTrace tailWord_5083977 prefixEnd_5083977 96686068051968912974323 := by
  unfold tailWord_5083977
  simp only [CollatzResearch.WordTrace]
  refine ⟨185427874702627077989874185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123618583135084718659916123 185427874702627077989874185)
  ·
    refine ⟨139070906026970308492405639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185427874702627077989874185 139070906026970308492405639)
    ·
      refine ⟨208606359040455462738608459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139070906026970308492405639 208606359040455462738608459)
      ·
        refine ⟨312909538560683194107912689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208606359040455462738608459 312909538560683194107912689)
        ·
          refine ⟨234682153920512395580934517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312909538560683194107912689 234682153920512395580934517)
          ·
            refine ⟨22001451930048037085712611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234682153920512395580934517 22001451930048037085712611)
            ·
              refine ⟨33002177895072055628568917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22001451930048037085712611 33002177895072055628568917)
              ·
                refine ⟨96686068051968912974323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33002177895072055628568917 96686068051968912974323)
                ·
                  rfl

theorem cell23_5083977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 10].length) (baseStart_5083977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083977 prefixEnd_5083977 := by exact prefixLift 5083977
  have htrace : WordTrace (prefixWord ++ tailWord_5083977) baseStart_5083977 baseEnd_5083977 := by
    simpa [prefixWord, tailWord_5083977, baseEnd_5083977] using wordTrace_append hprefix tailTrace_5083977
  have hstable : (prefixWord ++ tailWord_5083977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083977).length < 2 ^ (prefixWord ++ tailWord_5083977).sum := by decide
  have hdescent : baseEnd_5083977 < baseStart_5083977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083991 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_5083991 : Nat := 118140960795 + 5083991 * 2 ^ 59
def prefixEnd_5083991 : Nat := 4983230072969 + 3 ^ 40 * 5083991 * 2
def baseEnd_5083991 : Nat := 2610531026132323595531657

theorem tailTrace_5083991 : CollatzResearch.WordTrace tailWord_5083991 prefixEnd_5083991 2610531026132323595531657 := by
  unfold tailWord_5083991
  simp only [CollatzResearch.WordTrace]
  refine ⟨185428385324576358380883827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123618923549717572253922551 185428385324576358380883827)
  ·
    refine ⟨278142577986864537571325741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185428385324576358380883827 278142577986864537571325741)
    ·
      refine ⟨104303466745074201589247153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278142577986864537571325741 104303466745074201589247153)
      ·
        refine ⟨78227600058805651191935365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104303466745074201589247153 78227600058805651191935365)
        ·
          refine ⟨14667675011026059598487881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78227600058805651191935365 14667675011026059598487881)
          ·
            refine ⟨11000756258269544698865911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14667675011026059598487881 11000756258269544698865911)
            ·
              refine ⟨16501134387404317048298867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11000756258269544698865911 16501134387404317048298867)
              ·
                refine ⟨24751701581106475572448301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16501134387404317048298867 24751701581106475572448301)
                ·
                  refine ⟨9281888092914928339668113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24751701581106475572448301 9281888092914928339668113)
                  ·
                    refine ⟨6961416069686196254751085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9281888092914928339668113 6961416069686196254751085)
                    ·
                      refine ⟨2610531026132323595531657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961416069686196254751085 2610531026132323595531657)
                      ·
                        rfl

theorem cell23_5083991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_5083991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083991 prefixEnd_5083991 := by exact prefixLift 5083991
  have htrace : WordTrace (prefixWord ++ tailWord_5083991) baseStart_5083991 baseEnd_5083991 := by
    simpa [prefixWord, tailWord_5083991, baseEnd_5083991] using wordTrace_append hprefix tailTrace_5083991
  have hstable : (prefixWord ++ tailWord_5083991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083991).length < 2 ^ (prefixWord ++ tailWord_5083991).sum := by decide
  have hdescent : baseEnd_5083991 < baseStart_5083991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084031 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 3, 3, 2]
def baseStart_5084031 : Nat := 118140960795 + 5084031 * 2 ^ 59
def prefixEnd_5084031 : Nat := 4983230072969 + 3 ^ 40 * 5084031 * 2
def baseEnd_5084031 : Nat := 2610551565358503439031473

theorem tailTrace_5084031 : CollatzResearch.WordTrace tailWord_5084031 prefixEnd_5084031 2610551565358503439031473 := by
  unfold tailWord_5084031
  simp only [CollatzResearch.WordTrace]
  refine ⟨185429844244431445212339947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123619896162954296808226631 185429844244431445212339947)
  ·
    refine ⟨278144766366647167818509921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185429844244431445212339947 278144766366647167818509921)
    ·
      refine ⟨208608574774985375863882441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278144766366647167818509921 208608574774985375863882441)
      ·
        refine ⟨156456431081239031897911831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208608574774985375863882441 156456431081239031897911831)
        ·
          refine ⟨234684646621858547846867747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156456431081239031897911831 234684646621858547846867747)
          ·
            refine ⟨352026969932787821770301621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234684646621858547846867747 352026969932787821770301621)
            ·
              refine ⟨33002528431198858290965777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352026969932787821770301621 33002528431198858290965777)
              ·
                refine ⟨24751896323399143718224333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33002528431198858290965777 24751896323399143718224333)
                ·
                  refine ⟨9281961121274678894334125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24751896323399143718224333 9281961121274678894334125)
                  ·
                    refine ⟨3480735420478004585375297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9281961121274678894334125 3480735420478004585375297)
                    ·
                      refine ⟨2610551565358503439031473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480735420478004585375297 2610551565358503439031473)
                      ·
                        rfl

theorem cell23_5084031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_5084031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084031 prefixEnd_5084031 := by exact prefixLift 5084031
  have htrace : WordTrace (prefixWord ++ tailWord_5084031) baseStart_5084031 baseEnd_5084031 := by
    simpa [prefixWord, tailWord_5084031, baseEnd_5084031] using wordTrace_append hprefix tailTrace_5084031
  have hstable : (prefixWord ++ tailWord_5084031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084031).length < 2 ^ (prefixWord ++ tailWord_5084031).sum := by decide
  have hdescent : baseEnd_5084031 < baseStart_5084031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084064 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5084064 : Nat := 118140960795 + 5084064 * 2 ^ 59
def prefixEnd_5084064 : Nat := 4983230072969 + 3 ^ 40 * 5084064 * 2
def baseEnd_5084064 : Nat := 2610568510220101809918821

theorem tailTrace_5084064 : CollatzResearch.WordTrace tailWord_5084064 prefixEnd_5084064 2610568510220101809918821 := by
  unfold tailWord_5084064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92715523926655945924145623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123620698568874594565527497 92715523926655945924145623)
  ·
    refine ⟨139073285889983918886218435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92715523926655945924145623 139073285889983918886218435)
    ·
      refine ⟨208609928834975878329327653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139073285889983918886218435 208609928834975878329327653)
      ·
        refine ⟨39114361656557977186748935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208609928834975878329327653 39114361656557977186748935)
        ·
          refine ⟨58671542484836965780123403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39114361656557977186748935 58671542484836965780123403)
          ·
            refine ⟨88007313727255448670185105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58671542484836965780123403 88007313727255448670185105)
            ·
              refine ⟨66005485295441586502638829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88007313727255448670185105 66005485295441586502638829)
              ·
                refine ⟨24752056985790594938489561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66005485295441586502638829 24752056985790594938489561)
                ·
                  refine ⟨18564042739342946203867171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24752056985790594938489561 18564042739342946203867171)
                  ·
                    refine ⟨27846064109014419305800757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18564042739342946203867171 27846064109014419305800757)
                    ·
                      refine ⟨2610568510220101809918821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27846064109014419305800757 2610568510220101809918821)
                      ·
                        rfl

theorem cell23_5084064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5084064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084064 prefixEnd_5084064 := by exact prefixLift 5084064
  have htrace : WordTrace (prefixWord ++ tailWord_5084064) baseStart_5084064 baseEnd_5084064 := by
    simpa [prefixWord, tailWord_5084064, baseEnd_5084064] using wordTrace_append hprefix tailTrace_5084064
  have hstable : (prefixWord ++ tailWord_5084064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084064).length < 2 ^ (prefixWord ++ tailWord_5084064).sum := by decide
  have hdescent : baseEnd_5084064 < baseStart_5084064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084065 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5084065 : Nat := 118140960795 + 5084065 * 2 ^ 59
def prefixEnd_5084065 : Nat := 4983230072969 + 3 ^ 40 * 5084065 * 2
def baseEnd_5084065 : Nat := 2610569023700756306006317

theorem tailTrace_5084065 : CollatzResearch.WordTrace tailWord_5084065 prefixEnd_5084065 2610569023700756306006317 := by
  unfold tailWord_5084065
  simp only [CollatzResearch.WordTrace]
  refine ⟨185431084326308269019077649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123620722884205512679385099 185431084326308269019077649)
  ·
    refine ⟨139073313244731201764308237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185431084326308269019077649 139073313244731201764308237)
    ·
      refine ⟨52152492466774200661615589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139073313244731201764308237 52152492466774200661615589)
      ·
        refine ⟨9778592337520162624052923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52152492466774200661615589 9778592337520162624052923)
        ·
          refine ⟨14667888506280243936079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778592337520162624052923 14667888506280243936079385)
          ·
            refine ⟨11000916379710182952059539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14667888506280243936079385 11000916379710182952059539)
            ·
              refine ⟨16501374569565274428089309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11000916379710182952059539 16501374569565274428089309)
              ·
                refine ⟨6188015463586977910533491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16501374569565274428089309 6188015463586977910533491)
                ·
                  refine ⟨9282023195380466865800237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188015463586977910533491 9282023195380466865800237)
                  ·
                    refine ⟨3480758698267675074675089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9282023195380466865800237 3480758698267675074675089)
                    ·
                      refine ⟨2610569023700756306006317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480758698267675074675089 2610569023700756306006317)
                      ·
                        rfl

theorem cell23_5084065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5084065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084065 prefixEnd_5084065 := by exact prefixLift 5084065
  have htrace : WordTrace (prefixWord ++ tailWord_5084065) baseStart_5084065 baseEnd_5084065 := by
    simpa [prefixWord, tailWord_5084065, baseEnd_5084065] using wordTrace_append hprefix tailTrace_5084065
  have hstable : (prefixWord ++ tailWord_5084065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084065).length < 2 ^ (prefixWord ++ tailWord_5084065).sum := by decide
  have hdescent : baseEnd_5084065 < baseStart_5084065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084131 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 2, 5]
def baseStart_5084131 : Nat := 118140960795 + 5084131 * 2 ^ 59
def prefixEnd_5084131 : Nat := 4983230072969 + 3 ^ 40 * 5084131 * 2
def baseEnd_5084131 : Nat := 870200971141317682593671

theorem tailTrace_5084131 : CollatzResearch.WordTrace tailWord_5084131 prefixEnd_5084131 870200971141317682593671 := by
  unfold tailWord_5084131
  simp only [CollatzResearch.WordTrace]
  refine ⟨185433491544069162290980247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123622327696046108193986831 185433491544069162290980247)
  ·
    refine ⟨278150237316103743436470371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185433491544069162290980247 278150237316103743436470371)
    ·
      refine ⟨417225355974155615154705557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278150237316103743436470371 417225355974155615154705557)
      ·
        refine ⟨19557438561288544460376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 417225355974155615154705557 19557438561288544460376823)
        ·
          refine ⟨29336157841932816690565235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19557438561288544460376823 29336157841932816690565235)
          ·
            refine ⟨44004236762899225035847853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29336157841932816690565235 44004236762899225035847853)
            ·
              refine ⟨16501588786087209388442945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44004236762899225035847853 16501588786087209388442945)
              ·
                refine ⟨12376191589565407041332209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16501588786087209388442945 12376191589565407041332209)
                ·
                  refine ⟨9282143692174055280999157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12376191589565407041332209 9282143692174055280999157)
                  ·
                    refine ⟨870200971141317682593671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9282143692174055280999157 870200971141317682593671)
                    ·
                      rfl

theorem cell23_5084131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].length) (baseStart_5084131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084131 prefixEnd_5084131 := by exact prefixLift 5084131
  have htrace : WordTrace (prefixWord ++ tailWord_5084131) baseStart_5084131 baseEnd_5084131 := by
    simpa [prefixWord, tailWord_5084131, baseEnd_5084131] using wordTrace_append hprefix tailTrace_5084131
  have hstable : (prefixWord ++ tailWord_5084131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084131).length < 2 ^ (prefixWord ++ tailWord_5084131).sum := by decide
  have hdescent : baseEnd_5084131 < baseStart_5084131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084135 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 5]
def baseStart_5084135 : Nat := 118140960795 + 5084135 * 2 ^ 59
def prefixEnd_5084135 : Nat := 4983230072969 + 3 ^ 40 * 5084135 * 2
def baseEnd_5084135 : Nat := 290067218594063448014555

theorem tailTrace_5084135 : CollatzResearch.WordTrace tailWord_5084135 prefixEnd_5084135 290067218594063448014555 := by
  unfold tailWord_5084135
  simp only [CollatzResearch.WordTrace]
  refine ⟨185433637436054670974125859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123622424957369780649417239 185433637436054670974125859)
  ·
    refine ⟨278150456154082006461188789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185433637436054670974125859 278150456154082006461188789)
    ·
      refine ⟨26076605264445188105736449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278150456154082006461188789 26076605264445188105736449)
      ·
        refine ⟨19557453948333891079302337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26076605264445188105736449 19557453948333891079302337)
        ·
          refine ⟨14668090461250418309476753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19557453948333891079302337 14668090461250418309476753)
          ·
            refine ⟨11001067845937813732107565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14668090461250418309476753 11001067845937813732107565)
            ·
              refine ⟨4125400442226680149540337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11001067845937813732107565 4125400442226680149540337)
              ·
                refine ⟨3094050331670010112155253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125400442226680149540337 3094050331670010112155253)
                ·
                  refine ⟨290067218594063448014555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3094050331670010112155253 290067218594063448014555)
                  ·
                    rfl

theorem cell23_5084135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 5].length) (baseStart_5084135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084135 prefixEnd_5084135 := by exact prefixLift 5084135
  have htrace : WordTrace (prefixWord ++ tailWord_5084135) baseStart_5084135 baseEnd_5084135 := by
    simpa [prefixWord, tailWord_5084135, baseEnd_5084135] using wordTrace_append hprefix tailTrace_5084135
  have hstable : (prefixWord ++ tailWord_5084135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084135).length < 2 ^ (prefixWord ++ tailWord_5084135).sum := by decide
  have hdescent : baseEnd_5084135 < baseStart_5084135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084146 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5084146 : Nat := 118140960795 + 5084146 * 2 ^ 59
def prefixEnd_5084146 : Nat := 4983230072969 + 3 ^ 40 * 5084146 * 2
def baseEnd_5084146 : Nat := 2610610615633770489093445

theorem tailTrace_5084146 : CollatzResearch.WordTrace tailWord_5084146 prefixEnd_5084146 2610610615633770489093445 := by
  unfold tailWord_5084146
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358509659753704963194073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123622692426009879901850861 46358509659753704963194073)
  ·
    refine ⟨34768882244815278722395555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46358509659753704963194073 34768882244815278722395555)
    ·
      refine ⟨52153323367222918083593333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34768882244815278722395555 52153323367222918083593333)
      ·
        refine ⟨4889374065677148570336875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52153323367222918083593333 4889374065677148570336875)
        ·
          refine ⟨7334061098515722855505313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889374065677148570336875 7334061098515722855505313)
          ·
            refine ⟨5500545823886792141628985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7334061098515722855505313 5500545823886792141628985)
            ·
              refine ⟨4125409367915094106221739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500545823886792141628985 4125409367915094106221739)
              ·
                refine ⟨6188114051872641159332609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125409367915094106221739 6188114051872641159332609)
                ·
                  refine ⟨4641085538904480869499457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188114051872641159332609 4641085538904480869499457)
                  ·
                    refine ⟨3480814154178360652124593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641085538904480869499457 3480814154178360652124593)
                    ·
                      refine ⟨2610610615633770489093445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480814154178360652124593 2610610615633770489093445)
                      ·
                        rfl

theorem cell23_5084146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5084146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084146 prefixEnd_5084146 := by exact prefixLift 5084146
  have htrace : WordTrace (prefixWord ++ tailWord_5084146) baseStart_5084146 baseEnd_5084146 := by
    simpa [prefixWord, tailWord_5084146, baseEnd_5084146] using wordTrace_append hprefix tailTrace_5084146
  have hstable : (prefixWord ++ tailWord_5084146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084146).length < 2 ^ (prefixWord ++ tailWord_5084146).sum := by decide
  have hdescent : baseEnd_5084146 < baseStart_5084146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084154 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_5084154 : Nat := 118140960795 + 5084154 * 2 ^ 59
def prefixEnd_5084154 : Nat := 4983230072969 + 3 ^ 40 * 5084154 * 2
def baseEnd_5084154 : Nat := 2610614723479006457793407

theorem tailTrace_5084154 : CollatzResearch.WordTrace tailWord_5084154 prefixEnd_5084154 2610614723479006457793407 := by
  unfold tailWord_5084154
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358582605746459304766879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123622886948657224812711677 46358582605746459304766879)
  ·
    refine ⟨69537873908619688957150319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46358582605746459304766879 69537873908619688957150319)
    ·
      refine ⟨104306810862929533435725479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69537873908619688957150319 104306810862929533435725479)
      ·
        refine ⟨156460216294394300153588219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104306810862929533435725479 156460216294394300153588219)
        ·
          refine ⟨234690324441591450230382329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156460216294394300153588219 234690324441591450230382329)
          ·
            refine ⟨176017743331193587672786747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234690324441591450230382329 176017743331193587672786747)
            ·
              refine ⟨264026614996790381509180121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176017743331193587672786747 264026614996790381509180121)
              ·
                refine ⟨198019961247592786131885091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264026614996790381509180121 198019961247592786131885091)
                ·
                  refine ⟨297029941871389179197827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198019961247592786131885091 297029941871389179197827637)
                  ·
                    refine ⟨27846557050442735549796341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 297029941871389179197827637 27846557050442735549796341)
                    ·
                      refine ⟨2610614723479006457793407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27846557050442735549796341 2610614723479006457793407)
                      ·
                        rfl

theorem cell23_5084154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_5084154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084154 prefixEnd_5084154 := by exact prefixLift 5084154
  have htrace : WordTrace (prefixWord ++ tailWord_5084154) baseStart_5084154 baseEnd_5084154 := by
    simpa [prefixWord, tailWord_5084154, baseEnd_5084154] using wordTrace_append hprefix tailTrace_5084154
  have hstable : (prefixWord ++ tailWord_5084154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084154).length < 2 ^ (prefixWord ++ tailWord_5084154).sum := by decide
  have hdescent : baseEnd_5084154 < baseStart_5084154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084168 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_5084168 : Nat := 118140960795 + 5084168 * 2 ^ 59
def prefixEnd_5084168 : Nat := 4983230072969 + 3 ^ 40 * 5084168 * 2
def baseEnd_5084168 : Nat := 2610621912208169403018343

theorem tailTrace_5084168 : CollatzResearch.WordTrace tailWord_5084168 prefixEnd_5084168 2610621912208169403018343 := by
  unfold tailWord_5084168
  simp only [CollatzResearch.WordTrace]
  refine ⟨92717420522467558805038579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123623227363290078406718105 92717420522467558805038579)
  ·
    refine ⟨139076130783701338207557869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92717420522467558805038579 139076130783701338207557869)
    ·
      refine ⟨52153549043888001827834201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139076130783701338207557869 52153549043888001827834201)
      ·
        refine ⟨39115161782916001370875651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52153549043888001827834201 39115161782916001370875651)
        ·
          refine ⟨58672742674374002056313477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39115161782916001370875651 58672742674374002056313477)
          ·
            refine ⟨11001139251445125385558777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58672742674374002056313477 11001139251445125385558777)
            ·
              refine ⟨8250854438583844039169083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11001139251445125385558777 8250854438583844039169083)
              ·
                refine ⟨12376281657875766058753625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250854438583844039169083 12376281657875766058753625)
                ·
                  refine ⟨9282211243406824544065219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12376281657875766058753625 9282211243406824544065219)
                  ·
                    refine ⟨13923316865110236816097829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9282211243406824544065219 13923316865110236816097829)
                    ·
                      refine ⟨2610621912208169403018343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13923316865110236816097829 2610621912208169403018343)
                      ·
                        rfl

theorem cell23_5084168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_5084168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084168 prefixEnd_5084168 := by exact prefixLift 5084168
  have htrace : WordTrace (prefixWord ++ tailWord_5084168) baseStart_5084168 baseEnd_5084168 := by
    simpa [prefixWord, tailWord_5084168, baseEnd_5084168] using wordTrace_append hprefix tailTrace_5084168
  have hstable : (prefixWord ++ tailWord_5084168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084168).length < 2 ^ (prefixWord ++ tailWord_5084168).sum := by decide
  have hdescent : baseEnd_5084168 < baseStart_5084168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084191 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 6]
def baseStart_5084191 : Nat := 118140960795 + 5084191 * 2 ^ 59
def prefixEnd_5084191 : Nat := 4983230072969 + 3 ^ 40 * 5084191 * 2
def baseEnd_5084191 : Nat := 290070413584802534781193

theorem tailTrace_5084191 : CollatzResearch.WordTrace tailWord_5084191 prefixEnd_5084191 290070413584802534781193 := by
  unfold tailWord_5084191
  simp only [CollatzResearch.WordTrace]
  refine ⟨185435679923851792538164427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123623786615901195025442951 185435679923851792538164427)
  ·
    refine ⟨278153519885777688807246641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185435679923851792538164427 278153519885777688807246641)
    ·
      refine ⟨208615139914333266605434981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278153519885777688807246641 208615139914333266605434981)
      ·
        refine ⟨39115338733937487488519059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208615139914333266605434981 39115338733937487488519059)
        ·
          refine ⟨58673008100906231232778589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39115338733937487488519059 58673008100906231232778589)
          ·
            refine ⟨22002378037839836712291971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58673008100906231232778589 22002378037839836712291971)
            ·
              refine ⟨33003567056759755068437957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22002378037839836712291971 33003567056759755068437957)
              ·
                refine ⟨6188168823142454075332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33003567056759755068437957 6188168823142454075332117)
                ·
                  refine ⟨290070413584802534781193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6188168823142454075332117 290070413584802534781193)
                  ·
                    rfl

theorem cell23_5084191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 6].length) (baseStart_5084191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084191 prefixEnd_5084191 := by exact prefixLift 5084191
  have htrace : WordTrace (prefixWord ++ tailWord_5084191) baseStart_5084191 baseEnd_5084191 := by
    simpa [prefixWord, tailWord_5084191, baseEnd_5084191] using wordTrace_append hprefix tailTrace_5084191
  have hstable : (prefixWord ++ tailWord_5084191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084191).length < 2 ^ (prefixWord ++ tailWord_5084191).sum := by decide
  have hdescent : baseEnd_5084191 < baseStart_5084191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084195 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 1, 4]
def baseStart_5084195 : Nat := 118140960795 + 5084195 * 2 ^ 59
def prefixEnd_5084195 : Nat := 4983230072969 + 3 ^ 40 * 5084195 * 2
def baseEnd_5084195 : Nat := 870211925395280265793573

theorem tailTrace_5084195 : CollatzResearch.WordTrace tailWord_5084195 prefixEnd_5084195 870211925395280265793573 := by
  unfold tailWord_5084195
  simp only [CollatzResearch.WordTrace]
  refine ⟨185435825815837301221310039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123623883877224867480873359 185435825815837301221310039)
  ·
    refine ⟨278153738723755951831965059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185435825815837301221310039 278153738723755951831965059)
    ·
      refine ⟨417230608085633927747947589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278153738723755951831965059 417230608085633927747947589)
      ·
        refine ⟨78230739016056361452740173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 417230608085633927747947589 78230739016056361452740173)
        ·
          refine ⟨29336527131021135544777565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78230739016056361452740173 29336527131021135544777565)
          ·
            refine ⟨11001197674132925829291587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29336527131021135544777565 11001197674132925829291587)
            ·
              refine ⟨16501796511199388743937381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001197674132925829291587 16501796511199388743937381)
              ·
                refine ⟨3094086845849885389488259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16501796511199388743937381 3094086845849885389488259)
                ·
                  refine ⟨4641130268774828084232389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094086845849885389488259 4641130268774828084232389)
                  ·
                    refine ⟨870211925395280265793573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641130268774828084232389 870211925395280265793573)
                    ·
                      rfl

theorem cell23_5084195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 4].length) (baseStart_5084195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084195 prefixEnd_5084195 := by exact prefixLift 5084195
  have htrace : WordTrace (prefixWord ++ tailWord_5084195) baseStart_5084195 baseEnd_5084195 := by
    simpa [prefixWord, tailWord_5084195, baseEnd_5084195] using wordTrace_append hprefix tailTrace_5084195
  have hstable : (prefixWord ++ tailWord_5084195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084195).length < 2 ^ (prefixWord ++ tailWord_5084195).sum := by decide
  have hdescent : baseEnd_5084195 < baseStart_5084195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084218 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_5084218 : Nat := 118140960795 + 5084218 * 2 ^ 59
def prefixEnd_5084218 : Nat := 4983230072969 + 3 ^ 40 * 5084218 * 2
def baseEnd_5084218 : Nat := 2610647586240894207393113

theorem tailTrace_5084218 : CollatzResearch.WordTrace tailWord_5084218 prefixEnd_5084218 2610647586240894207393113 := by
  unfold tailWord_5084218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359166173688494037349327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123624443129835984099598205 46359166173688494037349327)
  ·
    refine ⟨69538749260532741056023991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46359166173688494037349327 69538749260532741056023991)
    ·
      refine ⟨104308123890799111584035987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69538749260532741056023991 104308123890799111584035987)
      ·
        refine ⟨156462185836198667376053981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104308123890799111584035987 156462185836198667376053981)
        ·
          refine ⟨58673319688574500266020243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156462185836198667376053981 58673319688574500266020243)
          ·
            refine ⟨88009979532861750399030365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58673319688574500266020243 88009979532861750399030365)
            ·
              refine ⟨33003742324823156399636387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88009979532861750399030365 33003742324823156399636387)
              ·
                refine ⟨49505613487234734599454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33003742324823156399636387 49505613487234734599454581)
                ·
                  refine ⟨4641151264428256368698867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49505613487234734599454581 4641151264428256368698867)
                  ·
                    refine ⟨6961726896642384553048301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641151264428256368698867 6961726896642384553048301)
                    ·
                      refine ⟨2610647586240894207393113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961726896642384553048301 2610647586240894207393113)
                      ·
                        rfl

theorem cell23_5084218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_5084218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084218 prefixEnd_5084218 := by exact prefixLift 5084218
  have htrace : WordTrace (prefixWord ++ tailWord_5084218) baseStart_5084218 baseEnd_5084218 := by
    simpa [prefixWord, tailWord_5084218, baseEnd_5084218] using wordTrace_append hprefix tailTrace_5084218
  have hstable : (prefixWord ++ tailWord_5084218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084218).length < 2 ^ (prefixWord ++ tailWord_5084218).sum := by decide
  have hdescent : baseEnd_5084218 < baseStart_5084218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084222 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5084222 : Nat := 118140960795 + 5084222 * 2 ^ 59
def prefixEnd_5084222 : Nat := 4983230072969 + 3 ^ 40 * 5084222 * 2
def baseEnd_5084222 : Nat := 2610649640163512191743095

theorem tailTrace_5084222 : CollatzResearch.WordTrace tailWord_5084222 prefixEnd_5084222 2610649640163512191743095 := by
  unfold tailWord_5084222
  simp only [CollatzResearch.WordTrace]
  refine ⟨23179601323342435604067865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123624540391159656555028613 23179601323342435604067865)
  ·
    refine ⟨17384700992506826703050899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23179601323342435604067865 17384700992506826703050899)
    ·
      refine ⟨26077051488760240054576349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384700992506826703050899 26077051488760240054576349)
      ·
        refine ⟨9778894308285090020466131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26077051488760240054576349 9778894308285090020466131)
        ·
          refine ⟨14668341462427635030699197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778894308285090020466131 14668341462427635030699197)
          ·
            refine ⟨5500628048410363136512199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14668341462427635030699197 5500628048410363136512199)
            ·
              refine ⟨8250942072615544704768299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500628048410363136512199 8250942072615544704768299)
              ·
                refine ⟨12376413108923317057152449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250942072615544704768299 12376413108923317057152449)
                ·
                  refine ⟨9282309831692487792864337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12376413108923317057152449 9282309831692487792864337)
                  ·
                    refine ⟨6961732373769365844648253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9282309831692487792864337 6961732373769365844648253)
                    ·
                      refine ⟨2610649640163512191743095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961732373769365844648253 2610649640163512191743095)
                      ·
                        rfl

theorem cell23_5084222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5084222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084222 prefixEnd_5084222 := by exact prefixLift 5084222
  have htrace : WordTrace (prefixWord ++ tailWord_5084222) baseStart_5084222 baseEnd_5084222 := by
    simpa [prefixWord, tailWord_5084222, baseEnd_5084222] using wordTrace_append hprefix tailTrace_5084222
  have hstable : (prefixWord ++ tailWord_5084222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084222).length < 2 ^ (prefixWord ++ tailWord_5084222).sum := by decide
  have hdescent : baseEnd_5084222 < baseStart_5084222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084238 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_5084238 : Nat := 118140960795 + 5084238 * 2 ^ 59
def prefixEnd_5084238 : Nat := 4983230072969 + 3 ^ 40 * 5084238 * 2
def baseEnd_5084238 : Nat := 870219285284661376381007

theorem tailTrace_5084238 : CollatzResearch.WordTrace tailWord_5084238 prefixEnd_5084238 870219285284661376381007 := by
  unfold tailWord_5084238
  simp only [CollatzResearch.WordTrace]
  refine ⟨23179674269335189945640671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123624929436454346376750245 23179674269335189945640671)
  ·
    refine ⟨34769511404002784918461007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23179674269335189945640671 34769511404002784918461007)
    ·
      refine ⟨52154267106004177377691511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34769511404002784918461007 52154267106004177377691511)
      ·
        refine ⟨78231400659006266066537267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52154267106004177377691511 78231400659006266066537267)
        ·
          refine ⟨117347100988509399099805901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78231400659006266066537267 117347100988509399099805901)
          ·
            refine ⟨44005162870691024662427213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117347100988509399099805901 44005162870691024662427213)
            ·
              refine ⟨16501936076509134248410205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44005162870691024662427213 16501936076509134248410205)
              ·
                refine ⟨6188226028690925343153827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16501936076509134248410205 6188226028690925343153827)
                ·
                  refine ⟨9282339043036388014730741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188226028690925343153827 9282339043036388014730741)
                  ·
                    refine ⟨870219285284661376381007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9282339043036388014730741 870219285284661376381007)
                    ·
                      rfl

theorem cell23_5084238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_5084238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084238 prefixEnd_5084238 := by exact prefixLift 5084238
  have htrace : WordTrace (prefixWord ++ tailWord_5084238) baseStart_5084238 baseEnd_5084238 := by
    simpa [prefixWord, tailWord_5084238, baseEnd_5084238] using wordTrace_append hprefix tailTrace_5084238
  have hstable : (prefixWord ++ tailWord_5084238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084238).length < 2 ^ (prefixWord ++ tailWord_5084238).sum := by decide
  have hdescent : baseEnd_5084238 < baseStart_5084238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084252 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_5084252 : Nat := 118140960795 + 5084252 * 2 ^ 59
def prefixEnd_5084252 : Nat := 4983230072969 + 3 ^ 40 * 5084252 * 2
def baseEnd_5084252 : Nat := 2610665044583147074367957

theorem tailTrace_5084252 : CollatzResearch.WordTrace tailWord_5084252 prefixEnd_5084252 2610665044583147074367957 := by
  unfold tailWord_5084252
  simp only [CollatzResearch.WordTrace]
  refine ⟨92718952388315399978067505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123625269851087199970756673 92718952388315399978067505)
  ·
    refine ⟨69539214291236549983550629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92718952388315399978067505 69539214291236549983550629)
    ·
      refine ⟨13038602679606853121915743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69539214291236549983550629 13038602679606853121915743)
      ·
        refine ⟨19557904019410279682873615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13038602679606853121915743 19557904019410279682873615)
        ·
          refine ⟨29336856029115419524310423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19557904019410279682873615 29336856029115419524310423)
          ·
            refine ⟨44005284043673129286465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29336856029115419524310423 44005284043673129286465635)
            ·
              refine ⟨66007926065509693929698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44005284043673129286465635 66007926065509693929698453)
              ·
                refine ⟨3094121534320766902954615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66007926065509693929698453 3094121534320766902954615)
                ·
                  refine ⟨4641182301481150354431923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094121534320766902954615 4641182301481150354431923)
                  ·
                    refine ⟨6961773452221725531647885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641182301481150354431923 6961773452221725531647885)
                    ·
                      refine ⟨2610665044583147074367957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6961773452221725531647885 2610665044583147074367957)
                      ·
                        rfl

theorem cell23_5084252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_5084252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084252 prefixEnd_5084252 := by exact prefixLift 5084252
  have htrace : WordTrace (prefixWord ++ tailWord_5084252) baseStart_5084252 baseEnd_5084252 := by
    simpa [prefixWord, tailWord_5084252, baseEnd_5084252] using wordTrace_append hprefix tailTrace_5084252
  have hstable : (prefixWord ++ tailWord_5084252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084252).length < 2 ^ (prefixWord ++ tailWord_5084252).sum := by decide
  have hdescent : baseEnd_5084252 < baseStart_5084252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084271 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_5084271 : Nat := 118140960795 + 5084271 * 2 ^ 59
def prefixEnd_5084271 : Nat := 4983230072969 + 3 ^ 40 * 5084271 * 2
def baseEnd_5084271 : Nat := 2610674800715582500030369

theorem tailTrace_5084271 : CollatzResearch.WordTrace tailWord_5084271 prefixEnd_5084271 2610674800715582500030369 := by
  unfold tailWord_5084271
  simp only [CollatzResearch.WordTrace]
  refine ⟨185438597763561966201076667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123625731842374644134051111 185438597763561966201076667)
  ·
    refine ⟨278157896645342949301615001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185438597763561966201076667 278157896645342949301615001)
    ·
      refine ⟨208618422484007211976211251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278157896645342949301615001 208618422484007211976211251)
      ·
        refine ⟨312927633726010817964316877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208618422484007211976211251 312927633726010817964316877)
        ·
          refine ⟨117347862647254056736618829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312927633726010817964316877 117347862647254056736618829)
          ·
            refine ⟨44005448492720271276232061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117347862647254056736618829 44005448492720271276232061)
            ·
              refine ⟨16502043184770101728587023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44005448492720271276232061 16502043184770101728587023)
              ·
                refine ⟨24753064777155152592880535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16502043184770101728587023 24753064777155152592880535)
                ·
                  refine ⟨37129597165732728889320803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24753064777155152592880535 37129597165732728889320803)
                  ·
                    refine ⟨55694395748599093333981205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37129597165732728889320803 55694395748599093333981205)
                    ·
                      refine ⟨2610674800715582500030369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55694395748599093333981205 2610674800715582500030369)
                      ·
                        rfl

theorem cell23_5084271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_5084271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084271 prefixEnd_5084271 := by exact prefixLift 5084271
  have htrace : WordTrace (prefixWord ++ tailWord_5084271) baseStart_5084271 baseEnd_5084271 := by
    simpa [prefixWord, tailWord_5084271, baseEnd_5084271] using wordTrace_append hprefix tailTrace_5084271
  have hstable : (prefixWord ++ tailWord_5084271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084271).length < 2 ^ (prefixWord ++ tailWord_5084271).sum := by decide
  have hdescent : baseEnd_5084271 < baseStart_5084271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084278 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5084278 : Nat := 118140960795 + 5084278 * 2 ^ 59
def prefixEnd_5084278 : Nat := 4983230072969 + 3 ^ 40 * 5084278 * 2
def baseEnd_5084278 : Nat := 2610678395080163972642837

theorem tailTrace_5084278 : CollatzResearch.WordTrace tailWord_5084278 prefixEnd_5084278 2610678395080163972642837 := by
  unfold tailWord_5084278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11589928317158537899786343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123625902049691070931054325 11589928317158537899786343)
  ·
    refine ⟨17384892475737806849679515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11589928317158537899786343 17384892475737806849679515)
    ·
      refine ⟨26077338713606710274519273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384892475737806849679515 26077338713606710274519273)
      ·
        refine ⟨19558004035205032705889455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26077338713606710274519273 19558004035205032705889455)
        ·
          refine ⟨29337006052807549058834183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19558004035205032705889455 29337006052807549058834183)
          ·
            refine ⟨44005509079211323588251275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29337006052807549058834183 44005509079211323588251275)
            ·
              refine ⟨66008263618816985382376913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44005509079211323588251275 66008263618816985382376913)
              ·
                refine ⟨49506197714112739036782685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66008263618816985382376913 49506197714112739036782685)
                ·
                  refine ⟨18564824142792277138793507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49506197714112739036782685 18564824142792277138793507)
                  ·
                    refine ⟨27847236214188415708190261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18564824142792277138793507 27847236214188415708190261)
                    ·
                      refine ⟨2610678395080163972642837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27847236214188415708190261 2610678395080163972642837)
                      ·
                        rfl

theorem cell23_5084278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5084278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084278 prefixEnd_5084278 := by exact prefixLift 5084278
  have htrace : WordTrace (prefixWord ++ tailWord_5084278) baseStart_5084278 baseEnd_5084278 := by
    simpa [prefixWord, tailWord_5084278, baseEnd_5084278] using wordTrace_append hprefix tailTrace_5084278
  have hstable : (prefixWord ++ tailWord_5084278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084278).length < 2 ^ (prefixWord ++ tailWord_5084278).sum := by decide
  have hdescent : baseEnd_5084278 < baseStart_5084278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084319 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 2, 4]
def baseStart_5084319 : Nat := 118140960795 + 5084319 * 2 ^ 59
def prefixEnd_5084319 : Nat := 4983230072969 + 3 ^ 40 * 5084319 * 2
def baseEnd_5084319 : Nat := 870233149262332770743383

theorem tailTrace_5084319 : CollatzResearch.WordTrace tailWord_5084319 prefixEnd_5084319 870233149262332770743383 := by
  unfold tailWord_5084319
  simp only [CollatzResearch.WordTrace]
  refine ⟨185440348467388070398824011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123626898978258713599216007 185440348467388070398824011)
  ·
    refine ⟨278160522701082105598236017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185440348467388070398824011 278160522701082105598236017)
    ·
      refine ⟨208620392025811579198677013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278160522701082105598236017 208620392025811579198677013)
      ·
        refine ⟨9779080876209917774937985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208620392025811579198677013 9779080876209917774937985)
        ·
          refine ⟨7334310657157438331203489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9779080876209917774937985 7334310657157438331203489)
          ·
            refine ⟨5500732992868078748402617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7334310657157438331203489 5500732992868078748402617)
            ·
              refine ⟨4125549744651059061301963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500732992868078748402617 4125549744651059061301963)
              ·
                refine ⟨6188324616976588591952945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125549744651059061301963 6188324616976588591952945)
                ·
                  refine ⟨4641243462732441443964709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188324616976588591952945 4641243462732441443964709)
                  ·
                    refine ⟨870233149262332770743383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641243462732441443964709 870233149262332770743383)
                    ·
                      rfl

theorem cell23_5084319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_5084319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084319 prefixEnd_5084319 := by exact prefixLift 5084319
  have htrace : WordTrace (prefixWord ++ tailWord_5084319) baseStart_5084319 baseEnd_5084319 := by
    simpa [prefixWord, tailWord_5084319, baseEnd_5084319] using wordTrace_append hprefix tailTrace_5084319
  have hstable : (prefixWord ++ tailWord_5084319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084319).length < 2 ^ (prefixWord ++ tailWord_5084319).sum := by decide
  have hdescent : baseEnd_5084319 < baseStart_5084319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084533 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5084533 : Nat := 118140960795 + 5084533 * 2 ^ 59
def prefixEnd_5084533 : Nat := 4983230072969 + 3 ^ 40 * 5084533 * 2
def baseEnd_5084533 : Nat := 870269777549020158318055

theorem tailTrace_5084533 : CollatzResearch.WordTrace tailWord_5084533 prefixEnd_5084533 870269777549020158318055 := by
  unfold tailWord_5084533
  simp only [CollatzResearch.WordTrace]
  refine ⟨185448153688612784947114253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123632102459075189964742835 185448153688612784947114253)
  ·
    refine ⟨69543057633229794355167845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185448153688612784947114253 69543057633229794355167845)
    ·
      refine ⟨13039323306230586441593971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69543057633229794355167845 13039323306230586441593971)
      ·
        refine ⟨19558984959345879662390957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13039323306230586441593971 19558984959345879662390957)
        ·
          refine ⟨7334619359754704873396609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19558984959345879662390957 7334619359754704873396609)
          ·
            refine ⟨5500964519816028655047457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7334619359754704873396609 5500964519816028655047457)
            ·
              refine ⟨4125723389862021491285593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500964519816028655047457 4125723389862021491285593)
              ·
                refine ⟨3094292542396516118464195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125723389862021491285593 3094292542396516118464195)
                ·
                  refine ⟨4641438813594774177696293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094292542396516118464195 4641438813594774177696293)
                  ·
                    refine ⟨870269777549020158318055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641438813594774177696293 870269777549020158318055)
                    ·
                      rfl

theorem cell23_5084533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5084533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084533 prefixEnd_5084533 := by exact prefixLift 5084533
  have htrace : WordTrace (prefixWord ++ tailWord_5084533) baseStart_5084533 baseEnd_5084533 := by
    simpa [prefixWord, tailWord_5084533, baseEnd_5084533] using wordTrace_append hprefix tailTrace_5084533
  have hstable : (prefixWord ++ tailWord_5084533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084533).length < 2 ^ (prefixWord ++ tailWord_5084533).sum := by decide
  have hdescent : baseEnd_5084533 < baseStart_5084533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084539 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 1, 1, 3]
def baseStart_5084539 : Nat := 118140960795 + 5084539 * 2 ^ 59
def prefixEnd_5084539 : Nat := 4983230072969 + 3 ^ 40 * 5084539 * 2
def baseEnd_5084539 : Nat := 2610812413530987451479137

theorem tailTrace_5084539 : CollatzResearch.WordTrace tailWord_5084539 prefixEnd_5084539 2610812413530987451479137 := by
  unfold tailWord_5084539
  simp only [CollatzResearch.WordTrace]
  refine ⟨185448372526591047971832671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123632248351060698647888447 185448372526591047971832671)
  ·
    refine ⟨278172558789886571957749007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185448372526591047971832671 278172558789886571957749007)
    ·
      refine ⟨417258838184829857936623511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278172558789886571957749007 417258838184829857936623511)
      ·
        refine ⟨625888257277244786904935267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417258838184829857936623511 625888257277244786904935267)
        ·
          refine ⟨938832385915867180357402901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625888257277244786904935267 938832385915867180357402901)
          ·
            refine ⟨44007768089806274079253261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 938832385915867180357402901 44007768089806274079253261)
            ·
              refine ⟨16502913033677352779719973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44007768089806274079253261 16502913033677352779719973)
              ·
                refine ⟨3094296193814503646197495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16502913033677352779719973 3094296193814503646197495)
                ·
                  refine ⟨4641444290721755469296243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094296193814503646197495 4641444290721755469296243)
                  ·
                    refine ⟨6962166436082633203944365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641444290721755469296243 6962166436082633203944365)
                    ·
                      refine ⟨2610812413530987451479137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6962166436082633203944365 2610812413530987451479137)
                      ·
                        rfl

theorem cell23_5084539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 1, 3].length) (baseStart_5084539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084539 prefixEnd_5084539 := by exact prefixLift 5084539
  have htrace : WordTrace (prefixWord ++ tailWord_5084539) baseStart_5084539 baseEnd_5084539 := by
    simpa [prefixWord, tailWord_5084539, baseEnd_5084539] using wordTrace_append hprefix tailTrace_5084539
  have hstable : (prefixWord ++ tailWord_5084539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084539).length < 2 ^ (prefixWord ++ tailWord_5084539).sum := by decide
  have hdescent : baseEnd_5084539 < baseStart_5084539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084555 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 6]
def baseStart_5084555 : Nat := 118140960795 + 5084555 * 2 ^ 59
def prefixEnd_5084555 : Nat := 4983230072969 + 3 ^ 40 * 5084555 * 2
def baseEnd_5084555 : Nat := 870273543073819796293021

theorem tailTrace_5084555 : CollatzResearch.WordTrace tailWord_5084555 prefixEnd_5084555 870273543073819796293021 := by
  unfold tailWord_5084555
  simp only [CollatzResearch.WordTrace]
  refine ⟨185448956094533082704415119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123632637396355388469610079 185448956094533082704415119)
  ·
    refine ⟨278173434141799624056622679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185448956094533082704415119 278173434141799624056622679)
    ·
      refine ⟨417260151212699436084934019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278173434141799624056622679 417260151212699436084934019)
      ·
        refine ⟨625890226819049154127401029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417260151212699436084934019 625890226819049154127401029)
        ·
          refine ⟨117354417528571716398887693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 625890226819049154127401029 117354417528571716398887693)
          ·
            refine ⟨44007906573214393649582885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117354417528571716398887693 44007906573214393649582885)
            ·
              refine ⟨8251482482477698809296791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44007906573214393649582885 8251482482477698809296791)
              ·
                refine ⟨12377223723716548213945187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251482482477698809296791 12377223723716548213945187)
                ·
                  refine ⟨18565835585574822320917781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12377223723716548213945187 18565835585574822320917781)
                  ·
                    refine ⟨870273543073819796293021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18565835585574822320917781 870273543073819796293021)
                    ·
                      rfl

theorem cell23_5084555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].length) (baseStart_5084555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084555 prefixEnd_5084555 := by exact prefixLift 5084555
  have htrace : WordTrace (prefixWord ++ tailWord_5084555) baseStart_5084555 baseEnd_5084555 := by
    simpa [prefixWord, tailWord_5084555, baseEnd_5084555] using wordTrace_append hprefix tailTrace_5084555
  have hstable : (prefixWord ++ tailWord_5084555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084555).length < 2 ^ (prefixWord ++ tailWord_5084555).sum := by decide
  have hdescent : baseEnd_5084555 < baseStart_5084555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084589 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5084589 : Nat := 118140960795 + 5084589 * 2 ^ 59
def prefixEnd_5084589 : Nat := 4983230072969 + 3 ^ 40 * 5084589 * 2
def baseEnd_5084589 : Nat := 870279362521237418617969

theorem tailTrace_5084589 : CollatzResearch.WordTrace tailWord_5084589 prefixEnd_5084589 870279362521237418617969 := by
  unfold tailWord_5084589
  simp only [CollatzResearch.WordTrace]
  refine ⟨185450196176409906511152821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123633464117606604340768547 185450196176409906511152821)
  ·
    refine ⟨17385955891538428735420577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185450196176409906511152821 17385955891538428735420577)
    ·
      refine ⟨13039466918653821551565433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17385955891538428735420577 13039466918653821551565433)
      ·
        refine ⟨9779600188990366163674075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13039466918653821551565433 9779600188990366163674075)
        ·
          refine ⟨14669400283485549245511113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9779600188990366163674075 14669400283485549245511113)
          ·
            refine ⟨11002050212614161934133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14669400283485549245511113 11002050212614161934133335)
            ·
              refine ⟨16503075318921242901200003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002050212614161934133335 16503075318921242901200003)
              ·
                refine ⟨24754612978381864351800005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16503075318921242901200003 24754612978381864351800005)
                ·
                  refine ⟨4641489933446599565962501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24754612978381864351800005 4641489933446599565962501)
                  ·
                    refine ⟨870279362521237418617969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641489933446599565962501 870279362521237418617969)
                    ·
                      rfl

theorem cell23_5084589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5084589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084589 prefixEnd_5084589 := by exact prefixLift 5084589
  have htrace : WordTrace (prefixWord ++ tailWord_5084589) baseStart_5084589 baseEnd_5084589 := by
    simpa [prefixWord, tailWord_5084589, baseEnd_5084589] using wordTrace_append hprefix tailTrace_5084589
  have hstable : (prefixWord ++ tailWord_5084589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084589).length < 2 ^ (prefixWord ++ tailWord_5084589).sum := by decide
  have hdescent : baseEnd_5084589 < baseStart_5084589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084595 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3]
def baseStart_5084595 : Nat := 118140960795 + 5084595 * 2 ^ 59
def prefixEnd_5084595 : Nat := 4983230072969 + 3 ^ 40 * 5084595 * 2
def baseEnd_5084595 : Nat := 2610841168447639232378879

theorem tailTrace_5084595 : CollatzResearch.WordTrace tailWord_5084595 prefixEnd_5084595 2610841168447639232378879 := by
  unfold tailWord_5084595
  simp only [CollatzResearch.WordTrace]
  refine ⟨185450415014388169535871239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123633610009592113023914159 185450415014388169535871239)
  ·
    refine ⟨278175622521582254303806859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185450415014388169535871239 278175622521582254303806859)
    ·
      refine ⟨417263433782373381455710289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278175622521582254303806859 417263433782373381455710289)
      ·
        refine ⟨312947575336780036091782717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417263433782373381455710289 312947575336780036091782717)
        ·
          refine ⟨117355340751292513534418519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312947575336780036091782717 117355340751292513534418519)
          ·
            refine ⟨176033011126938770301627779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117355340751292513534418519 176033011126938770301627779)
            ·
              refine ⟨264049516690408155452441669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176033011126938770301627779 264049516690408155452441669)
              ·
                refine ⟨49509284379451529147332813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264049516690408155452441669 49509284379451529147332813)
                ·
                  refine ⟨18565981642294323430249805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49509284379451529147332813 18565981642294323430249805)
                  ·
                    refine ⟨6962243115860371286343677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18565981642294323430249805 6962243115860371286343677)
                    ·
                      refine ⟨2610841168447639232378879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6962243115860371286343677 2610841168447639232378879)
                      ·
                        rfl

theorem cell23_5084595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_5084595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084595 prefixEnd_5084595 := by exact prefixLift 5084595
  have htrace : WordTrace (prefixWord ++ tailWord_5084595) baseStart_5084595 baseEnd_5084595 := by
    simpa [prefixWord, tailWord_5084595, baseEnd_5084595] using wordTrace_append hprefix tailTrace_5084595
  have hstable : (prefixWord ++ tailWord_5084595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084595).length < 2 ^ (prefixWord ++ tailWord_5084595).sum := by decide
  have hdescent : baseEnd_5084595 < baseStart_5084595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084610 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5084610 : Nat := 118140960795 + 5084610 * 2 ^ 59
def prefixEnd_5084610 : Nat := 4983230072969 + 3 ^ 40 * 5084610 * 2
def baseEnd_5084610 : Nat := 870282956885818891230437

theorem tailTrace_5084610 : CollatzResearch.WordTrace tailWord_5084610 prefixEnd_5084610 870282956885818891230437 := by
  unfold tailWord_5084610
  simp only [CollatzResearch.WordTrace]
  refine ⟨46362740527333456774416821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123633974739555884731778189 46362740527333456774416821)
  ·
    refine ⟨4346506924437511572601577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46362740527333456774416821 4346506924437511572601577)
    ·
      refine ⟨3259880193328133679451183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4346506924437511572601577 3259880193328133679451183)
      ·
        refine ⟨4889820289992200519176775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259880193328133679451183 4889820289992200519176775)
        ·
          refine ⟨7334730434988300778765163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889820289992200519176775 7334730434988300778765163)
          ·
            refine ⟨11002095652482451168147745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334730434988300778765163 11002095652482451168147745)
            ·
              refine ⟨8251571739361838376110809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11002095652482451168147745 8251571739361838376110809)
              ·
                refine ⟨6188678804521378782083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8251571739361838376110809 6188678804521378782083107)
                ·
                  refine ⟨9283018206782068173124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188678804521378782083107 9283018206782068173124661)
                  ·
                    refine ⟨870282956885818891230437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9283018206782068173124661 870282956885818891230437)
                    ·
                      rfl

theorem cell23_5084610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5084610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084610 prefixEnd_5084610 := by exact prefixLift 5084610
  have htrace : WordTrace (prefixWord ++ tailWord_5084610) baseStart_5084610 baseEnd_5084610 := by
    simpa [prefixWord, tailWord_5084610, baseEnd_5084610] using wordTrace_append hprefix tailTrace_5084610
  have hstable : (prefixWord ++ tailWord_5084610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084610).length < 2 ^ (prefixWord ++ tailWord_5084610).sum := by decide
  have hdescent : baseEnd_5084610 < baseStart_5084610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084630 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5084630 : Nat := 118140960795 + 5084630 * 2 ^ 59
def prefixEnd_5084630 : Nat := 4983230072969 + 3 ^ 40 * 5084630 * 2
def baseEnd_5084630 : Nat := 2610859140270546595441219

theorem tailTrace_5084630 : CollatzResearch.WordTrace tailWord_5084630 prefixEnd_5084630 2610859140270546595441219 := by
  unfold tailWord_5084630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590730723078835657087209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123634461046174247008930229 11590730723078835657087209)
  ·
    refine ⟨8693048042309126742815407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11590730723078835657087209 8693048042309126742815407)
    ·
      refine ⟨13039572063463690114223111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693048042309126742815407 13039572063463690114223111)
      ·
        refine ⟨19559358095195535171334667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13039572063463690114223111 19559358095195535171334667)
        ·
          refine ⟨29339037142793302757002001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19559358095195535171334667 29339037142793302757002001)
          ·
            refine ⟨22004277857094977067751501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29339037142793302757002001 22004277857094977067751501)
            ·
              refine ⟨8251604196410616400406813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22004277857094977067751501 8251604196410616400406813)
              ·
                refine ⟨3094351573653981150152555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8251604196410616400406813 3094351573653981150152555)
                ·
                  refine ⟨4641527360480971725228833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094351573653981150152555 4641527360480971725228833)
                  ·
                    refine ⟨3481145520360728793921625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641527360480971725228833 3481145520360728793921625)
                    ·
                      refine ⟨2610859140270546595441219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481145520360728793921625 2610859140270546595441219)
                      ·
                        rfl

theorem cell23_5084630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5084630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084630 prefixEnd_5084630 := by exact prefixLift 5084630
  have htrace : WordTrace (prefixWord ++ tailWord_5084630) baseStart_5084630 baseEnd_5084630 := by
    simpa [prefixWord, tailWord_5084630, baseEnd_5084630] using wordTrace_append hprefix tailTrace_5084630
  have hstable : (prefixWord ++ tailWord_5084630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084630).length < 2 ^ (prefixWord ++ tailWord_5084630).sum := by decide
  have hdescent : baseEnd_5084630 < baseStart_5084630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084639 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 1, 3, 2]
def baseStart_5084639 : Nat := 118140960795 + 5084639 * 2 ^ 59
def prefixEnd_5084639 : Nat := 4983230072969 + 3 ^ 40 * 5084639 * 2
def baseEnd_5084639 : Nat := 2610863761596437060228677

theorem tailTrace_5084639 : CollatzResearch.WordTrace tailWord_5084639 prefixEnd_5084639 2610863761596437060228677 := by
  unfold tailWord_5084639
  simp only [CollatzResearch.WordTrace]
  refine ⟨185452019826228765050472971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123634679884152510033648647 185452019826228765050472971)
  ·
    refine ⟨278178029739343147575709457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185452019826228765050472971 278178029739343147575709457)
    ·
      refine ⟨208633522304507360681782093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278178029739343147575709457 208633522304507360681782093)
      ·
        refine ⟨78237570864190260255668285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208633522304507360681782093 78237570864190260255668285)
        ·
          refine ⟨29339089074071347595875607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78237570864190260255668285 29339089074071347595875607)
          ·
            refine ⟨44008633611107021393813411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29339089074071347595875607 44008633611107021393813411)
            ·
              refine ⟨66012950416660532090720117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44008633611107021393813411 66012950416660532090720117)
              ·
                refine ⟨6188714101561924883505011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66012950416660532090720117 6188714101561924883505011)
                ·
                  refine ⟨9283071152342887325257517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188714101561924883505011 9283071152342887325257517)
                  ·
                    refine ⟨3481151682128582746971569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9283071152342887325257517 3481151682128582746971569)
                    ·
                      refine ⟨2610863761596437060228677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481151682128582746971569 2610863761596437060228677)
                      ·
                        rfl

theorem cell23_5084639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_5084639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084639 prefixEnd_5084639 := by exact prefixLift 5084639
  have htrace : WordTrace (prefixWord ++ tailWord_5084639) baseStart_5084639 baseEnd_5084639 := by
    simpa [prefixWord, tailWord_5084639, baseEnd_5084639] using wordTrace_append hprefix tailTrace_5084639
  have hstable : (prefixWord ++ tailWord_5084639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084639).length < 2 ^ (prefixWord ++ tailWord_5084639).sum := by decide
  have hdescent : baseEnd_5084639 < baseStart_5084639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_5084652 : Nat := 118140960795 + 5084652 * 2 ^ 59
def prefixEnd_5084652 : Nat := 4983230072969 + 3 ^ 40 * 5084652 * 2
def baseEnd_5084652 : Nat := 2610870436844945509366117

theorem tailTrace_5084652 : CollatzResearch.WordTrace tailWord_5084652 prefixEnd_5084652 2610870436844945509366117 := by
  unfold tailWord_5084652
  simp only [CollatzResearch.WordTrace]
  refine ⟨92726246987590834135348105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123634995983454445513797473 92726246987590834135348105)
  ·
    refine ⟨69544685240693125601511079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92726246987590834135348105 69544685240693125601511079)
    ·
      refine ⟨104317027861039688402266619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69544685240693125601511079 104317027861039688402266619)
      ·
        refine ⟨156475541791559532603399929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104317027861039688402266619 156475541791559532603399929)
        ·
          refine ⟨117356656343669649452549947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156475541791559532603399929 117356656343669649452549947)
          ·
            refine ⟨176034984515504474178824921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117356656343669649452549947 176034984515504474178824921)
            ·
              refine ⟨132026238386628355634118691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176034984515504474178824921 132026238386628355634118691)
              ·
                refine ⟨198039357579942533451178037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132026238386628355634118691 198039357579942533451178037)
                ·
                  refine ⟨18566189773119612511047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198039357579942533451178037 18566189773119612511047941)
                  ·
                    refine ⟨3481160582459927345821489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18566189773119612511047941 3481160582459927345821489)
                    ·
                      refine ⟨2610870436844945509366117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481160582459927345821489 2610870436844945509366117)
                      ·
                        rfl

theorem cell23_5084652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_5084652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084652 prefixEnd_5084652 := by exact prefixLift 5084652
  have htrace : WordTrace (prefixWord ++ tailWord_5084652) baseStart_5084652 baseEnd_5084652 := by
    simpa [prefixWord, tailWord_5084652, baseEnd_5084652] using wordTrace_append hprefix tailTrace_5084652
  have hstable : (prefixWord ++ tailWord_5084652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084652).length < 2 ^ (prefixWord ++ tailWord_5084652).sum := by decide
  have hdescent : baseEnd_5084652 < baseStart_5084652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084665 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_5084665 : Nat := 118140960795 + 5084665 * 2 ^ 59
def prefixEnd_5084665 : Nat := 4983230072969 + 3 ^ 40 * 5084665 * 2
def baseEnd_5084665 : Nat := 2610877112093453958503557

theorem tailTrace_5084665 : CollatzResearch.WordTrace tailWord_5084665 prefixEnd_5084665 2610877112093453958503557 := by
  unfold tailWord_5084665
  simp only [CollatzResearch.WordTrace]
  refine ⟨185452968124134571490919449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123635312082756380993946299 185452968124134571490919449)
  ·
    refine ⟨139089726093100928618189587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185452968124134571490919449 139089726093100928618189587)
    ·
      refine ⟨208634589139651392927284381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139089726093100928618189587 208634589139651392927284381)
      ·
        refine ⟨78237970927369272347731643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208634589139651392927284381 78237970927369272347731643)
        ·
          refine ⟨117356956391053908521597465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78237970927369272347731643 117356956391053908521597465)
          ·
            refine ⟨88017717293290431391198099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117356956391053908521597465 88017717293290431391198099)
            ·
              refine ⟨132026575939935647086797149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88017717293290431391198099 132026575939935647086797149)
              ·
                refine ⟨49509965977475867657548931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132026575939935647086797149 49509965977475867657548931)
                ·
                  refine ⟨74264948966213801486323397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49509965977475867657548931 74264948966213801486323397)
                  ·
                    refine ⟨13924677931165087778685637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74264948966213801486323397 13924677931165087778685637)
                    ·
                      refine ⟨2610877112093453958503557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13924677931165087778685637 2610877112093453958503557)
                      ·
                        rfl

theorem cell23_5084665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_5084665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084665 prefixEnd_5084665 := by exact prefixLift 5084665
  have htrace : WordTrace (prefixWord ++ tailWord_5084665) baseStart_5084665 baseEnd_5084665 := by
    simpa [prefixWord, tailWord_5084665, baseEnd_5084665] using wordTrace_append hprefix tailTrace_5084665
  have hstable : (prefixWord ++ tailWord_5084665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084665).length < 2 ^ (prefixWord ++ tailWord_5084665).sum := by decide
  have hdescent : baseEnd_5084665 < baseStart_5084665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084673 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_5084673 : Nat := 118140960795 + 5084673 * 2 ^ 59
def prefixEnd_5084673 : Nat := 4983230072969 + 3 ^ 40 * 5084673 * 2
def baseEnd_5084673 : Nat := 2610881219938689927203521

theorem tailTrace_5084673 : CollatzResearch.WordTrace tailWord_5084673 prefixEnd_5084673 2610881219938689927203521 := by
  unfold tailWord_5084673
  simp only [CollatzResearch.WordTrace]
  refine ⟨185453259908105588857210673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123635506605403725904807115 185453259908105588857210673)
  ·
    refine ⟨139089944931079191642908005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185453259908105588857210673 139089944931079191642908005)
    ·
      refine ⟨26079364674577348433045251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139089944931079191642908005 26079364674577348433045251)
      ·
        refine ⟨39119047011866022649567877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26079364674577348433045251 39119047011866022649567877)
        ·
          refine ⟨7334821314724879246793977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39119047011866022649567877 7334821314724879246793977)
          ·
            refine ⟨5501115986043659435095483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7334821314724879246793977 5501115986043659435095483)
            ·
              refine ⟨8251673979065489152643225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501115986043659435095483 8251673979065489152643225)
              ·
                refine ⟨6188755484299116864482419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8251673979065489152643225 6188755484299116864482419)
                ·
                  refine ⟨9283133226448675296723629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188755484299116864482419 9283133226448675296723629)
                  ·
                    refine ⟨3481174959918253236271361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9283133226448675296723629 3481174959918253236271361)
                    ·
                      refine ⟨2610881219938689927203521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481174959918253236271361 2610881219938689927203521)
                      ·
                        rfl

theorem cell23_5084673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_5084673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084673 prefixEnd_5084673 := by exact prefixLift 5084673
  have htrace : WordTrace (prefixWord ++ tailWord_5084673) baseStart_5084673 baseEnd_5084673 := by
    simpa [prefixWord, tailWord_5084673, baseEnd_5084673] using wordTrace_append hprefix tailTrace_5084673
  have hstable : (prefixWord ++ tailWord_5084673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084673).length < 2 ^ (prefixWord ++ tailWord_5084673).sum := by decide
  have hdescent : baseEnd_5084673 < baseStart_5084673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084686 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5084686 : Nat := 118140960795 + 5084686 * 2 ^ 59
def prefixEnd_5084686 : Nat := 4983230072969 + 3 ^ 40 * 5084686 * 2
def baseEnd_5084686 : Nat := 2610887895187198376340961

theorem tailTrace_5084686 : CollatzResearch.WordTrace tailWord_5084686 prefixEnd_5084686 2610887895187198376340961 := by
  unfold tailWord_5084686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23181716757132311509679239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123635822704705661384955941 23181716757132311509679239)
  ·
    refine ⟨34772575135698467264518859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23181716757132311509679239 34772575135698467264518859)
    ·
      refine ⟨52158862703547700896778289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34772575135698467264518859 52158862703547700896778289)
      ·
        refine ⟨39119147027660775672583717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52158862703547700896778289 39119147027660775672583717)
        ·
          refine ⟨7334840067686395438609447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39119147027660775672583717 7334840067686395438609447)
          ·
            refine ⟨11002260101529593157914171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334840067686395438609447 11002260101529593157914171)
            ·
              refine ⟨16503390152294389736871257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002260101529593157914171 16503390152294389736871257)
              ·
                refine ⟨12377542614220792302653443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16503390152294389736871257 12377542614220792302653443)
                ·
                  refine ⟨18566313921331188453980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12377542614220792302653443 18566313921331188453980165)
                  ·
                    refine ⟨3481183860249597835121281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18566313921331188453980165 3481183860249597835121281)
                    ·
                      refine ⟨2610887895187198376340961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481183860249597835121281 2610887895187198376340961)
                      ·
                        rfl

theorem cell23_5084686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5084686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084686 prefixEnd_5084686 := by exact prefixLift 5084686
  have htrace : WordTrace (prefixWord ++ tailWord_5084686) baseStart_5084686 baseEnd_5084686 := by
    simpa [prefixWord, tailWord_5084686, baseEnd_5084686] using wordTrace_append hprefix tailTrace_5084686
  have hstable : (prefixWord ++ tailWord_5084686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084686).length < 2 ^ (prefixWord ++ tailWord_5084686).sum := by decide
  have hdescent : baseEnd_5084686 < baseStart_5084686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084752 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_5084752 : Nat := 118140960795 + 5084752 * 2 ^ 59
def prefixEnd_5084752 : Nat := 4983230072969 + 3 ^ 40 * 5084752 * 2
def baseEnd_5084752 : Nat := 870307261636798372705219

theorem tailTrace_5084752 : CollatzResearch.WordTrace tailWord_5084752 prefixEnd_5084752 870307261636798372705219 := by
  unfold tailWord_5084752
  simp only [CollatzResearch.WordTrace]
  refine ⟨92728070637409692674668255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123637427516546256899557673 92728070637409692674668255)
  ·
    refine ⟨139092105956114539012002383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92728070637409692674668255 139092105956114539012002383)
    ·
      refine ⟨208638158934171808518003575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139092105956114539012002383 208638158934171808518003575)
      ·
        refine ⟨312957238401257712777005363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208638158934171808518003575 312957238401257712777005363)
        ·
          refine ⟨469435857601886569165508045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312957238401257712777005363 469435857601886569165508045)
          ·
            refine ⟨176038446600707463437065517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469435857601886569165508045 176038446600707463437065517)
            ·
              refine ⟨66014417475265298788899569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176038446600707463437065517 66014417475265298788899569)
              ·
                refine ⟨49510813106448974091674677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66014417475265298788899569 49510813106448974091674677)
                ·
                  refine ⟨4641638728729591321094501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49510813106448974091674677 4641638728729591321094501)
                  ·
                    refine ⟨870307261636798372705219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641638728729591321094501 870307261636798372705219)
                    ·
                      rfl

theorem cell23_5084752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_5084752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084752 prefixEnd_5084752 := by exact prefixLift 5084752
  have htrace : WordTrace (prefixWord ++ tailWord_5084752) baseStart_5084752 baseEnd_5084752 := by
    simpa [prefixWord, tailWord_5084752, baseEnd_5084752] using wordTrace_append hprefix tailTrace_5084752
  have hstable : (prefixWord ++ tailWord_5084752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084752).length < 2 ^ (prefixWord ++ tailWord_5084752).sum := by decide
  have hdescent : baseEnd_5084752 < baseStart_5084752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084759 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_5084759 : Nat := 118140960795 + 5084759 * 2 ^ 59
def prefixEnd_5084759 : Nat := 4983230072969 + 3 ^ 40 * 5084759 * 2
def baseEnd_5084759 : Nat := 2610925379274976590728125

theorem tailTrace_5084759 : CollatzResearch.WordTrace tailWord_5084759 prefixEnd_5084759 2610925379274976590728125 := by
  unfold tailWord_5084759
  simp only [CollatzResearch.WordTrace]
  refine ⟨185456396585794025544841331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123637597723862683696560887 185456396585794025544841331)
  ·
    refine ⟨278184594878691038317261997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185456396585794025544841331 278184594878691038317261997)
    ·
      refine ⟨104319223079509139368973249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278184594878691038317261997 104319223079509139368973249)
      ·
        refine ⟨78239417309631854526729937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104319223079509139368973249 78239417309631854526729937)
        ·
          refine ⟨58679562982223890895047453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78239417309631854526729937 58679562982223890895047453)
          ·
            refine ⟨22004836118333959085642795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58679562982223890895047453 22004836118333959085642795)
            ·
              refine ⟨33007254177500938628464193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22004836118333959085642795 33007254177500938628464193)
              ·
                refine ⟨24755440633125703971348145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33007254177500938628464193 24755440633125703971348145)
                ·
                  refine ⟨18566580474844277978511109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24755440633125703971348145 18566580474844277978511109)
                  ·
                    refine ⟨3481233839033302120970833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18566580474844277978511109 3481233839033302120970833)
                    ·
                      refine ⟨2610925379274976590728125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481233839033302120970833 2610925379274976590728125)
                      ·
                        rfl

theorem cell23_5084759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_5084759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084759 prefixEnd_5084759 := by exact prefixLift 5084759
  have htrace : WordTrace (prefixWord ++ tailWord_5084759) baseStart_5084759 baseEnd_5084759 := by
    simpa [prefixWord, tailWord_5084759, baseEnd_5084759] using wordTrace_append hprefix tailTrace_5084759
  have hstable : (prefixWord ++ tailWord_5084759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084759).length < 2 ^ (prefixWord ++ tailWord_5084759).sum := by decide
  have hdescent : baseEnd_5084759 < baseStart_5084759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084769 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_5084769 : Nat := 118140960795 + 5084769 * 2 ^ 59
def prefixEnd_5084769 : Nat := 4983230072969 + 3 ^ 40 * 5084769 * 2
def baseEnd_5084769 : Nat := 870310171360507183867693

theorem tailTrace_5084769 : CollatzResearch.WordTrace tailWord_5084769 prefixEnd_5084769 870310171360507183867693 := by
  unfold tailWord_5084769
  simp only [CollatzResearch.WordTrace]
  refine ⟨185456761315757797252705361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123637840877171864835136907 185456761315757797252705361)
  ·
    refine ⟨139092570986818347939529021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185456761315757797252705361 139092570986818347939529021)
    ·
      refine ⟨52159714120056880477323383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139092570986818347939529021 52159714120056880477323383)
      ·
        refine ⟨78239571180085320715985075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52159714120056880477323383 78239571180085320715985075)
        ·
          refine ⟨117359356770127981073977613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78239571180085320715985075 117359356770127981073977613)
          ·
            refine ⟨44009758788797992902741605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117359356770127981073977613 44009758788797992902741605)
            ·
              refine ⟨8251829772899623669264051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44009758788797992902741605 8251829772899623669264051)
              ·
                refine ⟨12377744659349435503896077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251829772899623669264051 12377744659349435503896077)
                ·
                  refine ⟨4641654247256038313961029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12377744659349435503896077 4641654247256038313961029)
                  ·
                    refine ⟨870310171360507183867693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641654247256038313961029 870310171360507183867693)
                    ·
                      rfl

theorem cell23_5084769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_5084769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084769 prefixEnd_5084769 := by exact prefixLift 5084769
  have htrace : WordTrace (prefixWord ++ tailWord_5084769) baseStart_5084769 baseEnd_5084769 := by
    simpa [prefixWord, tailWord_5084769, baseEnd_5084769] using wordTrace_append hprefix tailTrace_5084769
  have hstable : (prefixWord ++ tailWord_5084769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084769).length < 2 ^ (prefixWord ++ tailWord_5084769).sum := by decide
  have hdescent : baseEnd_5084769 < baseStart_5084769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084776 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5084776 : Nat := 118140960795 + 5084776 * 2 ^ 59
def prefixEnd_5084776 : Nat := 4983230072969 + 3 ^ 40 * 5084776 * 2
def baseEnd_5084776 : Nat := 2610934108446103024215547

theorem tailTrace_5084776 : CollatzResearch.WordTrace tailWord_5084776 prefixEnd_5084776 2610934108446103024215547 := by
  unfold tailWord_5084776
  simp only [CollatzResearch.WordTrace]
  refine ⟨92728508313366218724105091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123638011084488291632140121 92728508313366218724105091)
  ·
    refine ⟨139092762470049328086157637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92728508313366218724105091 139092762470049328086157637)
    ·
      refine ⟨26079892963134249016154557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139092762470049328086157637 26079892963134249016154557)
      ·
        refine ⟨9779959861175343381057959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26079892963134249016154557 9779959861175343381057959)
        ·
          refine ⟨14669939791763015071586939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9779959861175343381057959 14669939791763015071586939)
          ·
            refine ⟨22004909687644522607380409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14669939791763015071586939 22004909687644522607380409)
            ·
              refine ⟨16503682265733391955535307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22004909687644522607380409 16503682265733391955535307)
              ·
                refine ⟨24755523398600087933302961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16503682265733391955535307 24755523398600087933302961)
                ·
                  refine ⟨18566642548950065949977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24755523398600087933302961 18566642548950065949977221)
                  ·
                    refine ⟨3481245477928137365620729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18566642548950065949977221 3481245477928137365620729)
                    ·
                      refine ⟨2610934108446103024215547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481245477928137365620729 2610934108446103024215547)
                      ·
                        rfl

theorem cell23_5084776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5084776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084776 prefixEnd_5084776 := by exact prefixLift 5084776
  have htrace : WordTrace (prefixWord ++ tailWord_5084776) baseStart_5084776 baseEnd_5084776 := by
    simpa [prefixWord, tailWord_5084776, baseEnd_5084776] using wordTrace_append hprefix tailTrace_5084776
  have hstable : (prefixWord ++ tailWord_5084776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084776).length < 2 ^ (prefixWord ++ tailWord_5084776).sum := by decide
  have hdescent : baseEnd_5084776 < baseStart_5084776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084809 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_5084809 : Nat := 118140960795 + 5084809 * 2 ^ 59
def prefixEnd_5084809 : Nat := 4983230072969 + 3 ^ 40 * 5084809 * 2
def baseEnd_5084809 : Nat := 2610951053307701395102895

theorem tailTrace_5084809 : CollatzResearch.WordTrace tailWord_5084809 prefixEnd_5084809 2610951053307701395102895 := by
  unfold tailWord_5084809
  simp only [CollatzResearch.WordTrace]
  refine ⟨185458220235612884084161481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123638813490408589389440987 185458220235612884084161481)
  ·
    refine ⟨139093665176709663063121111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185458220235612884084161481 139093665176709663063121111)
    ·
      refine ⟨208640497765064494594681667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139093665176709663063121111 208640497765064494594681667)
      ·
        refine ⟨312960746647596741892022501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208640497765064494594681667 312960746647596741892022501)
        ·
          refine ⟨58680139996424389104754219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312960746647596741892022501 58680139996424389104754219)
          ·
            refine ⟨88020209994636583657131329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58680139996424389104754219 88020209994636583657131329)
            ·
              refine ⟨66015157495977437742848497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88020209994636583657131329 66015157495977437742848497)
              ·
                refine ⟨49511368121983078307136373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66015157495977437742848497 49511368121983078307136373)
                ·
                  refine ⟨4641690761435913591294035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49511368121983078307136373 4641690761435913591294035)
                  ·
                    refine ⟨6962536142153870386941053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641690761435913591294035 6962536142153870386941053)
                    ·
                      refine ⟨2610951053307701395102895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6962536142153870386941053 2610951053307701395102895)
                      ·
                        rfl

theorem cell23_5084809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_5084809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084809 prefixEnd_5084809 := by exact prefixLift 5084809
  have htrace : WordTrace (prefixWord ++ tailWord_5084809) baseStart_5084809 baseEnd_5084809 := by
    simpa [prefixWord, tailWord_5084809, baseEnd_5084809] using wordTrace_append hprefix tailTrace_5084809
  have hstable : (prefixWord ++ tailWord_5084809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084809).length < 2 ^ (prefixWord ++ tailWord_5084809).sum := by decide
  have hdescent : baseEnd_5084809 < baseStart_5084809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084820 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5084820 : Nat := 118140960795 + 5084820 * 2 ^ 59
def prefixEnd_5084820 : Nat := 4983230072969 + 3 ^ 40 * 5084820 * 2
def baseEnd_5084820 : Nat := 870318900531633617355115

theorem tailTrace_5084820 : CollatzResearch.WordTrace tailWord_5084820 prefixEnd_5084820 870318900531633617355115 := by
  unfold tailWord_5084820
  simp only [CollatzResearch.WordTrace]
  refine ⟨92729310719286516481405957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123639080959048688641874609 92729310719286516481405957)
  ·
    refine ⟨17386745759866221840263617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92729310719286516481405957 17386745759866221840263617)
    ·
      refine ⟨13040059319899666380197713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17386745759866221840263617 13040059319899666380197713)
      ·
        refine ⟨9780044489924749785148285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13040059319899666380197713 9780044489924749785148285)
        ·
          refine ⟨3667516683721781169430607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9780044489924749785148285 3667516683721781169430607)
          ·
            refine ⟨5501275025582671754145911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667516683721781169430607 5501275025582671754145911)
            ·
              refine ⟨8251912538374007631218867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501275025582671754145911 8251912538374007631218867)
              ·
                refine ⟨12377868807561011446828301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251912538374007631218867 12377868807561011446828301)
                ·
                  refine ⟨4641700802835379292560613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12377868807561011446828301 4641700802835379292560613)
                  ·
                    refine ⟨870318900531633617355115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641700802835379292560613 870318900531633617355115)
                    ·
                      rfl

theorem cell23_5084820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5084820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084820 prefixEnd_5084820 := by exact prefixLift 5084820
  have htrace : WordTrace (prefixWord ++ tailWord_5084820) baseStart_5084820 baseEnd_5084820 := by
    simpa [prefixWord, tailWord_5084820, baseEnd_5084820] using wordTrace_append hprefix tailTrace_5084820
  have hstable : (prefixWord ++ tailWord_5084820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084820).length < 2 ^ (prefixWord ++ tailWord_5084820).sum := by decide
  have hdescent : baseEnd_5084820 < baseStart_5084820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084877 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5084877 : Nat := 118140960795 + 5084877 * 2 ^ 59
def prefixEnd_5084877 : Nat := 4983230072969 + 3 ^ 40 * 5084877 * 2
def baseEnd_5084877 : Nat := 2610985969992207129052583

theorem tailTrace_5084877 : CollatzResearch.WordTrace tailWord_5084877 prefixEnd_5084877 2610985969992207129052583 := by
  unfold tailWord_5084877
  simp only [CollatzResearch.WordTrace]
  refine ⟨185460700399366531697636885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123640466932911021131757923 185460700399366531697636885)
  ·
    refine ⟨8693470331220306173326729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185460700399366531697636885 8693470331220306173326729)
    ·
      refine ⟨6520102748415229629995047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8693470331220306173326729 6520102748415229629995047)
      ·
        refine ⟨9780154122622844444992571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6520102748415229629995047 9780154122622844444992571)
        ·
          refine ⟨14670231183934266667488857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9780154122622844444992571 14670231183934266667488857)
          ·
            refine ⟨11002673387950700000616643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14670231183934266667488857 11002673387950700000616643)
            ·
              refine ⟨16504010081926050000924965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002673387950700000616643 16504010081926050000924965)
              ·
                refine ⟨3094501890361134375173431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16504010081926050000924965 3094501890361134375173431)
                ·
                  refine ⟨4641752835541701562760147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094501890361134375173431 4641752835541701562760147)
                  ·
                    refine ⟨6962629253312552344140221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641752835541701562760147 6962629253312552344140221)
                    ·
                      refine ⟨2610985969992207129052583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6962629253312552344140221 2610985969992207129052583)
                      ·
                        rfl

theorem cell23_5084877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5084877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084877 prefixEnd_5084877 := by exact prefixLift 5084877
  have htrace : WordTrace (prefixWord ++ tailWord_5084877) baseStart_5084877 baseEnd_5084877 := by
    simpa [prefixWord, tailWord_5084877, baseEnd_5084877] using wordTrace_append hprefix tailTrace_5084877
  have hstable : (prefixWord ++ tailWord_5084877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084877).length < 2 ^ (prefixWord ++ tailWord_5084877).sum := by decide
  have hdescent : baseEnd_5084877 < baseStart_5084877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084889 : List Nat := [1, 2, 1, 2, 3, 5, 1, 8]
def baseStart_5084889 : Nat := 118140960795 + 5084889 * 2 ^ 59
def prefixEnd_5084889 : Nat := 4983230072969 + 3 ^ 40 * 5084889 * 2
def baseEnd_5084889 : Nat := 96703412287409669707501

theorem tailTrace_5084889 : CollatzResearch.WordTrace tailWord_5084889 prefixEnd_5084889 96703412287409669707501 := by
  unfold tailWord_5084889
  simp only [CollatzResearch.WordTrace]
  refine ⟨185461138075323057747073721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123640758716882038498049147 185461138075323057747073721)
  ·
    refine ⟨139095853556492293310305291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185461138075323057747073721 139095853556492293310305291)
    ·
      refine ⟨208643780334738439965457937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139095853556492293310305291 208643780334738439965457937)
      ·
        refine ⟨156482835251053829974093453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208643780334738439965457937 156482835251053829974093453)
        ·
          refine ⟨58681063219145186240285045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156482835251053829974093453 58681063219145186240285045)
          ·
            refine ⟨5501349676794861210026723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58681063219145186240285045 5501349676794861210026723)
            ·
              refine ⟨8252024515192291815040085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501349676794861210026723 8252024515192291815040085)
              ·
                refine ⟨96703412287409669707501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8252024515192291815040085 96703412287409669707501)
                ·
                  rfl

theorem cell23_5084889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 8].length) (baseStart_5084889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084889 prefixEnd_5084889 := by exact prefixLift 5084889
  have htrace : WordTrace (prefixWord ++ tailWord_5084889) baseStart_5084889 baseEnd_5084889 := by
    simpa [prefixWord, tailWord_5084889, baseEnd_5084889] using wordTrace_append hprefix tailTrace_5084889
  have hstable : (prefixWord ++ tailWord_5084889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084889).length < 2 ^ (prefixWord ++ tailWord_5084889).sum := by decide
  have hdescent : baseEnd_5084889 < baseStart_5084889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084893 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_5084893 : Nat := 118140960795 + 5084893 * 2 ^ 59
def prefixEnd_5084893 : Nat := 4983230072969 + 3 ^ 40 * 5084893 * 2
def baseEnd_5084893 : Nat := 870331395227559688817503

theorem tailTrace_5084893 : CollatzResearch.WordTrace tailWord_5084893 prefixEnd_5084893 870331395227559688817503 := by
  unfold tailWord_5084893
  simp only [CollatzResearch.WordTrace]
  refine ⟨185461283967308566430219333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123640855978205710953479555 185461283967308566430219333)
  ·
    refine ⟨34773990743870356205666125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185461283967308566430219333 34773990743870356205666125)
    ·
      refine ⟨13040246528951383577124797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34773990743870356205666125 13040246528951383577124797)
      ·
        refine ⟨4890092448356768841421799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13040246528951383577124797 4890092448356768841421799)
        ·
          refine ⟨7335138672535153262132699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890092448356768841421799 7335138672535153262132699)
          ·
            refine ⟨11002708008802729893199049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335138672535153262132699 11002708008802729893199049)
            ·
              refine ⟨8252031006602047419899287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11002708008802729893199049 8252031006602047419899287)
              ·
                refine ⟨12378046509903071129848931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8252031006602047419899287 12378046509903071129848931)
                ·
                  refine ⟨18567069764854606694773397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12378046509903071129848931 18567069764854606694773397)
                  ·
                    refine ⟨870331395227559688817503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18567069764854606694773397 870331395227559688817503)
                    ·
                      rfl

theorem cell23_5084893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_5084893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084893 prefixEnd_5084893 := by exact prefixLift 5084893
  have htrace : WordTrace (prefixWord ++ tailWord_5084893) baseStart_5084893 baseEnd_5084893 := by
    simpa [prefixWord, tailWord_5084893, baseEnd_5084893] using wordTrace_append hprefix tailTrace_5084893
  have hstable : (prefixWord ++ tailWord_5084893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084893).length < 2 ^ (prefixWord ++ tailWord_5084893).sum := by decide
  have hdescent : baseEnd_5084893 < baseStart_5084893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084949 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_5084949 : Nat := 118140960795 + 5084949 * 2 ^ 59
def prefixEnd_5084949 : Nat := 4983230072969 + 3 ^ 40 * 5084949 * 2
def baseEnd_5084949 : Nat := 870340980199776949117417

theorem tailTrace_5084949 : CollatzResearch.WordTrace tailWord_5084949 prefixEnd_5084949 870340980199776949117417 := by
  unfold tailWord_5084949
  simp only [CollatzResearch.WordTrace]
  refine ⟨185463326455105687994257901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123642217636737125329505267 185463326455105687994257901)
  ·
    refine ⟨69548747420664632997846713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185463326455105687994257901 69548747420664632997846713)
    ·
      refine ⟨52161560565498474748385035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69548747420664632997846713 52161560565498474748385035)
      ·
        refine ⟨78242340848247712122577553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52161560565498474748385035 78242340848247712122577553)
        ·
          refine ⟨58681755636185784091933165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78242340848247712122577553 58681755636185784091933165)
          ·
            refine ⟨22005658363569669034474937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58681755636185784091933165 22005658363569669034474937)
            ·
              refine ⟨16504243772677251775856203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22005658363569669034474937 16504243772677251775856203)
              ·
                refine ⟨24756365659015877663784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16504243772677251775856203 24756365659015877663784305)
                ·
                  refine ⟨18567274244261908247838229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24756365659015877663784305 18567274244261908247838229)
                  ·
                    refine ⟨870340980199776949117417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18567274244261908247838229 870340980199776949117417)
                    ·
                      rfl

theorem cell23_5084949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_5084949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084949 prefixEnd_5084949 := by exact prefixLift 5084949
  have htrace : WordTrace (prefixWord ++ tailWord_5084949) baseStart_5084949 baseEnd_5084949 := by
    simpa [prefixWord, tailWord_5084949, baseEnd_5084949] using wordTrace_append hprefix tailTrace_5084949
  have hstable : (prefixWord ++ tailWord_5084949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084949).length < 2 ^ (prefixWord ++ tailWord_5084949).sum := by decide
  have hdescent : baseEnd_5084949 < baseStart_5084949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084959 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5084959 : Nat := 118140960795 + 5084959 * 2 ^ 59
def prefixEnd_5084959 : Nat := 4983230072969 + 3 ^ 40 * 5084959 * 2
def baseEnd_5084959 : Nat := 2611028075405875808227205

theorem tailTrace_5084959 : CollatzResearch.WordTrace tailWord_5084959 prefixEnd_5084959 2611028075405875808227205 := by
  unfold tailWord_5084959
  simp only [CollatzResearch.WordTrace]
  refine ⟨185463691185069459702121931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123642460790046306468081287 185463691185069459702121931)
  ·
    refine ⟨278195536777604189553182897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185463691185069459702121931 278195536777604189553182897)
    ·
      refine ⟨208646652583203142164887173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278195536777604189553182897 208646652583203142164887173)
      ·
        refine ⟨39121247359350589155916345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208646652583203142164887173 39121247359350589155916345)
        ·
          refine ⟨29340935519512941866937259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39121247359350589155916345 29340935519512941866937259)
          ·
            refine ⟨44011403279269412800405889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29340935519512941866937259 44011403279269412800405889)
            ·
              refine ⟨33008552459452059600304417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44011403279269412800405889 33008552459452059600304417)
              ·
                refine ⟨24756414344589044700228313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33008552459452059600304417 24756414344589044700228313)
                ·
                  refine ⟨18567310758441783525171235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24756414344589044700228313 18567310758441783525171235)
                  ·
                    refine ⟨27850966137662675287756853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18567310758441783525171235 27850966137662675287756853)
                    ·
                      refine ⟨2611028075405875808227205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27850966137662675287756853 2611028075405875808227205)
                      ·
                        rfl

theorem cell23_5084959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5084959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084959 prefixEnd_5084959 := by exact prefixLift 5084959
  have htrace : WordTrace (prefixWord ++ tailWord_5084959) baseStart_5084959 baseEnd_5084959 := by
    simpa [prefixWord, tailWord_5084959, baseEnd_5084959] using wordTrace_append hprefix tailTrace_5084959
  have hstable : (prefixWord ++ tailWord_5084959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084959).length < 2 ^ (prefixWord ++ tailWord_5084959).sum := by decide
  have hdescent : baseEnd_5084959 < baseStart_5084959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5084990 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5084990 : Nat := 118140960795 + 5084990 * 2 ^ 59
def prefixEnd_5084990 : Nat := 4983230072969 + 3 ^ 40 * 5084990 * 2
def baseEnd_5084990 : Nat := 2611043993306165186939563

theorem tailTrace_5084990 : CollatzResearch.WordTrace tailWord_5084990 prefixEnd_5084990 2611043993306165186939563 := by
  unfold tailWord_5084990
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183102730994643999562553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123643214565304767997666949 23183102730994643999562553)
  ·
    refine ⟨17387327048245982999671915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23183102730994643999562553 17387327048245982999671915)
    ·
      refine ⟨26080990572368974499507873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17387327048245982999671915 26080990572368974499507873)
      ·
        refine ⟨19560742929276730874630905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26080990572368974499507873 19560742929276730874630905)
        ·
          refine ⟨14670557196957548155973179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19560742929276730874630905 14670557196957548155973179)
          ·
            refine ⟨22005835795436322233959769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14670557196957548155973179 22005835795436322233959769)
            ·
              refine ⟨16504376846577241675469827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22005835795436322233959769 16504376846577241675469827)
              ·
                refine ⟨24756565269865862513204741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16504376846577241675469827 24756565269865862513204741)
                ·
                  refine ⟨4641855988099849221225889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24756565269865862513204741 4641855988099849221225889)
                  ·
                    refine ⟨3481391991074886915919417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641855988099849221225889 3481391991074886915919417)
                    ·
                      refine ⟨2611043993306165186939563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481391991074886915919417 2611043993306165186939563)
                      ·
                        rfl

theorem cell23_5084990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5084990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5084990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5084990 prefixEnd_5084990 := by exact prefixLift 5084990
  have htrace : WordTrace (prefixWord ++ tailWord_5084990) baseStart_5084990 baseEnd_5084990 := by
    simpa [prefixWord, tailWord_5084990, baseEnd_5084990] using wordTrace_append hprefix tailTrace_5084990
  have hstable : (prefixWord ++ tailWord_5084990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5084990).length < 2 ^ (prefixWord ++ tailWord_5084990).sum := by decide
  have hdescent : baseEnd_5084990 < baseStart_5084990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5084990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085049 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_5085049 : Nat := 118140960795 + 5085049 * 2 ^ 59
def prefixEnd_5085049 : Nat := 4983230072969 + 3 ^ 40 * 5085049 * 2
def baseEnd_5085049 : Nat := 2611074288664780456101791

theorem tailTrace_5085049 : CollatzResearch.WordTrace tailWord_5085049 prefixEnd_5085049 2611074288664780456101791 := by
  unfold tailWord_5085049
  simp only [CollatzResearch.WordTrace]
  refine ⟨185466973754743405072898201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123644649169828936715265467 185466973754743405072898201)
  ·
    refine ⟨139100230316057553804673651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185466973754743405072898201 139100230316057553804673651)
    ·
      refine ⟨208650345474086330707010477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139100230316057553804673651 208650345474086330707010477)
      ·
        refine ⟨78243879552782374015128929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208650345474086330707010477 78243879552782374015128929)
        ·
          refine ⟨58682909664586780511346697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78243879552782374015128929 58682909664586780511346697)
          ·
            refine ⟨44012182248440085383510023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58682909664586780511346697 44012182248440085383510023)
            ·
              refine ⟨66018273372660128075265035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44012182248440085383510023 66018273372660128075265035)
              ·
                refine ⟨99027410058990192112897553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66018273372660128075265035 99027410058990192112897553)
                ·
                  refine ⟨74270557544242644084673165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99027410058990192112897553 74270557544242644084673165)
                  ·
                    refine ⟨27851459079090991531752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74270557544242644084673165 27851459079090991531752437)
                    ·
                      refine ⟨2611074288664780456101791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27851459079090991531752437 2611074288664780456101791)
                      ·
                        rfl

theorem cell23_5085049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_5085049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085049 prefixEnd_5085049 := by exact prefixLift 5085049
  have htrace : WordTrace (prefixWord ++ tailWord_5085049) baseStart_5085049 baseEnd_5085049 := by
    simpa [prefixWord, tailWord_5085049, baseEnd_5085049] using wordTrace_append hprefix tailTrace_5085049
  have hstable : (prefixWord ++ tailWord_5085049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085049).length < 2 ^ (prefixWord ++ tailWord_5085049).sum := by decide
  have hdescent : baseEnd_5085049 < baseStart_5085049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085056 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_5085056 : Nat := 118140960795 + 5085056 * 2 ^ 59
def prefixEnd_5085056 : Nat := 4983230072969 + 3 ^ 40 * 5085056 * 2
def baseEnd_5085056 : Nat := 870359294343120642904753

theorem tailTrace_5085056 : CollatzResearch.WordTrace tailWord_5085056 prefixEnd_5085056 870359294343120642904753 := by
  unfold tailWord_5085056
  simp only [CollatzResearch.WordTrace]
  refine ⟨92733614532859022634201511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123644819377145363512268681 92733614532859022634201511)
  ·
    refine ⟨139100421799288533951302267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92733614532859022634201511 139100421799288533951302267)
    ·
      refine ⟨208650632698932800926953401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139100421799288533951302267 208650632698932800926953401)
      ·
        refine ⟨156487974524199600695215051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208650632698932800926953401 156487974524199600695215051)
        ·
          refine ⟨234731961786299401042822577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156487974524199600695215051 234731961786299401042822577)
          ·
            refine ⟨176048971339724550782116933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234731961786299401042822577 176048971339724550782116933)
            ·
              refine ⟨33009182126198353271646925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176048971339724550782116933 33009182126198353271646925)
              ·
                refine ⟨12378443297324382476867597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33009182126198353271646925 12378443297324382476867597)
                ·
                  refine ⟨4641916236496643428825349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12378443297324382476867597 4641916236496643428825349)
                  ·
                    refine ⟨870359294343120642904753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641916236496643428825349 870359294343120642904753)
                    ·
                      rfl

theorem cell23_5085056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_5085056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085056 prefixEnd_5085056 := by exact prefixLift 5085056
  have htrace : WordTrace (prefixWord ++ tailWord_5085056) baseStart_5085056 baseEnd_5085056 := by
    simpa [prefixWord, tailWord_5085056, baseEnd_5085056] using wordTrace_append hprefix tailTrace_5085056
  have hstable : (prefixWord ++ tailWord_5085056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085056).length < 2 ^ (prefixWord ++ tailWord_5085056).sum := by decide
  have hdescent : baseEnd_5085056 < baseStart_5085056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085136 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_5085136 : Nat := 118140960795 + 5085136 * 2 ^ 59
def prefixEnd_5085136 : Nat := 4983230072969 + 3 ^ 40 * 5085136 * 2
def baseEnd_5085136 : Nat := 2611118961481721615713891

theorem tailTrace_5085136 : CollatzResearch.WordTrace tailWord_5085136 prefixEnd_5085136 2611118961481721615713891 := by
  unfold tailWord_5085136
  simp only [CollatzResearch.WordTrace]
  refine ⟨92735073452714109465657631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123646764603618812620876841 92735073452714109465657631)
  ·
    refine ⟨139102610179071164198486447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92735073452714109465657631 139102610179071164198486447)
    ·
      refine ⟨208653915268606746297729671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139102610179071164198486447 208653915268606746297729671)
      ·
        refine ⟨312980872902910119446594507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208653915268606746297729671 312980872902910119446594507)
        ·
          refine ⟨469471309354365179169891761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312980872902910119446594507 469471309354365179169891761)
          ·
            refine ⟨352103482015773884377418821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469471309354365179169891761 352103482015773884377418821)
            ·
              refine ⟨66019402877957603320766029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 352103482015773884377418821 66019402877957603320766029)
              ·
                refine ⟨24757276079234101245287261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66019402877957603320766029 24757276079234101245287261)
                ·
                  refine ⟨9283978529712787966982723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24757276079234101245287261 9283978529712787966982723)
                  ·
                    refine ⟨13925967794569181950474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9283978529712787966982723 13925967794569181950474085)
                    ·
                      refine ⟨2611118961481721615713891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13925967794569181950474085 2611118961481721615713891)
                      ·
                        rfl

theorem cell23_5085136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_5085136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085136 prefixEnd_5085136 := by exact prefixLift 5085136
  have htrace : WordTrace (prefixWord ++ tailWord_5085136) baseStart_5085136 baseEnd_5085136 := by
    simpa [prefixWord, tailWord_5085136, baseEnd_5085136] using wordTrace_append hprefix tailTrace_5085136
  have hstable : (prefixWord ++ tailWord_5085136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085136).length < 2 ^ (prefixWord ++ tailWord_5085136).sum := by decide
  have hdescent : baseEnd_5085136 < baseStart_5085136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085140 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5085140 : Nat := 118140960795 + 5085140 * 2 ^ 59
def prefixEnd_5085140 : Nat := 4983230072969 + 3 ^ 40 * 5085140 * 2
def baseEnd_5085140 : Nat := 2611121015404339600063873

theorem tailTrace_5085140 : CollatzResearch.WordTrace tailWord_5085140 prefixEnd_5085140 2611121015404339600063873 := by
  unfold tailWord_5085140
  simp only [CollatzResearch.WordTrace]
  refine ⟨92735146398706863807230437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123646861864942485076307249 92735146398706863807230437)
  ·
    refine ⟨17387839949757536963855707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92735146398706863807230437 17387839949757536963855707)
    ·
      refine ⟨26081759924636305445783561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17387839949757536963855707 26081759924636305445783561)
      ·
        refine ⟨19561319943477229084337671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26081759924636305445783561 19561319943477229084337671)
        ·
          refine ⟨29341979915215843626506507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19561319943477229084337671 29341979915215843626506507)
          ·
            refine ⟨44012969872823765439759761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29341979915215843626506507 44012969872823765439759761)
            ·
              refine ⟨33009727404617824079819821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44012969872823765439759761 33009727404617824079819821)
              ·
                refine ⟨12378647776731684029932433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33009727404617824079819821 12378647776731684029932433)
                ·
                  refine ⟨9283985832548763022449325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12378647776731684029932433 9283985832548763022449325)
                  ·
                    refine ⟨3481494687205786133418497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9283985832548763022449325 3481494687205786133418497)
                    ·
                      refine ⟨2611121015404339600063873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481494687205786133418497 2611121015404339600063873)
                      ·
                        rfl

theorem cell23_5085140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5085140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085140 prefixEnd_5085140 := by exact prefixLift 5085140
  have htrace : WordTrace (prefixWord ++ tailWord_5085140) baseStart_5085140 baseEnd_5085140 := by
    simpa [prefixWord, tailWord_5085140, baseEnd_5085140] using wordTrace_append hprefix tailTrace_5085140
  have hstable : (prefixWord ++ tailWord_5085140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085140).length < 2 ^ (prefixWord ++ tailWord_5085140).sum := by decide
  have hdescent : baseEnd_5085140 < baseStart_5085140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085153 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_5085153 : Nat := 118140960795 + 5085153 * 2 ^ 59
def prefixEnd_5085153 : Nat := 4983230072969 + 3 ^ 40 * 5085153 * 2
def baseEnd_5085153 : Nat := 2611127690652848049201313

theorem tailTrace_5085153 : CollatzResearch.WordTrace tailWord_5085153 prefixEnd_5085153 2611127690652848049201313 := by
  unfold tailWord_5085153
  simp only [CollatzResearch.WordTrace]
  refine ⟨185470766946366630834684113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123647177964244420556456075 185470766946366630834684113)
  ·
    refine ⟨139103075209774973126013085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185470766946366630834684113 139103075209774973126013085)
    ·
      refine ⟨52163653203665614922254907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139103075209774973126013085 52163653203665614922254907)
      ·
        refine ⟨78245479805498422383382361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52163653203665614922254907 78245479805498422383382361)
        ·
          refine ⟨58684109854123816787536771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78245479805498422383382361 58684109854123816787536771)
          ·
            refine ⟨88026164781185725181305157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58684109854123816787536771 88026164781185725181305157)
            ·
              refine ⟨16504905896472323471494717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88026164781185725181305157 16504905896472323471494717)
              ·
                refine ⟨6189339711177121301810519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16504905896472323471494717 6189339711177121301810519)
                ·
                  refine ⟨9284009566765681952715779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189339711177121301810519 9284009566765681952715779)
                  ·
                    refine ⟨13926014350148522929073669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9284009566765681952715779 13926014350148522929073669)
                    ·
                      refine ⟨2611127690652848049201313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13926014350148522929073669 2611127690652848049201313)
                      ·
                        rfl

theorem cell23_5085153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_5085153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085153 prefixEnd_5085153 := by exact prefixLift 5085153
  have htrace : WordTrace (prefixWord ++ tailWord_5085153) baseStart_5085153 baseEnd_5085153 := by
    simpa [prefixWord, tailWord_5085153, baseEnd_5085153] using wordTrace_append hprefix tailTrace_5085153
  have hstable : (prefixWord ++ tailWord_5085153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085153).length < 2 ^ (prefixWord ++ tailWord_5085153).sum := by decide
  have hdescent : baseEnd_5085153 < baseStart_5085153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085203 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 3]
def baseStart_5085203 : Nat := 118140960795 + 5085203 * 2 ^ 59
def prefixEnd_5085203 : Nat := 4983230072969 + 3 ^ 40 * 5085203 * 2
def baseEnd_5085203 : Nat := 2611153364685572853576083

theorem tailTrace_5085203 : CollatzResearch.WordTrace tailWord_5085203 prefixEnd_5085203 2611153364685572853576083 := by
  unfold tailWord_5085203
  simp only [CollatzResearch.WordTrace]
  refine ⟨185472590596185489374004263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123648393730790326249336175 185472590596185489374004263)
  ·
    refine ⟨278208885894278234061006395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185472590596185489374004263 278208885894278234061006395)
    ·
      refine ⟨417313328841417351091509593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278208885894278234061006395 417313328841417351091509593)
      ·
        refine ⟨312984996631063013318632195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417313328841417351091509593 312984996631063013318632195)
        ·
          refine ⟨469477494946594519977948293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312984996631063013318632195 469477494946594519977948293)
          ·
            refine ⟨88027030302486472495865305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 469477494946594519977948293 88027030302486472495865305)
            ·
              refine ⟨66020272726864854371898979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88027030302486472495865305 66020272726864854371898979)
              ·
                refine ⟨99030409090297281557848469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66020272726864854371898979 99030409090297281557848469)
                ·
                  refine ⟨4642050426107685073024147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99030409090297281557848469 4642050426107685073024147)
                  ·
                    refine ⟨6963075639161527609536221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642050426107685073024147 6963075639161527609536221)
                    ·
                      refine ⟨2611153364685572853576083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963075639161527609536221 2611153364685572853576083)
                      ·
                        rfl

theorem cell23_5085203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_5085203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085203 prefixEnd_5085203 := by exact prefixLift 5085203
  have htrace : WordTrace (prefixWord ++ tailWord_5085203) baseStart_5085203 baseEnd_5085203 := by
    simpa [prefixWord, tailWord_5085203, baseEnd_5085203] using wordTrace_append hprefix tailTrace_5085203
  have hstable : (prefixWord ++ tailWord_5085203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085203).length < 2 ^ (prefixWord ++ tailWord_5085203).sum := by decide
  have hdescent : baseEnd_5085203 < baseStart_5085203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085207 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5085207 : Nat := 118140960795 + 5085207 * 2 ^ 59
def prefixEnd_5085207 : Nat := 4983230072969 + 3 ^ 40 * 5085207 * 2
def baseEnd_5085207 : Nat := 2611155418608190837926065

theorem tailTrace_5085207 : CollatzResearch.WordTrace tailWord_5085207 prefixEnd_5085207 2611155418608190837926065 := by
  unfold tailWord_5085207
  simp only [CollatzResearch.WordTrace]
  refine ⟨185472736488170998057149875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123648490992113998704766583 185472736488170998057149875)
  ·
    refine ⟨278209104732256497085724813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185472736488170998057149875 278209104732256497085724813)
    ·
      refine ⟨104328414274596186407146805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278209104732256497085724813 104328414274596186407146805)
      ·
        refine ⟨9780788838243392475670013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104328414274596186407146805 9780788838243392475670013)
        ·
          refine ⟨3667795814341272178376255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9780788838243392475670013 3667795814341272178376255)
          ·
            refine ⟨5501693721511908267564383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667795814341272178376255 5501693721511908267564383)
            ·
              refine ⟨8252540582267862401346575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501693721511908267564383 8252540582267862401346575)
              ·
                refine ⟨12378810873401793602019863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8252540582267862401346575 12378810873401793602019863)
                ·
                  refine ⟨18568216310102690403029795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12378810873401793602019863 18568216310102690403029795)
                  ·
                    refine ⟨27852324465154035604544693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18568216310102690403029795 27852324465154035604544693)
                    ·
                      refine ⟨2611155418608190837926065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27852324465154035604544693 2611155418608190837926065)
                      ·
                        rfl

theorem cell23_5085207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5085207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085207 prefixEnd_5085207 := by exact prefixLift 5085207
  have htrace : WordTrace (prefixWord ++ tailWord_5085207) baseStart_5085207 baseEnd_5085207 := by
    simpa [prefixWord, tailWord_5085207, baseEnd_5085207] using wordTrace_append hprefix tailTrace_5085207
  have hstable : (prefixWord ++ tailWord_5085207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085207).length < 2 ^ (prefixWord ++ tailWord_5085207).sum := by decide
  have hdescent : baseEnd_5085207 < baseStart_5085207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085221 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_5085221 : Nat := 118140960795 + 5085221 * 2 ^ 59
def prefixEnd_5085221 : Nat := 4983230072969 + 3 ^ 40 * 5085221 * 2
def baseEnd_5085221 : Nat := 2611162607337353783151001

theorem tailTrace_5085221 : CollatzResearch.WordTrace tailWord_5085221 prefixEnd_5085221 2611162607337353783151001 := by
  unfold tailWord_5085221
  simp only [CollatzResearch.WordTrace]
  refine ⟨185473247110120278448159517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123648831406746852298773011 185473247110120278448159517)
  ·
    refine ⟨69552467666295104418059819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185473247110120278448159517 69552467666295104418059819)
    ·
      refine ⟨104328701499442656627089729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69552467666295104418059819 104328701499442656627089729)
      ·
        refine ⟨78246526124581992470317297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104328701499442656627089729 78246526124581992470317297)
        ·
          refine ⟨58684894593436494352737973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78246526124581992470317297 58684894593436494352737973)
          ·
            refine ⟨5501708868134671345569185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58684894593436494352737973 5501708868134671345569185)
            ·
              refine ⟨4126281651101003509176889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5501708868134671345569185 4126281651101003509176889)
              ·
                refine ⟨3094711238325752631882667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126281651101003509176889 3094711238325752631882667)
                ·
                  refine ⟨4642066857488628947824001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094711238325752631882667 4642066857488628947824001)
                  ·
                    refine ⟨3481550143116471710868001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4642066857488628947824001 3481550143116471710868001)
                    ·
                      refine ⟨2611162607337353783151001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481550143116471710868001 2611162607337353783151001)
                      ·
                        rfl

theorem cell23_5085221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_5085221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085221 prefixEnd_5085221 := by exact prefixLift 5085221
  have htrace : WordTrace (prefixWord ++ tailWord_5085221) baseStart_5085221 baseEnd_5085221 := by
    simpa [prefixWord, tailWord_5085221, baseEnd_5085221] using wordTrace_append hprefix tailTrace_5085221
  have hstable : (prefixWord ++ tailWord_5085221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085221).length < 2 ^ (prefixWord ++ tailWord_5085221).sum := by decide
  have hdescent : baseEnd_5085221 < baseStart_5085221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 4, 2]
def baseStart_5085243 : Nat := 118140960795 + 5085243 * 2 ^ 59
def prefixEnd_5085243 : Nat := 4983230072969 + 3 ^ 40 * 5085243 * 2
def baseEnd_5085243 : Nat := 2611173903911752697075899

theorem tailTrace_5085243 : CollatzResearch.WordTrace tailWord_5085243 prefixEnd_5085243 2611173903911752697075899 := by
  unfold tailWord_5085243
  simp only [CollatzResearch.WordTrace]
  refine ⟨185474049516040576205460383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123649366344027050803640255 185474049516040576205460383)
  ·
    refine ⟨278211074274060864308190575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185474049516040576205460383 278211074274060864308190575)
    ·
      refine ⟨417316611411091296462285863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278211074274060864308190575 417316611411091296462285863)
      ·
        refine ⟨625974917116636944693428795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417316611411091296462285863 625974917116636944693428795)
        ·
          refine ⟨938962375674955417040143193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625974917116636944693428795 938962375674955417040143193)
          ·
            refine ⟨704221781756216562780107395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938962375674955417040143193 704221781756216562780107395)
            ·
              refine ⟨1056332672634324844170161093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704221781756216562780107395 1056332672634324844170161093)
              ·
                refine ⟨198062376118935908281905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1056332672634324844170161093 198062376118935908281905205)
                ·
                  refine ⟨18568347761150241401428613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198062376118935908281905205 18568347761150241401428613)
                  ·
                    refine ⟨3481565205215670262767865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18568347761150241401428613 3481565205215670262767865)
                    ·
                      refine ⟨2611173903911752697075899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481565205215670262767865 2611173903911752697075899)
                      ·
                        rfl

theorem cell23_5085243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4, 2].length) (baseStart_5085243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085243 prefixEnd_5085243 := by exact prefixLift 5085243
  have htrace : WordTrace (prefixWord ++ tailWord_5085243) baseStart_5085243 baseEnd_5085243 := by
    simpa [prefixWord, tailWord_5085243, baseEnd_5085243] using wordTrace_append hprefix tailTrace_5085243
  have hstable : (prefixWord ++ tailWord_5085243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085243).length < 2 ^ (prefixWord ++ tailWord_5085243).sum := by decide
  have hdescent : baseEnd_5085243 < baseStart_5085243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085260 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5085260 : Nat := 118140960795 + 5085260 * 2 ^ 59
def prefixEnd_5085260 : Nat := 4983230072969 + 3 ^ 40 * 5085260 * 2
def baseEnd_5085260 : Nat := 2611182633082879130563321

theorem tailTrace_5085260 : CollatzResearch.WordTrace tailWord_5085260 prefixEnd_5085260 2611182633082879130563321 := by
  unfold tailWord_5085260
  simp only [CollatzResearch.WordTrace]
  refine ⟨92737334778489494054414617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123649779704652658739219489 92737334778489494054414617)
  ·
    refine ⟨69553001083867120540810963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92737334778489494054414617 69553001083867120540810963)
    ·
      refine ⟨104329501625800680811216445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69553001083867120540810963 104329501625800680811216445)
      ·
        refine ⟨39123563109675255304206167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104329501625800680811216445 39123563109675255304206167)
        ·
          refine ⟨58685344664512882956309251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39123563109675255304206167 58685344664512882956309251)
          ·
            refine ⟨88028016996769324434463877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58685344664512882956309251 88028016996769324434463877)
            ·
              refine ⟨16505253186894248331461977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88028016996769324434463877 16505253186894248331461977)
              ·
                refine ⟨12378939890170686248596483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16505253186894248331461977 12378939890170686248596483)
                ·
                  refine ⟨18568409835256029372894725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12378939890170686248596483 18568409835256029372894725)
                  ·
                    refine ⟨3481576844110505507417761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18568409835256029372894725 3481576844110505507417761)
                    ·
                      refine ⟨2611182633082879130563321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481576844110505507417761 2611182633082879130563321)
                      ·
                        rfl

theorem cell23_5085260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5085260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085260 prefixEnd_5085260 := by exact prefixLift 5085260
  have htrace : WordTrace (prefixWord ++ tailWord_5085260) baseStart_5085260 baseEnd_5085260 := by
    simpa [prefixWord, tailWord_5085260, baseEnd_5085260] using wordTrace_append hprefix tailTrace_5085260
  have hstable : (prefixWord ++ tailWord_5085260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085260).length < 2 ^ (prefixWord ++ tailWord_5085260).sum := by decide
  have hdescent : baseEnd_5085260 < baseStart_5085260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085317 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 5]
def baseStart_5085317 : Nat := 118140960795 + 5085317 * 2 ^ 59
def prefixEnd_5085317 : Nat := 4983230072969 + 3 ^ 40 * 5085317 * 2
def baseEnd_5085317 : Nat := 290134655720020600838951

theorem tailTrace_5085317 : CollatzResearch.WordTrace tailWord_5085317 prefixEnd_5085317 290134655720020600838951 := by
  unfold tailWord_5085317
  simp only [CollatzResearch.WordTrace]
  refine ⟨185476748517772486843654205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123651165678514991229102803 185476748517772486843654205)
  ·
    refine ⟨69553780694164682566370327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185476748517772486843654205 69553780694164682566370327)
    ·
      refine ⟨104330671041247023849555491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69553780694164682566370327 104330671041247023849555491)
      ·
        refine ⟨156496006561870535774333237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104330671041247023849555491 156496006561870535774333237)
        ·
          refine ⟨14671500615175362728843741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156496006561870535774333237 14671500615175362728843741)
          ·
            refine ⟨5501812730690761023316403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14671500615175362728843741 5501812730690761023316403)
            ·
              refine ⟨8252719096036141534974605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501812730690761023316403 8252719096036141534974605)
              ·
                refine ⟨3094769661013553075615477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8252719096036141534974605 3094769661013553075615477)
                ·
                  refine ⟨290134655720020600838951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3094769661013553075615477 290134655720020600838951)
                  ·
                    rfl

theorem cell23_5085317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_5085317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085317 prefixEnd_5085317 := by exact prefixLift 5085317
  have htrace : WordTrace (prefixWord ++ tailWord_5085317) baseStart_5085317 baseEnd_5085317 := by
    simpa [prefixWord, tailWord_5085317, baseEnd_5085317] using wordTrace_append hprefix tailTrace_5085317
  have hstable : (prefixWord ++ tailWord_5085317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085317).length < 2 ^ (prefixWord ++ tailWord_5085317).sum := by decide
  have hdescent : baseEnd_5085317 < baseStart_5085317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085330 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5085330 : Nat := 118140960795 + 5085330 * 2 ^ 59
def prefixEnd_5085330 : Nat := 4983230072969 + 3 ^ 40 * 5085330 * 2
def baseEnd_5085330 : Nat := 870406192242897952229333

theorem tailTrace_5085330 : CollatzResearch.WordTrace tailWord_5085330 prefixEnd_5085330 870406192242897952229333 := by
  unfold tailWord_5085330
  simp only [CollatzResearch.WordTrace]
  refine ⟨46369305666681347515969361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123651481777816926709251629 46369305666681347515969361)
  ·
    refine ⟨34776979250011010636977021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46369305666681347515969361 34776979250011010636977021)
    ·
      refine ⟨13041367218754128988866383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34776979250011010636977021 13041367218754128988866383)
      ·
        refine ⟨19562050828131193483299575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13041367218754128988866383 19562050828131193483299575)
        ·
          refine ⟨29343076242196790224949363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19562050828131193483299575 29343076242196790224949363)
          ·
            refine ⟨44014614363295185337424045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29343076242196790224949363 44014614363295185337424045)
            ·
              refine ⟨16505480386235694501534017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44014614363295185337424045 16505480386235694501534017)
              ·
                refine ⟨12379110289676770876150513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16505480386235694501534017 12379110289676770876150513)
                ·
                  refine ⟨9284332717257578157112885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12379110289676770876150513 9284332717257578157112885)
                  ·
                    refine ⟨870406192242897952229333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9284332717257578157112885 870406192242897952229333)
                    ·
                      rfl

theorem cell23_5085330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5085330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085330 prefixEnd_5085330 := by exact prefixLift 5085330
  have htrace : WordTrace (prefixWord ++ tailWord_5085330) baseStart_5085330 baseEnd_5085330 := by
    simpa [prefixWord, tailWord_5085330, baseEnd_5085330] using wordTrace_append hprefix tailTrace_5085330
  have hstable : (prefixWord ++ tailWord_5085330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085330).length < 2 ^ (prefixWord ++ tailWord_5085330).sum := by decide
  have hdescent : baseEnd_5085330 < baseStart_5085330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085370 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_5085370 : Nat := 118140960795 + 5085370 * 2 ^ 59
def prefixEnd_5085370 : Nat := 4983230072969 + 3 ^ 40 * 5085370 * 2
def baseEnd_5085370 : Nat := 2611239115954873700187815

theorem tailTrace_5085370 : CollatzResearch.WordTrace tailWord_5085370 prefixEnd_5085370 2611239115954873700187815 := by
  unfold tailWord_5085370
  simp only [CollatzResearch.WordTrace]
  refine ⟨46369670396645119223833391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123652454391053651263555709 46369670396645119223833391)
  ·
    refine ⟨69554505594967678835750087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46369670396645119223833391 69554505594967678835750087)
    ·
      refine ⟨104331758392451518253625131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69554505594967678835750087 104331758392451518253625131)
      ·
        refine ⟨156497637588677277380437697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104331758392451518253625131 156497637588677277380437697)
        ·
          refine ⟨117373228191507958035328273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156497637588677277380437697 117373228191507958035328273)
          ·
            refine ⟨88029921143630968526496205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117373228191507958035328273 88029921143630968526496205)
            ·
              refine ⟨33011220428861613197436077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88029921143630968526496205 33011220428861613197436077)
              ·
                refine ⟨12379207660823104949038529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33011220428861613197436077 12379207660823104949038529)
                ·
                  refine ⟨9284405745617328711778897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12379207660823104949038529 9284405745617328711778897)
                  ·
                    refine ⟨6963304309212996533834173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9284405745617328711778897 6963304309212996533834173)
                    ·
                      refine ⟨2611239115954873700187815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963304309212996533834173 2611239115954873700187815)
                      ·
                        rfl

theorem cell23_5085370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_5085370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085370 prefixEnd_5085370 := by exact prefixLift 5085370
  have htrace : WordTrace (prefixWord ++ tailWord_5085370) baseStart_5085370 baseEnd_5085370 := by
    simpa [prefixWord, tailWord_5085370, baseEnd_5085370] using wordTrace_append hprefix tailTrace_5085370
  have hstable : (prefixWord ++ tailWord_5085370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085370).length < 2 ^ (prefixWord ++ tailWord_5085370).sum := by decide
  have hdescent : baseEnd_5085370 < baseStart_5085370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085390 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_5085390 : Nat := 118140960795 + 5085390 * 2 ^ 59
def prefixEnd_5085390 : Nat := 4983230072969 + 3 ^ 40 * 5085390 * 2
def baseEnd_5085390 : Nat := 290138820618662624659747

theorem tailTrace_5085390 : CollatzResearch.WordTrace tailWord_5085390 prefixEnd_5085390 290138820618662624659747 := by
  unfold tailWord_5085390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184926380813502538882703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123652940697672013540707749 23184926380813502538882703)
  ·
    refine ⟨34777389571220253808324055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23184926380813502538882703 34777389571220253808324055)
    ·
      refine ⟨52166084356830380712486083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34777389571220253808324055 52166084356830380712486083)
      ·
        refine ⟨78249126535245571068729125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52166084356830380712486083 78249126535245571068729125)
        ·
          refine ⟨14671711225358544575386711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78249126535245571068729125 14671711225358544575386711)
          ·
            refine ⟨22007566838037816863080067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14671711225358544575386711 22007566838037816863080067)
            ·
              refine ⟨33011350257056725294620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22007566838037816863080067 33011350257056725294620101)
              ·
                refine ⟨6189628173198135992741269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33011350257056725294620101 6189628173198135992741269)
                ·
                  refine ⟨290138820618662624659747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6189628173198135992741269 290138820618662624659747)
                  ·
                    rfl

theorem cell23_5085390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_5085390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085390 prefixEnd_5085390 := by exact prefixLift 5085390
  have htrace : WordTrace (prefixWord ++ tailWord_5085390) baseStart_5085390 baseEnd_5085390 := by
    simpa [prefixWord, tailWord_5085390, baseEnd_5085390] using wordTrace_append hprefix tailTrace_5085390
  have hstable : (prefixWord ++ tailWord_5085390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085390).length < 2 ^ (prefixWord ++ tailWord_5085390).sum := by decide
  have hdescent : baseEnd_5085390 < baseStart_5085390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085394 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_5085394 : Nat := 118140960795 + 5085394 * 2 ^ 59
def prefixEnd_5085394 : Nat := 4983230072969 + 3 ^ 40 * 5085394 * 2
def baseEnd_5085394 : Nat := 870417146496860535429235

theorem tailTrace_5085394 : CollatzResearch.WordTrace tailWord_5085394 prefixEnd_5085394 870417146496860535429235 := by
  unfold tailWord_5085394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46369889234623382248551809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123653037958995685996138157 46369889234623382248551809)
  ·
    refine ⟨34777416925967536686413857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46369889234623382248551809 34777416925967536686413857)
    ·
      refine ⟨26083062694475652514810393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34777416925967536686413857 26083062694475652514810393)
      ·
        refine ⟨19562297020856739386107795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26083062694475652514810393 19562297020856739386107795)
        ·
          refine ⟨29343445531285109079161693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19562297020856739386107795 29343445531285109079161693)
          ·
            refine ⟨11003792074231915904685635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29343445531285109079161693 11003792074231915904685635)
            ·
              refine ⟨16505688111347873857028453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11003792074231915904685635 16505688111347873857028453)
              ·
                refine ⟨3094816520877726348192835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16505688111347873857028453 3094816520877726348192835)
                ·
                  refine ⟨4642224781316589522289253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094816520877726348192835 4642224781316589522289253)
                  ·
                    refine ⟨870417146496860535429235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642224781316589522289253 870417146496860535429235)
                    ·
                      rfl

theorem cell23_5085394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_5085394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085394 prefixEnd_5085394 := by exact prefixLift 5085394
  have htrace : WordTrace (prefixWord ++ tailWord_5085394) baseStart_5085394 baseEnd_5085394 := by
    simpa [prefixWord, tailWord_5085394, baseEnd_5085394] using wordTrace_append hprefix tailTrace_5085394
  have hstable : (prefixWord ++ tailWord_5085394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085394).length < 2 ^ (prefixWord ++ tailWord_5085394).sum := by decide
  have hdescent : baseEnd_5085394 < baseStart_5085394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085403 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 3, 5]
def baseStart_5085403 : Nat := 118140960795 + 5085403 * 2 ^ 59
def prefixEnd_5085403 : Nat := 4983230072969 + 3 ^ 40 * 5085403 * 2
def baseEnd_5085403 : Nat := 870418686938824023691721

theorem tailTrace_5085403 : CollatzResearch.WordTrace tailWord_5085403 prefixEnd_5085403 870418686938824023691721 := by
  unfold tailWord_5085403
  simp only [CollatzResearch.WordTrace]
  refine ⟨185479885195460923531284863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123653256796973949020856575 185479885195460923531284863)
  ·
    refine ⟨278219827793191385296927295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185479885195460923531284863 278219827793191385296927295)
    ·
      refine ⟨417329741689787077945390943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278219827793191385296927295 417329741689787077945390943)
      ·
        refine ⟨625994612534680616918086415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417329741689787077945390943 625994612534680616918086415)
        ·
          refine ⟨938991918802020925377129623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625994612534680616918086415 938991918802020925377129623)
          ·
            refine ⟨1408487878203031388065694435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938991918802020925377129623 1408487878203031388065694435)
            ·
              refine ⟨2112731817304547082098541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408487878203031388065694435 2112731817304547082098541653)
              ·
                refine ⟨24758575984037661118342285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2112731817304547082098541653 24758575984037661118342285)
                ·
                  refine ⟨9284465994014122919378357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24758575984037661118342285 9284465994014122919378357)
                  ·
                    refine ⟨870418686938824023691721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9284465994014122919378357 870418686938824023691721)
                    ·
                      rfl

theorem cell23_5085403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].length) (baseStart_5085403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085403 prefixEnd_5085403 := by exact prefixLift 5085403
  have htrace : WordTrace (prefixWord ++ tailWord_5085403) baseStart_5085403 baseEnd_5085403 := by
    simpa [prefixWord, tailWord_5085403, baseEnd_5085403] using wordTrace_append hprefix tailTrace_5085403
  have hstable : (prefixWord ++ tailWord_5085403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085403).length < 2 ^ (prefixWord ++ tailWord_5085403).sum := by decide
  have hdescent : baseEnd_5085403 < baseStart_5085403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085420 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_5085420 : Nat := 118140960795 + 5085420 * 2 ^ 59
def prefixEnd_5085420 : Nat := 4983230072969 + 3 ^ 40 * 5085420 * 2
def baseEnd_5085420 : Nat := 870421596662532834854195

theorem tailTrace_5085420 : CollatzResearch.WordTrace tailWord_5085420 prefixEnd_5085420 870421596662532834854195 := by
  unfold tailWord_5085420
  simp only [CollatzResearch.WordTrace]
  refine ⟨92740252618199667717326857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123653670157599556956435809 92740252618199667717326857)
  ·
    refine ⟨69555189463649750787995143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92740252618199667717326857 69555189463649750787995143)
    ·
      refine ⟨104332784195474626181992715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69555189463649750787995143 104332784195474626181992715)
      ·
        refine ⟨156499176293211939272989073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104332784195474626181992715 156499176293211939272989073)
        ·
          refine ⟨117374382219908954454741805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156499176293211939272989073 117374382219908954454741805)
          ·
            refine ⟨44015393332465857920528177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117374382219908954454741805 44015393332465857920528177)
            ·
              refine ⟨33011544999349393440396133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44015393332465857920528177 33011544999349393440396133)
              ·
                refine ⟨6189664687378011270074275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33011544999349393440396133 6189664687378011270074275)
                ·
                  refine ⟨9284497031067016905111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189664687378011270074275 9284497031067016905111413)
                  ·
                    refine ⟨870421596662532834854195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9284497031067016905111413 870421596662532834854195)
                    ·
                      rfl

theorem cell23_5085420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_5085420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085420 prefixEnd_5085420 := by exact prefixLift 5085420
  have htrace : WordTrace (prefixWord ++ tailWord_5085420) baseStart_5085420 baseEnd_5085420 := by
    simpa [prefixWord, tailWord_5085420, baseEnd_5085420] using wordTrace_append hprefix tailTrace_5085420
  have hstable : (prefixWord ++ tailWord_5085420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085420).length < 2 ^ (prefixWord ++ tailWord_5085420).sum := by decide
  have hdescent : baseEnd_5085420 < baseStart_5085420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085421 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5085421 : Nat := 118140960795 + 5085421 * 2 ^ 59
def prefixEnd_5085421 : Nat := 4983230072969 + 3 ^ 40 * 5085421 * 2
def baseEnd_5085421 : Nat := 2611265303468253000650081

theorem tailTrace_5085421 : CollatzResearch.WordTrace tailWord_5085421 prefixEnd_5085421 2611265303468253000650081 := by
  unfold tailWord_5085421
  simp only [CollatzResearch.WordTrace]
  refine ⟨185480541709395712605440117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123653694472930475070293411 185480541709395712605440117)
  ·
    refine ⟨17388800785255848056760011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185480541709395712605440117 17388800785255848056760011)
    ·
      refine ⟨26083201177883772085140017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17388800785255848056760011 26083201177883772085140017)
      ·
        refine ⟨19562400883412829063855013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26083201177883772085140017 19562400883412829063855013)
        ·
          refine ⟨3667950165639905449472815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19562400883412829063855013 3667950165639905449472815)
          ·
            refine ⟨5501925248459858174209223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667950165639905449472815 5501925248459858174209223)
            ·
              refine ⟨8252887872689787261313835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501925248459858174209223 8252887872689787261313835)
              ·
                refine ⟨12379331809034680891970753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8252887872689787261313835 12379331809034680891970753)
                ·
                  refine ⟨9284498856776010668978065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12379331809034680891970753 9284498856776010668978065)
                  ·
                    refine ⟨6963374142582008001733549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9284498856776010668978065 6963374142582008001733549)
                    ·
                      refine ⟨2611265303468253000650081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963374142582008001733549 2611265303468253000650081)
                      ·
                        rfl

theorem cell23_5085421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5085421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085421 prefixEnd_5085421 := by exact prefixLift 5085421
  have htrace : WordTrace (prefixWord ++ tailWord_5085421) baseStart_5085421 baseEnd_5085421 := by
    simpa [prefixWord, tailWord_5085421, baseEnd_5085421] using wordTrace_append hprefix tailTrace_5085421
  have hstable : (prefixWord ++ tailWord_5085421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085421).length < 2 ^ (prefixWord ++ tailWord_5085421).sum := by decide
  have hdescent : baseEnd_5085421 < baseStart_5085421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085433 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_5085433 : Nat := 118140960795 + 5085433 * 2 ^ 59
def prefixEnd_5085433 : Nat := 4983230072969 + 3 ^ 40 * 5085433 * 2
def baseEnd_5085433 : Nat := 870423821745368984566675

theorem tailTrace_5085433 : CollatzResearch.WordTrace tailWord_5085433 prefixEnd_5085433 870423821745368984566675 := by
  unfold tailWord_5085433
  simp only [CollatzResearch.WordTrace]
  refine ⟨185480979385352238654876953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123653986256901492436584635 185480979385352238654876953)
  ·
    refine ⟨139110734539014178991157715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185480979385352238654876953 139110734539014178991157715)
    ·
      refine ⟨208666101808521268486736573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139110734539014178991157715 208666101808521268486736573)
      ·
        refine ⟨78249788178195475682526215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208666101808521268486736573 78249788178195475682526215)
        ·
          refine ⟨117374682267293213523789323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78249788178195475682526215 117374682267293213523789323)
          ·
            refine ⟨176062023400939820285683985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117374682267293213523789323 176062023400939820285683985)
            ·
              refine ⟨132046517550704865214262989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176062023400939820285683985 132046517550704865214262989)
              ·
                refine ⟨49517444081514324455348621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132046517550704865214262989 49517444081514324455348621)
                ·
                  refine ⟨18569041530567871670755733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49517444081514324455348621 18569041530567871670755733)
                  ·
                    refine ⟨870423821745368984566675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18569041530567871670755733 870423821745368984566675)
                    ·
                      rfl

theorem cell23_5085433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_5085433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085433 prefixEnd_5085433 := by exact prefixLift 5085433
  have htrace : WordTrace (prefixWord ++ tailWord_5085433) baseStart_5085433 baseEnd_5085433 := by
    simpa [prefixWord, tailWord_5085433, baseEnd_5085433] using wordTrace_append hprefix tailTrace_5085433
  have hstable : (prefixWord ++ tailWord_5085433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085433).length < 2 ^ (prefixWord ++ tailWord_5085433).sum := by decide
  have hdescent : baseEnd_5085433 < baseStart_5085433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085434 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_5085434 : Nat := 118140960795 + 5085434 * 2 ^ 59
def prefixEnd_5085434 : Nat := 4983230072969 + 3 ^ 40 * 5085434 * 2
def baseEnd_5085434 : Nat := 2611271978716761449787521

theorem tailTrace_5085434 : CollatzResearch.WordTrace tailWord_5085434 prefixEnd_5085434 2611271978716761449787521 := by
  unfold tailWord_5085434
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370253964587153956415839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123654010572232410550442237 46370253964587153956415839)
  ·
    refine ⟨69555380946880730934623759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46370253964587153956415839 69555380946880730934623759)
    ·
      refine ⟨104333071420321096401935639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69555380946880730934623759 104333071420321096401935639)
      ·
        refine ⟨156499607130481644602903459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104333071420321096401935639 156499607130481644602903459)
        ·
          refine ⟨234749410695722466904355189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156499607130481644602903459 234749410695722466904355189)
          ·
            refine ⟨22007757252723981272283299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234749410695722466904355189 22007757252723981272283299)
            ·
              refine ⟨33011635879085971908424949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22007757252723981272283299 33011635879085971908424949)
              ·
                refine ⟨3094840863664309866414839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33011635879085971908424949 3094840863664309866414839)
                ·
                  refine ⟨4642261295496464799622259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094840863664309866414839 4642261295496464799622259)
                  ·
                    refine ⟨6963391943244697199433389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642261295496464799622259 6963391943244697199433389)
                    ·
                      refine ⟨2611271978716761449787521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963391943244697199433389 2611271978716761449787521)
                      ·
                        rfl

theorem cell23_5085434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_5085434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085434 prefixEnd_5085434 := by exact prefixLift 5085434
  have htrace : WordTrace (prefixWord ++ tailWord_5085434) baseStart_5085434 baseEnd_5085434 := by
    simpa [prefixWord, tailWord_5085434, baseEnd_5085434] using wordTrace_append hprefix tailTrace_5085434
  have hstable : (prefixWord ++ tailWord_5085434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085434).length < 2 ^ (prefixWord ++ tailWord_5085434).sum := by decide
  have hdescent : baseEnd_5085434 < baseStart_5085434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085474 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5085474 : Nat := 118140960795 + 5085474 * 2 ^ 59
def prefixEnd_5085474 : Nat := 4983230072969 + 3 ^ 40 * 5085474 * 2
def baseEnd_5085474 : Nat := 2611292517942941293287337

theorem tailTrace_5085474 : CollatzResearch.WordTrace tailWord_5085474 prefixEnd_5085474 2611292517942941293287337 := by
  unfold tailWord_5085474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370618694550925664279869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123654983185469135104746317 46370618694550925664279869)
  ·
    refine ⟨17388982010456597124104951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46370618694550925664279869 17388982010456597124104951)
    ·
      refine ⟨26083473015684895686157427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17388982010456597124104951 26083473015684895686157427)
      ·
        refine ⟨39125209523527343529236141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26083473015684895686157427 39125209523527343529236141)
        ·
          refine ⟨14671953571322753823463553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39125209523527343529236141 14671953571322753823463553)
          ·
            refine ⟨11003965178492065367597665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14671953571322753823463553 11003965178492065367597665)
            ·
              refine ⟨8252973883869049025698249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11003965178492065367597665 8252973883869049025698249)
              ·
                refine ⟨6189730412901786769273687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252973883869049025698249 6189730412901786769273687)
                ·
                  refine ⟨9284595619352680153910531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189730412901786769273687 9284595619352680153910531)
                  ·
                    refine ⟨13926893429029020230865797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9284595619352680153910531 13926893429029020230865797)
                    ·
                      refine ⟨2611292517942941293287337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13926893429029020230865797 2611292517942941293287337)
                      ·
                        rfl

theorem cell23_5085474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5085474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085474 prefixEnd_5085474 := by exact prefixLift 5085474
  have htrace : WordTrace (prefixWord ++ tailWord_5085474) baseStart_5085474 baseEnd_5085474 := by
    simpa [prefixWord, tailWord_5085474, baseEnd_5085474] using wordTrace_append hprefix tailTrace_5085474
  have hstable : (prefixWord ++ tailWord_5085474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085474).length < 2 ^ (prefixWord ++ tailWord_5085474).sum := by decide
  have hdescent : baseEnd_5085474 < baseStart_5085474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085485 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5085485 : Nat := 118140960795 + 5085485 * 2 ^ 59
def prefixEnd_5085485 : Nat := 4983230072969 + 3 ^ 40 * 5085485 * 2
def baseEnd_5085485 : Nat := 2611298166230140750249787

theorem tailTrace_5085485 : CollatzResearch.WordTrace tailWord_5085485 prefixEnd_5085485 2611298166230140750249787 := by
  unfold tailWord_5085485
  simp only [CollatzResearch.WordTrace]
  refine ⟨185482875981163851535769909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123655250654109234357179939 185482875981163851535769909)
  ·
    refine ⟨17389019623234111081478429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185482875981163851535769909 17389019623234111081478429)
    ·
      refine ⟨6520882358712791655554411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17389019623234111081478429 6520882358712791655554411)
      ·
        refine ⟨9781323538069187483331617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6520882358712791655554411 9781323538069187483331617)
        ·
          refine ⟨7335992653551890612498713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9781323538069187483331617 7335992653551890612498713)
          ·
            refine ⟨5501994490163917959374035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335992653551890612498713 5501994490163917959374035)
            ·
              refine ⟨8252991735245876939061053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501994490163917959374035 8252991735245876939061053)
              ·
                refine ⟨3094871900717203852147895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8252991735245876939061053 3094871900717203852147895)
                ·
                  refine ⟨4642307851075805778221843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094871900717203852147895 4642307851075805778221843)
                  ·
                    refine ⟨6963461776613708667332765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642307851075805778221843 6963461776613708667332765)
                    ·
                      refine ⟨2611298166230140750249787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963461776613708667332765 2611298166230140750249787)
                      ·
                        rfl

theorem cell23_5085485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5085485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085485 prefixEnd_5085485 := by exact prefixLift 5085485
  have htrace : WordTrace (prefixWord ++ tailWord_5085485) baseStart_5085485 baseEnd_5085485 := by
    simpa [prefixWord, tailWord_5085485, baseEnd_5085485] using wordTrace_append hprefix tailTrace_5085485
  have hstable : (prefixWord ++ tailWord_5085485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085485).length < 2 ^ (prefixWord ++ tailWord_5085485).sum := by decide
  have hdescent : baseEnd_5085485 < baseStart_5085485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085507 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 3]
def baseStart_5085507 : Nat := 118140960795 + 5085507 * 2 ^ 59
def prefixEnd_5085507 : Nat := 4983230072969 + 3 ^ 40 * 5085507 * 2
def baseEnd_5085507 : Nat := 2611309462804539664174685

theorem tailTrace_5085507 : CollatzResearch.WordTrace tailWord_5085507 prefixEnd_5085507 2611309462804539664174685 := by
  unfold tailWord_5085507
  simp only [CollatzResearch.WordTrace]
  refine ⟨185483678387084149293070775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123655785591389432862047183 185483678387084149293070775)
  ·
    refine ⟨278225517580626223939606163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185483678387084149293070775 278225517580626223939606163)
    ·
      refine ⟨417338276370939335909409245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278225517580626223939606163 417338276370939335909409245)
      ·
        refine ⟨156501853639102250966028467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417338276370939335909409245 156501853639102250966028467)
        ·
          refine ⟨234752780458653376449042701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156501853639102250966028467 234752780458653376449042701)
          ·
            refine ⟨88032292671995016168391013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234752780458653376449042701 88032292671995016168391013)
            ·
              refine ⟨16506054875999065531573315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88032292671995016168391013 16506054875999065531573315)
              ·
                refine ⟨24759082313998598297359973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16506054875999065531573315 24759082313998598297359973)
                ·
                  refine ⟨4642327933874737180754995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24759082313998598297359973 4642327933874737180754995)
                  ·
                    refine ⟨6963491900812105771132493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642327933874737180754995 6963491900812105771132493)
                    ·
                      refine ⟨2611309462804539664174685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963491900812105771132493 2611309462804539664174685)
                      ·
                        rfl

theorem cell23_5085507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_5085507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085507 prefixEnd_5085507 := by exact prefixLift 5085507
  have htrace : WordTrace (prefixWord ++ tailWord_5085507) baseStart_5085507 baseEnd_5085507 := by
    simpa [prefixWord, tailWord_5085507, baseEnd_5085507] using wordTrace_append hprefix tailTrace_5085507
  have hstable : (prefixWord ++ tailWord_5085507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085507).length < 2 ^ (prefixWord ++ tailWord_5085507).sum := by decide
  have hdescent : baseEnd_5085507 < baseStart_5085507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085547 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 4, 2]
def baseStart_5085547 : Nat := 118140960795 + 5085547 * 2 ^ 59
def prefixEnd_5085547 : Nat := 4983230072969 + 3 ^ 40 * 5085547 * 2
def baseEnd_5085547 : Nat := 2611330002030719507674501

theorem tailTrace_5085547 : CollatzResearch.WordTrace tailWord_5085547 prefixEnd_5085547 2611330002030719507674501 := by
  unfold tailWord_5085547
  simp only [CollatzResearch.WordTrace]
  refine ⟨185485137306939236124526895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123656758204626157416351263 185485137306939236124526895)
  ·
    refine ⟨278227705960408854186790343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185485137306939236124526895 278227705960408854186790343)
    ·
      refine ⟨417341558940613281280185515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278227705960408854186790343 417341558940613281280185515)
      ·
        refine ⟨626012338410919921920278273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417341558940613281280185515 626012338410919921920278273)
        ·
          refine ⟨469509253808189941440208705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626012338410919921920278273 469509253808189941440208705)
          ·
            refine ⟨352131940356142456080156529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469509253808189941440208705 352131940356142456080156529)
            ·
              refine ⟨264098955267106842060117397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352131940356142456080156529 264098955267106842060117397)
              ·
                refine ⟨12379638528145633221568003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 264098955267106842060117397 12379638528145633221568003)
                ·
                  refine ⟨18569457792218449832352005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12379638528145633221568003 18569457792218449832352005)
                  ·
                    refine ⟨3481773336040959343566001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18569457792218449832352005 3481773336040959343566001)
                    ·
                      refine ⟨2611330002030719507674501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481773336040959343566001 2611330002030719507674501)
                      ·
                        rfl

theorem cell23_5085547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4, 2].length) (baseStart_5085547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085547 prefixEnd_5085547 := by exact prefixLift 5085547
  have htrace : WordTrace (prefixWord ++ tailWord_5085547) baseStart_5085547 baseEnd_5085547 := by
    simpa [prefixWord, tailWord_5085547, baseEnd_5085547] using wordTrace_append hprefix tailTrace_5085547
  have hstable : (prefixWord ++ tailWord_5085547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085547).length < 2 ^ (prefixWord ++ tailWord_5085547).sum := by decide
  have hdescent : baseEnd_5085547 < baseStart_5085547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085577 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_5085577 : Nat := 118140960795 + 5085577 * 2 ^ 59
def prefixEnd_5085577 : Nat := 4983230072969 + 3 ^ 40 * 5085577 * 2
def baseEnd_5085577 : Nat := 2611345406450354390299363

theorem tailTrace_5085577 : CollatzResearch.WordTrace tailWord_5085577 prefixEnd_5085577 2611345406450354390299363 := by
  unfold tailWord_5085577
  simp only [CollatzResearch.WordTrace]
  refine ⟨185486231496830551248118985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123657487664553700832079323 185486231496830551248118985)
  ·
    refine ⟨139114673622622913436089239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185486231496830551248118985 139114673622622913436089239)
    ·
      refine ⟨208672010433934370154133859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139114673622622913436089239 208672010433934370154133859)
      ·
        refine ⟨313008015650901555231200789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208672010433934370154133859 313008015650901555231200789)
        ·
          refine ⟨14672250733636010401462537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 313008015650901555231200789 14672250733636010401462537)
          ·
            refine ⟨11004188050227007801096903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14672250733636010401462537 11004188050227007801096903)
            ·
              refine ⟨16506282075340511701645355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11004188050227007801096903 16506282075340511701645355)
              ·
                refine ⟨24759423113010767552468033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16506282075340511701645355 24759423113010767552468033)
                ·
                  refine ⟨18569567334758075664351025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24759423113010767552468033 18569567334758075664351025)
                  ·
                    refine ⟨13927175501068556748263269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18569567334758075664351025 13927175501068556748263269)
                    ·
                      refine ⟨2611345406450354390299363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13927175501068556748263269 2611345406450354390299363)
                      ·
                        rfl

theorem cell23_5085577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_5085577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085577 prefixEnd_5085577 := by exact prefixLift 5085577
  have htrace : WordTrace (prefixWord ++ tailWord_5085577) baseStart_5085577 baseEnd_5085577 := by
    simpa [prefixWord, tailWord_5085577, baseEnd_5085577] using wordTrace_append hprefix tailTrace_5085577
  have hstable : (prefixWord ++ tailWord_5085577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085577).length < 2 ^ (prefixWord ++ tailWord_5085577).sum := by decide
  have hdescent : baseEnd_5085577 < baseStart_5085577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085654 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5085654 : Nat := 118140960795 + 5085654 * 2 ^ 59
def prefixEnd_5085654 : Nat := 4983230072969 + 3 ^ 40 * 5085654 * 2
def baseEnd_5085654 : Nat := 2611384944460750589036509

theorem tailTrace_5085654 : CollatzResearch.WordTrace tailWord_5085654 prefixEnd_5085654 2611384944460750589036509 := by
  unfold tailWord_5085654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593064994846974587417001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123659359945034395599114677 11593064994846974587417001)
  ·
    refine ⟨8694798746135230940562751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11593064994846974587417001 8694798746135230940562751)
    ·
      refine ⟨13042198119202846410844127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8694798746135230940562751 13042198119202846410844127)
      ·
        refine ⟨19563297178804269616266191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13042198119202846410844127 19563297178804269616266191)
        ·
          refine ⟨29344945768206404424399287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19563297178804269616266191 29344945768206404424399287)
          ·
            refine ⟨44017418652309606636598931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29344945768206404424399287 44017418652309606636598931)
            ·
              refine ⟨66026127978464409954898397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44017418652309606636598931 66026127978464409954898397)
              ·
                refine ⟨24759797991924153733086899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66026127978464409954898397 24759797991924153733086899)
                ·
                  refine ⟨37139696987886230599630349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24759797991924153733086899 37139696987886230599630349)
                  ·
                    refine ⟨13927386370457336474861381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37139696987886230599630349 13927386370457336474861381)
                    ·
                      refine ⟨2611384944460750589036509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13927386370457336474861381 2611384944460750589036509)
                      ·
                        rfl

theorem cell23_5085654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5085654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085654 prefixEnd_5085654 := by exact prefixLift 5085654
  have htrace : WordTrace (prefixWord ++ tailWord_5085654) baseStart_5085654 baseEnd_5085654 := by
    simpa [prefixWord, tailWord_5085654, baseEnd_5085654] using wordTrace_append hprefix tailTrace_5085654
  have hstable : (prefixWord ++ tailWord_5085654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085654).length < 2 ^ (prefixWord ++ tailWord_5085654).sum := by decide
  have hdescent : baseEnd_5085654 < baseStart_5085654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085657 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_5085657 : Nat := 118140960795 + 5085657 * 2 ^ 59
def prefixEnd_5085657 : Nat := 4983230072969 + 3 ^ 40 * 5085657 * 2
def baseEnd_5085657 : Nat := 2611386484902714077298995

theorem tailTrace_5085657 : CollatzResearch.WordTrace tailWord_5085657 prefixEnd_5085657 2611386484902714077298995 := by
  unfold tailWord_5085657
  simp only [CollatzResearch.WordTrace]
  refine ⟨185489149336540724911031225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123659432891027149940687483 185489149336540724911031225)
  ·
    refine ⟨139116862002405543683273419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185489149336540724911031225 139116862002405543683273419)
    ·
      refine ⟨208675293003608315524910129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139116862002405543683273419 208675293003608315524910129)
      ·
        refine ⟨156506469752706236643682597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208675293003608315524910129 156506469752706236643682597)
        ·
          refine ⟨29344963078632419370690487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156506469752706236643682597 29344963078632419370690487)
          ·
            refine ⟨44017444617948629056035731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29344963078632419370690487 44017444617948629056035731)
            ·
              refine ⟨66026166926922943584053597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44017444617948629056035731 66026166926922943584053597)
              ·
                refine ⟨24759812597596103844020099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66026166926922943584053597 24759812597596103844020099)
                ·
                  refine ⟨37139718896394155766030149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24759812597596103844020099 37139718896394155766030149)
                  ·
                    refine ⟨6963697293073904206130653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37139718896394155766030149 6963697293073904206130653)
                    ·
                      refine ⟨2611386484902714077298995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963697293073904206130653 2611386484902714077298995)
                      ·
                        rfl

theorem cell23_5085657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_5085657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085657 prefixEnd_5085657 := by exact prefixLift 5085657
  have htrace : WordTrace (prefixWord ++ tailWord_5085657) baseStart_5085657 baseEnd_5085657 := by
    simpa [prefixWord, tailWord_5085657, baseEnd_5085657] using wordTrace_append hprefix tailTrace_5085657
  have hstable : (prefixWord ++ tailWord_5085657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085657).length < 2 ^ (prefixWord ++ tailWord_5085657).sum := by decide
  have hdescent : baseEnd_5085657 < baseStart_5085657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085674 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_5085674 : Nat := 118140960795 + 5085674 * 2 ^ 59
def prefixEnd_5085674 : Nat := 4983230072969 + 3 ^ 40 * 5085674 * 2
def baseEnd_5085674 : Nat := 2611395214073840510786417

theorem tailTrace_5085674 : CollatzResearch.WordTrace tailWord_5085674 prefixEnd_5085674 2611395214073840510786417 := by
  unfold tailWord_5085674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46372442344369784203600019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123659846251652757876266717 46372442344369784203600019)
  ·
    refine ⟨69558663516554676305400029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46372442344369784203600019 69558663516554676305400029)
    ·
      refine ⟨26084498818708003614525011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69558663516554676305400029 26084498818708003614525011)
      ·
        refine ⟨39126748228062005421787517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26084498818708003614525011 39126748228062005421787517)
        ·
          refine ⟨14672530585523252033170319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39126748228062005421787517 14672530585523252033170319)
          ·
            refine ⟨22008795878284878049755479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14672530585523252033170319 22008795878284878049755479)
            ·
              refine ⟨33013193817427317074633219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22008795878284878049755479 33013193817427317074633219)
              ·
                refine ⟨49519790726140975611949829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33013193817427317074633219 49519790726140975611949829)
                ·
                  refine ⟨9284960761151432927240593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49519790726140975611949829 9284960761151432927240593)
                  ·
                    refine ⟨6963720570863574695430445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9284960761151432927240593 6963720570863574695430445)
                    ·
                      refine ⟨2611395214073840510786417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963720570863574695430445 2611395214073840510786417)
                      ·
                        rfl

theorem cell23_5085674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_5085674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085674 prefixEnd_5085674 := by exact prefixLift 5085674
  have htrace : WordTrace (prefixWord ++ tailWord_5085674) baseStart_5085674 baseEnd_5085674 := by
    simpa [prefixWord, tailWord_5085674, baseEnd_5085674] using wordTrace_append hprefix tailTrace_5085674
  have hstable : (prefixWord ++ tailWord_5085674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085674).length < 2 ^ (prefixWord ++ tailWord_5085674).sum := by decide
  have hdescent : baseEnd_5085674 < baseStart_5085674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085704 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_5085704 : Nat := 118140960795 + 5085704 * 2 ^ 59
def prefixEnd_5085704 : Nat := 4983230072969 + 3 ^ 40 * 5085704 * 2
def baseEnd_5085704 : Nat := 2611410618493475393411279

theorem tailTrace_5085704 : CollatzResearch.WordTrace tailWord_5085704 prefixEnd_5085704 2611410618493475393411279 := by
  unfold tailWord_5085704
  simp only [CollatzResearch.WordTrace]
  refine ⟨92745431783685225968996083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123660575711580301291994777 92745431783685225968996083)
  ·
    refine ⟨139118147675527838953494125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92745431783685225968996083 139118147675527838953494125)
    ·
      refine ⟨52169305378322939607560297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139118147675527838953494125 52169305378322939607560297)
      ·
        refine ⟨39126979033742204705670223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52169305378322939607560297 39126979033742204705670223)
        ·
          refine ⟨58690468550613307058505335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39126979033742204705670223 58690468550613307058505335)
          ·
            refine ⟨88035702825919960587758003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58690468550613307058505335 88035702825919960587758003)
            ·
              refine ⟨132053554238879940881637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88035702825919960587758003 132053554238879940881637005)
              ·
                refine ⟨49520082839579977830613877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132053554238879940881637005 49520082839579977830613877)
                ·
                  refine ⟨4642507766210622921620051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49520082839579977830613877 4642507766210622921620051)
                  ·
                    refine ⟨6963761649315934382430077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642507766210622921620051 6963761649315934382430077)
                    ·
                      refine ⟨2611410618493475393411279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6963761649315934382430077 2611410618493475393411279)
                      ·
                        rfl

theorem cell23_5085704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_5085704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085704 prefixEnd_5085704 := by exact prefixLift 5085704
  have htrace : WordTrace (prefixWord ++ tailWord_5085704) baseStart_5085704 baseEnd_5085704 := by
    simpa [prefixWord, tailWord_5085704, baseEnd_5085704] using wordTrace_append hprefix tailTrace_5085704
  have hstable : (prefixWord ++ tailWord_5085704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085704).length < 2 ^ (prefixWord ++ tailWord_5085704).sum := by decide
  have hdescent : baseEnd_5085704 < baseStart_5085704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085731 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 2, 3, 2]
def baseStart_5085731 : Nat := 118140960795 + 5085731 * 2 ^ 59
def prefixEnd_5085731 : Nat := 4983230072969 + 3 ^ 40 * 5085731 * 2
def baseEnd_5085731 : Nat := 2611424482471146787773655

theorem tailTrace_5085731 : CollatzResearch.WordTrace tailWord_5085731 prefixEnd_5085731 2611424482471146787773655 := by
  unfold tailWord_5085731
  simp only [CollatzResearch.WordTrace]
  refine ⟨185491848338272635549225047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123661232225515090366150031 185491848338272635549225047)
  ·
    refine ⟨278237772507408953323837571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185491848338272635549225047 278237772507408953323837571)
    ·
      refine ⟨417356658761113429985756357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278237772507408953323837571 417356658761113429985756357)
      ·
        refine ⟨78254373517708768122329317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 417356658761113429985756357 78254373517708768122329317)
        ·
          refine ⟨14672695034570394022936747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78254373517708768122329317 14672695034570394022936747)
          ·
            refine ⟨22009042551855591034405121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14672695034570394022936747 22009042551855591034405121)
            ·
              refine ⟨16506781913891693275803841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22009042551855591034405121 16506781913891693275803841)
              ·
                refine ⟨12380086435418769956852881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16506781913891693275803841 12380086435418769956852881)
                ·
                  refine ⟨9285064826564077467639661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12380086435418769956852881 9285064826564077467639661)
                  ·
                    refine ⟨3481899309961529050364873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285064826564077467639661 3481899309961529050364873)
                    ·
                      refine ⟨2611424482471146787773655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481899309961529050364873 2611424482471146787773655)
                      ·
                        rfl

theorem cell23_5085731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_5085731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085731 prefixEnd_5085731 := by exact prefixLift 5085731
  have htrace : WordTrace (prefixWord ++ tailWord_5085731) baseStart_5085731 baseEnd_5085731 := by
    simpa [prefixWord, tailWord_5085731, baseEnd_5085731] using wordTrace_append hprefix tailTrace_5085731
  have hstable : (prefixWord ++ tailWord_5085731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085731).length < 2 ^ (prefixWord ++ tailWord_5085731).sum := by decide
  have hdescent : baseEnd_5085731 < baseStart_5085731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085732 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_5085732 : Nat := 118140960795 + 5085732 * 2 ^ 59
def prefixEnd_5085732 : Nat := 4983230072969 + 3 ^ 40 * 5085732 * 2
def baseEnd_5085732 : Nat := 870474998650600427953717

theorem tailTrace_5085732 : CollatzResearch.WordTrace tailWord_5085732 prefixEnd_5085732 870474998650600427953717 := by
  unfold tailWord_5085732
  simp only [CollatzResearch.WordTrace]
  refine ⟨92745942405634506360005725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123661256540846008480007633 92745942405634506360005725)
  ·
    refine ⟨34779728402112939885002147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92745942405634506360005725 34779728402112939885002147)
    ·
      refine ⟨52169592603169409827503221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34779728402112939885002147 52169592603169409827503221)
      ·
        refine ⟨4890899306547132171328427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52169592603169409827503221 4890899306547132171328427)
        ·
          refine ⟨7336348959820698256992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890899306547132171328427 7336348959820698256992641)
          ·
            refine ⟨5502261719865523692744481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336348959820698256992641 5502261719865523692744481)
            ·
              refine ⟨4126696289899142769558361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502261719865523692744481 4126696289899142769558361)
              ·
                refine ⟨3095022217424357077168771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126696289899142769558361 3095022217424357077168771)
                ·
                  refine ⟨4642533326136535615753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095022217424357077168771 4642533326136535615753157)
                  ·
                    refine ⟨870474998650600427953717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642533326136535615753157 870474998650600427953717)
                    ·
                      rfl

theorem cell23_5085732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_5085732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085732 prefixEnd_5085732 := by exact prefixLift 5085732
  have htrace : WordTrace (prefixWord ++ tailWord_5085732) baseStart_5085732 baseEnd_5085732 := by
    simpa [prefixWord, tailWord_5085732, baseEnd_5085732] using wordTrace_append hprefix tailTrace_5085732
  have hstable : (prefixWord ++ tailWord_5085732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085732).length < 2 ^ (prefixWord ++ tailWord_5085732).sum := by decide
  have hdescent : baseEnd_5085732 < baseStart_5085732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085747 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_5085747 : Nat := 118140960795 + 5085747 * 2 ^ 59
def prefixEnd_5085747 : Nat := 4983230072969 + 3 ^ 40 * 5085747 * 2
def baseEnd_5085747 : Nat := 2611432698161618725173581

theorem tailTrace_5085747 : CollatzResearch.WordTrace tailWord_5085747 prefixEnd_5085747 2611432698161618725173581 := by
  unfold tailWord_5085747
  simp only [CollatzResearch.WordTrace]
  refine ⟨185492431906214670281807495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123661621270809780187871663 185492431906214670281807495)
  ·
    refine ⟨278238647859322005422711243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185492431906214670281807495 278238647859322005422711243)
    ·
      refine ⟨417357971788983008134066865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278238647859322005422711243 417357971788983008134066865)
      ·
        refine ⟨313018478841737256100550149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417357971788983008134066865 313018478841737256100550149)
        ·
          refine ⟨58690964782825735518853153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313018478841737256100550149 58690964782825735518853153)
          ·
            refine ⟨44018223587119301639139865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58690964782825735518853153 44018223587119301639139865)
            ·
              refine ⟨33013667690339476229354899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44018223587119301639139865 33013667690339476229354899)
              ·
                refine ⟨49520501535509214344032349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33013667690339476229354899 49520501535509214344032349)
                ·
                  refine ⟨18570188075815955379012131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49520501535509214344032349 18570188075815955379012131)
                  ·
                    refine ⟨27855282113723933068518197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18570188075815955379012131 27855282113723933068518197)
                    ·
                      refine ⟨2611432698161618725173581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27855282113723933068518197 2611432698161618725173581)
                      ·
                        rfl

theorem cell23_5085747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_5085747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085747 prefixEnd_5085747 := by exact prefixLift 5085747
  have htrace : WordTrace (prefixWord ++ tailWord_5085747) baseStart_5085747 baseEnd_5085747 := by
    simpa [prefixWord, tailWord_5085747, baseEnd_5085747] using wordTrace_append hprefix tailTrace_5085747
  have hstable : (prefixWord ++ tailWord_5085747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085747).length < 2 ^ (prefixWord ++ tailWord_5085747).sum := by decide
  have hdescent : baseEnd_5085747 < baseStart_5085747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085754 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_5085754 : Nat := 118140960795 + 5085754 * 2 ^ 59
def prefixEnd_5085754 : Nat := 4983230072969 + 3 ^ 40 * 5085754 * 2
def baseEnd_5085754 : Nat := 870478764175400065928683

theorem tailTrace_5085754 : CollatzResearch.WordTrace tailWord_5085754 prefixEnd_5085754 870478764175400065928683 := by
  unfold tailWord_5085754
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373171804297327619328079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123661791478126206984874877 46373171804297327619328079)
  ·
    refine ⟨69559757706445991428992119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46373171804297327619328079 69559757706445991428992119)
    ·
      refine ⟨104339636559668987143488179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69559757706445991428992119 104339636559668987143488179)
      ·
        refine ⟨156509454839503480715232269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104339636559668987143488179 156509454839503480715232269)
        ·
          refine ⟨58691045564813805268212101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156509454839503480715232269 58691045564813805268212101)
          ·
            refine ⟨11004571043402588487789769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58691045564813805268212101 11004571043402588487789769)
            ·
              refine ⟨8253428282551941365842327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11004571043402588487789769 8253428282551941365842327)
              ·
                refine ⟨12380142423827912048763491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253428282551941365842327 12380142423827912048763491)
                ·
                  refine ⟨18570213635741868073145237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380142423827912048763491 18570213635741868073145237)
                  ·
                    refine ⟨870478764175400065928683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18570213635741868073145237 870478764175400065928683)
                    ·
                      rfl

theorem cell23_5085754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_5085754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085754 prefixEnd_5085754 := by exact prefixLift 5085754
  have htrace : WordTrace (prefixWord ++ tailWord_5085754) baseStart_5085754 baseEnd_5085754 := by
    simpa [prefixWord, tailWord_5085754, baseEnd_5085754] using wordTrace_append hprefix tailTrace_5085754
  have hstable : (prefixWord ++ tailWord_5085754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085754).length < 2 ^ (prefixWord ++ tailWord_5085754).sum := by decide
  have hdescent : baseEnd_5085754 < baseStart_5085754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085774 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_5085774 : Nat := 118140960795 + 5085774 * 2 ^ 59
def prefixEnd_5085774 : Nat := 4983230072969 + 3 ^ 40 * 5085774 * 2
def baseEnd_5085774 : Nat := 2611446562139290119535957

theorem tailTrace_5085774 : CollatzResearch.WordTrace tailWord_5085774 prefixEnd_5085774 2611446562139290119535957 := by
  unfold tailWord_5085774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23186677084639606736630047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123662277784744569262026917 23186677084639606736630047)
  ·
    refine ⟨34780015626959410104945071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23186677084639606736630047 34780015626959410104945071)
    ·
      refine ⟨52170023440439115157417607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34780015626959410104945071 52170023440439115157417607)
      ·
        refine ⟨78255035160658672736126411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52170023440439115157417607 78255035160658672736126411)
        ·
          refine ⟨117382552740988009104189617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78255035160658672736126411 117382552740988009104189617)
          ·
            refine ⟨88036914555741006828142213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117382552740988009104189617 88036914555741006828142213)
            ·
              refine ⟨16506921479201438780276665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88036914555741006828142213 16506921479201438780276665)
              ·
                refine ⟨12380191109401079085207499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16506921479201438780276665 12380191109401079085207499)
                ·
                  refine ⟨18570286664101618627811249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380191109401079085207499 18570286664101618627811249)
                  ·
                    refine ⟨13927714998076213970858437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18570286664101618627811249 13927714998076213970858437)
                    ·
                      refine ⟨2611446562139290119535957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13927714998076213970858437 2611446562139290119535957)
                      ·
                        rfl

theorem cell23_5085774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_5085774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085774 prefixEnd_5085774 := by exact prefixLift 5085774
  have htrace : WordTrace (prefixWord ++ tailWord_5085774) baseStart_5085774 baseEnd_5085774 := by
    simpa [prefixWord, tailWord_5085774, baseEnd_5085774] using wordTrace_append hprefix tailTrace_5085774
  have hstable : (prefixWord ++ tailWord_5085774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085774).length < 2 ^ (prefixWord ++ tailWord_5085774).sum := by decide
  have hdescent : baseEnd_5085774 < baseStart_5085774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085808 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4]
def baseStart_5085808 : Nat := 118140960795 + 5085808 * 2 ^ 59
def prefixEnd_5085808 : Nat := 4983230072969 + 3 ^ 40 * 5085808 * 2
def baseEnd_5085808 : Nat := 2611464020481542986510801

theorem tailTrace_5085808 : CollatzResearch.WordTrace tailWord_5085808 prefixEnd_5085808 2611464020481542986510801 := by
  unfold tailWord_5085808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92747328379496838849889039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123663104505995785133185385 92747328379496838849889039)
  ·
    refine ⟨139120992569245258274833559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92747328379496838849889039 139120992569245258274833559)
    ·
      refine ⟨208681488853867887412250339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139120992569245258274833559 208681488853867887412250339)
      ·
        refine ⟨313022233280801831118375509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208681488853867887412250339 313022233280801831118375509)
        ·
          refine ⟨3668229296259396458418463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 313022233280801831118375509 3668229296259396458418463)
          ·
            refine ⟨5502343944389094687627695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668229296259396458418463 5502343944389094687627695)
            ·
              refine ⟨8253515916583642031441543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502343944389094687627695 8253515916583642031441543)
              ·
                refine ⟨12380273874875463047162315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253515916583642031441543 12380273874875463047162315)
                ·
                  refine ⟨18570410812313194570743473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380273874875463047162315 18570410812313194570743473)
                  ·
                    refine ⟨13927808109234895928057605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18570410812313194570743473 13927808109234895928057605)
                    ·
                      refine ⟨2611464020481542986510801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13927808109234895928057605 2611464020481542986510801)
                      ·
                        rfl

theorem cell23_5085808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4].length) (baseStart_5085808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085808 prefixEnd_5085808 := by exact prefixLift 5085808
  have htrace : WordTrace (prefixWord ++ tailWord_5085808) baseStart_5085808 baseEnd_5085808 := by
    simpa [prefixWord, tailWord_5085808, baseEnd_5085808] using wordTrace_append hprefix tailTrace_5085808
  have hstable : (prefixWord ++ tailWord_5085808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085808).length < 2 ^ (prefixWord ++ tailWord_5085808).sum := by decide
  have hdescent : baseEnd_5085808 < baseStart_5085808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085827 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 8]
def baseStart_5085827 : Nat := 118140960795 + 5085827 * 2 ^ 59
def prefixEnd_5085827 : Nat := 4983230072969 + 3 ^ 40 * 5085827 * 2
def baseEnd_5085827 : Nat := 870491258871326137391071

theorem tailTrace_5085827 : CollatzResearch.WordTrace tailWord_5085827 prefixEnd_5085827 870491258871326137391071 := by
  unfold tailWord_5085827
  simp only [CollatzResearch.WordTrace]
  refine ⟨185495349745924843944719735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123663566497283229296479823 185495349745924843944719735)
  ·
    refine ⟨278243024618887265917079603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185495349745924843944719735 278243024618887265917079603)
    ·
      refine ⟨417364536928330898875619405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278243024618887265917079603 417364536928330898875619405)
      ·
        refine ⟨156511701348124087078357277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417364536928330898875619405 156511701348124087078357277)
        ·
          refine ⟨58691888005546532654383979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156511701348124087078357277 58691888005546532654383979)
          ·
            refine ⟨88037832008319798981575969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58691888005546532654383979 88037832008319798981575969)
            ·
              refine ⟨66028374006239849236181977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88037832008319798981575969 66028374006239849236181977)
              ·
                refine ⟨49521280504679886927136483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66028374006239849236181977 49521280504679886927136483)
                ·
                  refine ⟨74281920757019830390704725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49521280504679886927136483 74281920757019830390704725)
                  ·
                    refine ⟨870491258871326137391071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74281920757019830390704725 870491258871326137391071)
                    ·
                      rfl

theorem cell23_5085827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_5085827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085827 prefixEnd_5085827 := by exact prefixLift 5085827
  have htrace : WordTrace (prefixWord ++ tailWord_5085827) baseStart_5085827 baseEnd_5085827 := by
    simpa [prefixWord, tailWord_5085827, baseEnd_5085827] using wordTrace_append hprefix tailTrace_5085827
  have hstable : (prefixWord ++ tailWord_5085827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085827).length < 2 ^ (prefixWord ++ tailWord_5085827).sum := by decide
  have hdescent : baseEnd_5085827 < baseStart_5085827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085838 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5085838 : Nat := 118140960795 + 5085838 * 2 ^ 59
def prefixEnd_5085838 : Nat := 4983230072969 + 3 ^ 40 * 5085838 * 2
def baseEnd_5085838 : Nat := 2611479424901177869135663

theorem tailTrace_5085838 : CollatzResearch.WordTrace tailWord_5085838 prefixEnd_5085838 2611479424901177869135663 := by
  unfold tailWord_5085838
  simp only [CollatzResearch.WordTrace]
  refine ⟨23186968868610624102921271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123663833965923328548913445 23186968868610624102921271)
  ·
    refine ⟨34780453302915936154381907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23186968868610624102921271 34780453302915936154381907)
    ·
      refine ⟨52170679954373904231572861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34780453302915936154381907 52170679954373904231572861)
      ·
        refine ⟨19564004982890214086839823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52170679954373904231572861 19564004982890214086839823)
        ·
          refine ⟨29346007474335321130259735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19564004982890214086839823 29346007474335321130259735)
          ·
            refine ⟨44019011211502981695389603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29346007474335321130259735 44019011211502981695389603)
            ·
              refine ⟨66028516817254472543084405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44019011211502981695389603 66028516817254472543084405)
              ·
                refine ⟨6190173451617606800914163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66028516817254472543084405 6190173451617606800914163)
                ·
                  refine ⟨9285260177426410201371245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190173451617606800914163 9285260177426410201371245)
                  ·
                    refine ⟨3481972566534903825514217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285260177426410201371245 3481972566534903825514217)
                    ·
                      refine ⟨2611479424901177869135663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3481972566534903825514217 2611479424901177869135663)
                      ·
                        rfl

theorem cell23_5085838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5085838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085838 prefixEnd_5085838 := by exact prefixLift 5085838
  have htrace : WordTrace (prefixWord ++ tailWord_5085838) baseStart_5085838 baseEnd_5085838 := by
    simpa [prefixWord, tailWord_5085838, baseEnd_5085838] using wordTrace_append hprefix tailTrace_5085838
  have hstable : (prefixWord ++ tailWord_5085838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085838).length < 2 ^ (prefixWord ++ tailWord_5085838).sum := by decide
  have hdescent : baseEnd_5085838 < baseStart_5085838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085889 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5085889 : Nat := 118140960795 + 5085889 * 2 ^ 59
def prefixEnd_5085889 : Nat := 4983230072969 + 3 ^ 40 * 5085889 * 2
def baseEnd_5085889 : Nat := 2611505612414557169597929

theorem tailTrace_5085889 : CollatzResearch.WordTrace tailWord_5085889 prefixEnd_5085889 2611505612414557169597929 := by
  unfold tailWord_5085889
  simp only [CollatzResearch.WordTrace]
  refine ⟨185497611071700228533476721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123665074047800152355651147 185497611071700228533476721)
  ·
    refine ⟨139123208303775171400107541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185497611071700228533476721 139123208303775171400107541)
    ·
      refine ⟨6521400389239461159380041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139123208303775171400107541 6521400389239461159380041)
      ·
        refine ⟨4891050291929595869535031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521400389239461159380041 4891050291929595869535031)
        ·
          refine ⟨7336575437894393804302547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891050291929595869535031 7336575437894393804302547)
          ·
            refine ⟨11004863156841590706453821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336575437894393804302547 11004863156841590706453821)
            ·
              refine ⟨4126823683815596514920183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11004863156841590706453821 4126823683815596514920183)
              ·
                refine ⟨6190235525723394772380275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126823683815596514920183 6190235525723394772380275)
                ·
                  refine ⟨9285353288585092158570413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190235525723394772380275 9285353288585092158570413)
                  ·
                    refine ⟨3482007483219409559463905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285353288585092158570413 3482007483219409559463905)
                    ·
                      refine ⟨2611505612414557169597929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482007483219409559463905 2611505612414557169597929)
                      ·
                        rfl

theorem cell23_5085889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5085889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085889 prefixEnd_5085889 := by exact prefixLift 5085889
  have htrace : WordTrace (prefixWord ++ tailWord_5085889) baseStart_5085889 baseEnd_5085889 := by
    simpa [prefixWord, tailWord_5085889, baseEnd_5085889] using wordTrace_append hprefix tailTrace_5085889
  have hstable : (prefixWord ++ tailWord_5085889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085889).length < 2 ^ (prefixWord ++ tailWord_5085889).sum := by decide
  have hdescent : baseEnd_5085889 < baseStart_5085889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085911 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_5085911 : Nat := 118140960795 + 5085911 * 2 ^ 59
def prefixEnd_5085911 : Nat := 4983230072969 + 3 ^ 40 * 5085911 * 2
def baseEnd_5085911 : Nat := 2611516908988956083522827

theorem tailTrace_5085911 : CollatzResearch.WordTrace tailWord_5085911 prefixEnd_5085911 2611516908988956083522827 := by
  unfold tailWord_5085911
  simp only [CollatzResearch.WordTrace]
  refine ⟨185498413477620526290777587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123665608985080350860518391 185498413477620526290777587)
  ·
    refine ⟨278247620216430789436166381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185498413477620526290777587 278247620216430789436166381)
    ·
      refine ⟨104342857581161546038562393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278247620216430789436166381 104342857581161546038562393)
      ·
        refine ⟨78257143185871159528921795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104342857581161546038562393 78257143185871159528921795)
        ·
          refine ⟨117385714778806739293382693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78257143185871159528921795 117385714778806739293382693)
          ·
            refine ⟨22009821521026263617509255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117385714778806739293382693 22009821521026263617509255)
            ·
              refine ⟨33014732281539395426263883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22009821521026263617509255 33014732281539395426263883)
              ·
                refine ⟨49522098422309093139395825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33014732281539395426263883 49522098422309093139395825)
                ·
                  refine ⟨37141573816731819854546869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49522098422309093139395825 37141573816731819854546869)
                  ·
                    refine ⟨3482022545318608111363769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37141573816731819854546869 3482022545318608111363769)
                    ·
                      refine ⟨2611516908988956083522827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482022545318608111363769 2611516908988956083522827)
                      ·
                        rfl

theorem cell23_5085911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_5085911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085911 prefixEnd_5085911 := by exact prefixLift 5085911
  have htrace : WordTrace (prefixWord ++ tailWord_5085911) baseStart_5085911 baseEnd_5085911 := by
    simpa [prefixWord, tailWord_5085911, baseEnd_5085911] using wordTrace_append hprefix tailTrace_5085911
  have hstable : (prefixWord ++ tailWord_5085911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085911).length < 2 ^ (prefixWord ++ tailWord_5085911).sum := by decide
  have hdescent : baseEnd_5085911 < baseStart_5085911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085914 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_5085914 : Nat := 118140960795 + 5085914 * 2 ^ 59
def prefixEnd_5085914 : Nat := 4983230072969 + 3 ^ 40 * 5085914 * 2
def baseEnd_5085914 : Nat := 2611518449430919571785313

theorem tailTrace_5085914 : CollatzResearch.WordTrace tailWord_5085914 prefixEnd_5085914 2611518449430919571785313 := by
  unfold tailWord_5085914
  simp only [CollatzResearch.WordTrace]
  refine ⟨46374630724152414450784199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123665681931073105202091197 46374630724152414450784199)
  ·
    refine ⟨69561946086228621676176299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46374630724152414450784199 69561946086228621676176299)
    ·
      refine ⟨104342919129342932514264449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69561946086228621676176299 104342919129342932514264449)
      ·
        refine ⟨78257189347007199385698337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104342919129342932514264449 78257189347007199385698337)
        ·
          refine ⟨58692892010255399539273753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78257189347007199385698337 58692892010255399539273753)
          ·
            refine ⟨44019669007691549654455315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58692892010255399539273753 44019669007691549654455315)
            ·
              refine ⟨66029503511537324481682973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44019669007691549654455315 66029503511537324481682973)
              ·
                refine ⟨24761063816826496680631115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66029503511537324481682973 24761063816826496680631115)
                ·
                  refine ⟨37141595725239745020946673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24761063816826496680631115 37141595725239745020946673)
                  ·
                    refine ⟨27856196793929808765710005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37141595725239745020946673 27856196793929808765710005)
                    ·
                      refine ⟨2611518449430919571785313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27856196793929808765710005 2611518449430919571785313)
                      ·
                        rfl

theorem cell23_5085914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_5085914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085914 prefixEnd_5085914 := by exact prefixLift 5085914
  have htrace : WordTrace (prefixWord ++ tailWord_5085914) baseStart_5085914 baseEnd_5085914 := by
    simpa [prefixWord, tailWord_5085914, baseEnd_5085914] using wordTrace_append hprefix tailTrace_5085914
  have hstable : (prefixWord ++ tailWord_5085914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085914).length < 2 ^ (prefixWord ++ tailWord_5085914).sum := by decide
  have hdescent : baseEnd_5085914 < baseStart_5085914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085938 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_5085938 : Nat := 118140960795 + 5085938 * 2 ^ 59
def prefixEnd_5085938 : Nat := 4983230072969 + 3 ^ 40 * 5085938 * 2
def baseEnd_5085938 : Nat := 870510257655542492628401

theorem tailTrace_5085938 : CollatzResearch.WordTrace tailWord_5085938 prefixEnd_5085938 870510257655542492628401 := by
  unfold tailWord_5085938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46374849562130677475502617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123666265499015139934673645 46374849562130677475502617)
  ·
    refine ⟨34781137171598008106626963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46374849562130677475502617 34781137171598008106626963)
    ·
      refine ⟨52171705757397012159940445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34781137171598008106626963 52171705757397012159940445)
      ·
        refine ⟨19564389659023879559977667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52171705757397012159940445 19564389659023879559977667)
        ·
          refine ⟨29346584488535819339966501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19564389659023879559977667 29346584488535819339966501)
          ·
            refine ⟨5502484591600466126243719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29346584488535819339966501 5502484591600466126243719)
            ·
              refine ⟨8253726887400699189365579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502484591600466126243719 8253726887400699189365579)
              ·
                refine ⟨12380590331101048784048369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253726887400699189365579 12380590331101048784048369)
                ·
                  refine ⟨9285442748325786588036277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12380590331101048784048369 9285442748325786588036277)
                  ·
                    refine ⟨870510257655542492628401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9285442748325786588036277 870510257655542492628401)
                    ·
                      rfl

theorem cell23_5085938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_5085938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085938 prefixEnd_5085938 := by exact prefixLift 5085938
  have htrace : WordTrace (prefixWord ++ tailWord_5085938) baseStart_5085938 baseEnd_5085938 := by
    simpa [prefixWord, tailWord_5085938, baseEnd_5085938] using wordTrace_append hprefix tailTrace_5085938
  have hstable : (prefixWord ++ tailWord_5085938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085938).length < 2 ^ (prefixWord ++ tailWord_5085938).sum := by decide
  have hdescent : baseEnd_5085938 < baseStart_5085938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5085961 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_5085961 : Nat := 118140960795 + 5085961 * 2 ^ 59
def prefixEnd_5085961 : Nat := 4983230072969 + 3 ^ 40 * 5085961 * 2
def baseEnd_5085961 : Nat := 2611542583021680887897597

theorem tailTrace_5085961 : CollatzResearch.WordTrace tailWord_5085961 prefixEnd_5085961 2611542583021680887897597 := by
  unfold tailWord_5085961
  simp only [CollatzResearch.WordTrace]
  refine ⟨185500237127439384830097737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123666824751626256553398491 185500237127439384830097737)
  ·
    refine ⟨139125177845579538622573303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185500237127439384830097737 139125177845579538622573303)
    ·
      refine ⟨208687766768369307933859955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139125177845579538622573303 208687766768369307933859955)
      ·
        refine ⟨313031650152553961900789933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208687766768369307933859955 313031650152553961900789933)
        ·
          refine ⟨117386868807207735712796225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313031650152553961900789933 117386868807207735712796225)
          ·
            refine ⟨88040151605405801784597169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117386868807207735712796225 88040151605405801784597169)
            ·
              refine ⟨66030113704054351338447877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88040151605405801784597169 66030113704054351338447877)
              ·
                refine ⟨12380646319510190875958977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66030113704054351338447877 12380646319510190875958977)
                ·
                  refine ⟨9285484739632643156969233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12380646319510190875958977 9285484739632643156969233)
                  ·
                    refine ⟨6964113554724482367726925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9285484739632643156969233 6964113554724482367726925)
                    ·
                      refine ⟨2611542583021680887897597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964113554724482367726925 2611542583021680887897597)
                      ·
                        rfl

theorem cell23_5085961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_5085961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5085961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5085961 prefixEnd_5085961 := by exact prefixLift 5085961
  have htrace : WordTrace (prefixWord ++ tailWord_5085961) baseStart_5085961 baseEnd_5085961 := by
    simpa [prefixWord, tailWord_5085961, baseEnd_5085961] using wordTrace_append hprefix tailTrace_5085961
  have hstable : (prefixWord ++ tailWord_5085961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5085961).length < 2 ^ (prefixWord ++ tailWord_5085961).sum := by decide
  have hdescent : baseEnd_5085961 < baseStart_5085961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5085961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086025 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_5086025 : Nat := 118140960795 + 5086025 * 2 ^ 59
def prefixEnd_5086025 : Nat := 4983230072969 + 3 ^ 40 * 5086025 * 2
def baseEnd_5086025 : Nat := 2611575445783568637497303

theorem tailTrace_5086025 : CollatzResearch.WordTrace tailWord_5086025 prefixEnd_5086025 2611575445783568637497303 := by
  unfold tailWord_5086025
  simp only [CollatzResearch.WordTrace]
  refine ⟨185502571399207523760427529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123668380932805015840285019 185502571399207523760427529)
  ·
    refine ⟨139126928549405642820320647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185502571399207523760427529 139126928549405642820320647)
    ·
      refine ⟨208690392824108464230480971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139126928549405642820320647 208690392824108464230480971)
      ·
        refine ⟨313035589236162696345721457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208690392824108464230480971 313035589236162696345721457)
        ·
          refine ⟨234776691927122022259291093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313035589236162696345721457 234776691927122022259291093)
          ·
            refine ⟨5502578717041922396702135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 234776691927122022259291093 5502578717041922396702135)
            ·
              refine ⟨8253868075562883595053203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502578717041922396702135 8253868075562883595053203)
              ·
                refine ⟨12380802113344325392579805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253868075562883595053203 12380802113344325392579805)
                ·
                  refine ⟨4642800792504122022217427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12380802113344325392579805 4642800792504122022217427)
                  ·
                    refine ⟨6964201188756183033326141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4642800792504122022217427 6964201188756183033326141)
                    ·
                      refine ⟨2611575445783568637497303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964201188756183033326141 2611575445783568637497303)
                      ·
                        rfl

theorem cell23_5086025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_5086025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086025 prefixEnd_5086025 := by exact prefixLift 5086025
  have htrace : WordTrace (prefixWord ++ tailWord_5086025) baseStart_5086025 baseEnd_5086025 := by
    simpa [prefixWord, tailWord_5086025, baseEnd_5086025] using wordTrace_append hprefix tailTrace_5086025
  have hstable : (prefixWord ++ tailWord_5086025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086025).length < 2 ^ (prefixWord ++ tailWord_5086025).sum := by decide
  have hdescent : baseEnd_5086025 < baseStart_5086025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086062 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5086062 : Nat := 118140960795 + 5086062 * 2 ^ 59
def prefixEnd_5086062 : Nat := 4983230072969 + 3 ^ 40 * 5086062 * 2
def baseEnd_5086062 : Nat := 870531481522594997578211

theorem tailTrace_5086062 : CollatzResearch.WordTrace tailWord_5086062 prefixEnd_5086062 870531481522594997578211 := by
  unfold tailWord_5086062
  simp only [CollatzResearch.WordTrace]
  refine ⟨23187990112509184884940555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123669280600048986053016293 23187990112509184884940555)
  ·
    refine ⟨34781985168763777327410833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23187990112509184884940555 34781985168763777327410833)
    ·
      refine ⟨26086488876572832995558125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34781985168763777327410833 26086488876572832995558125)
      ·
        refine ⟨9782433328714812373334297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26086488876572832995558125 9782433328714812373334297)
        ·
          refine ⟨7336824996536109280000723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782433328714812373334297 7336824996536109280000723)
          ·
            refine ⟨11005237494804163920001085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336824996536109280000723 11005237494804163920001085)
            ·
              refine ⟨4126964060551561470000407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11005237494804163920001085 4126964060551561470000407)
              ·
                refine ⟨6190446090827342205000611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126964060551561470000407 6190446090827342205000611)
                ·
                  refine ⟨9285669136241013307500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190446090827342205000611 9285669136241013307500917)
                  ·
                    refine ⟨870531481522594997578211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9285669136241013307500917 870531481522594997578211)
                    ·
                      rfl

theorem cell23_5086062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5086062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086062 prefixEnd_5086062 := by exact prefixLift 5086062
  have htrace : WordTrace (prefixWord ++ tailWord_5086062) baseStart_5086062 baseEnd_5086062 := by
    simpa [prefixWord, tailWord_5086062, baseEnd_5086062] using wordTrace_append hprefix tailTrace_5086062
  have hstable : (prefixWord ++ tailWord_5086062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086062).length < 2 ^ (prefixWord ++ tailWord_5086062).sum := by decide
  have hdescent : baseEnd_5086062 < baseStart_5086062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086065 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_5086065 : Nat := 118140960795 + 5086065 * 2 ^ 59
def prefixEnd_5086065 : Nat := 4983230072969 + 3 ^ 40 * 5086065 * 2
def baseEnd_5086065 : Nat := 2611595985009748480997119

theorem tailTrace_5086065 : CollatzResearch.WordTrace tailWord_5086065 prefixEnd_5086065 2611595985009748480997119 := by
  unfold tailWord_5086065
  simp only [CollatzResearch.WordTrace]
  refine ⟨185504030319062610591883649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123669353546041740394589099 185504030319062610591883649)
  ·
    refine ⟨139128022739296957943912737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185504030319062610591883649 139128022739296957943912737)
    ·
      refine ⟨104346017054472718457934553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139128022739296957943912737 104346017054472718457934553)
      ·
        refine ⟨78259512790854538843450915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104346017054472718457934553 78259512790854538843450915)
        ·
          refine ⟨117389269186281808265176373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78259512790854538843450915 117389269186281808265176373)
          ·
            refine ⟨11005243986213919524860285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117389269186281808265176373 11005243986213919524860285)
            ·
              refine ⟨4126966494830219821822607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11005243986213919524860285 4126966494830219821822607)
              ·
                refine ⟨6190449742245329732733911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126966494830219821822607 6190449742245329732733911)
                ·
                  refine ⟨9285674613367994599100867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190449742245329732733911 9285674613367994599100867)
                  ·
                    refine ⟨13928511920051991898651301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9285674613367994599100867 13928511920051991898651301)
                    ·
                      refine ⟨2611595985009748480997119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13928511920051991898651301 2611595985009748480997119)
                      ·
                        rfl

theorem cell23_5086065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_5086065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086065 prefixEnd_5086065 := by exact prefixLift 5086065
  have htrace : WordTrace (prefixWord ++ tailWord_5086065) baseStart_5086065 baseEnd_5086065 := by
    simpa [prefixWord, tailWord_5086065, baseEnd_5086065] using wordTrace_append hprefix tailTrace_5086065
  have hstable : (prefixWord ++ tailWord_5086065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086065).length < 2 ^ (prefixWord ++ tailWord_5086065).sum := by decide
  have hdescent : baseEnd_5086065 < baseStart_5086065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086088 : List Nat := [2, 1, 3, 3, 2, 3, 1, 8]
def baseStart_5086088 : Nat := 118140960795 + 5086088 * 2 ^ 59
def prefixEnd_5086088 : Nat := 4983230072969 + 3 ^ 40 * 5086088 * 2
def baseEnd_5086088 : Nat := 96726214632029699667019

theorem tailTrace_5086088 : CollatzResearch.WordTrace tailWord_5086088 prefixEnd_5086088 96726214632029699667019 := by
  unfold tailWord_5086088
  simp only [CollatzResearch.WordTrace]
  refine ⟨92752434598989642759985459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123669912798652857013313945 92752434598989642759985459)
  ·
    refine ⟨139128651898484464139978189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92752434598989642759985459 139128651898484464139978189)
    ·
      refine ⟨52173244461931674052491821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139128651898484464139978189 52173244461931674052491821)
      ·
        refine ⟨19564966673224377769684433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52173244461931674052491821 19564966673224377769684433)
        ·
          refine ⟨14673725004918283327263325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19564966673224377769684433 14673725004918283327263325)
          ·
            refine ⟨5502646876844356247723747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14673725004918283327263325 5502646876844356247723747)
            ·
              refine ⟨8253970315266534371585621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502646876844356247723747 8253970315266534371585621)
              ·
                refine ⟨96726214632029699667019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8253970315266534371585621 96726214632029699667019)
                ·
                  rfl

theorem cell23_5086088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 8].length) (baseStart_5086088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086088 prefixEnd_5086088 := by exact prefixLift 5086088
  have htrace : WordTrace (prefixWord ++ tailWord_5086088) baseStart_5086088 baseEnd_5086088 := by
    simpa [prefixWord, tailWord_5086088, baseEnd_5086088] using wordTrace_append hprefix tailTrace_5086088
  have hstable : (prefixWord ++ tailWord_5086088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086088).length < 2 ^ (prefixWord ++ tailWord_5086088).sum := by decide
  have hdescent : baseEnd_5086088 < baseStart_5086088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086119 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5086119 : Nat := 118140960795 + 5086119 * 2 ^ 59
def prefixEnd_5086119 : Nat := 4983230072969 + 3 ^ 40 * 5086119 * 2
def baseEnd_5086119 : Nat := 2611623712965091269721871

theorem tailTrace_5086119 : CollatzResearch.WordTrace tailWord_5086119 prefixEnd_5086119 2611623712965091269721871 := by
  unfold tailWord_5086119
  simp only [CollatzResearch.WordTrace]
  refine ⟨185505999860866977814349411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123670666573911318542899607 185505999860866977814349411)
  ·
    refine ⟨278258999791300466721524117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185505999860866977814349411 278258999791300466721524117)
    ·
      refine ⟨13043390615217209377571443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 278258999791300466721524117 13043390615217209377571443)
      ·
        refine ⟨19565085922825814066357165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13043390615217209377571443 19565085922825814066357165)
        ·
          refine ⟨7336907221059680274883937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19565085922825814066357165 7336907221059680274883937)
          ·
            refine ⟨5502680415794760206162953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336907221059680274883937 5502680415794760206162953)
            ·
              refine ⟨4127010311846070154622215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502680415794760206162953 4127010311846070154622215)
              ·
                refine ⟨6190515467769105231933323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127010311846070154622215 6190515467769105231933323)
                ·
                  refine ⟨9285773201653657847899985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190515467769105231933323 9285773201653657847899985)
                  ·
                    refine ⟨6964329901240243385924989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9285773201653657847899985 6964329901240243385924989)
                    ·
                      refine ⟨2611623712965091269721871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964329901240243385924989 2611623712965091269721871)
                      ·
                        rfl

theorem cell23_5086119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5086119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086119 prefixEnd_5086119 := by exact prefixLift 5086119
  have htrace : WordTrace (prefixWord ++ tailWord_5086119) baseStart_5086119 baseEnd_5086119 := by
    simpa [prefixWord, tailWord_5086119, baseEnd_5086119] using wordTrace_append hprefix tailTrace_5086119
  have hstable : (prefixWord ++ tailWord_5086119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086119).length < 2 ^ (prefixWord ++ tailWord_5086119).sum := by decide
  have hdescent : baseEnd_5086119 < baseStart_5086119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086155 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 4, 2]
def baseStart_5086155 : Nat := 118140960795 + 5086155 * 2 ^ 59
def prefixEnd_5086155 : Nat := 4983230072969 + 3 ^ 40 * 5086155 * 2
def baseEnd_5086155 : Nat := 2611642198268653128871705

theorem tailTrace_5086155 : CollatzResearch.WordTrace tailWord_5086155 prefixEnd_5086155 2611642198268653128871705 := by
  unfold tailWord_5086155
  simp only [CollatzResearch.WordTrace]
  refine ⟨185507312888736555962659919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123671541925824370641773279 185507312888736555962659919)
  ·
    refine ⟨278260969333104833943989879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185507312888736555962659919 278260969333104833943989879)
    ·
      refine ⟨417391453999657250915984819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278260969333104833943989879 417391453999657250915984819)
      ·
        refine ⟨626087180999485876373977229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417391453999657250915984819 626087180999485876373977229)
        ·
          refine ⟨234782692874807203640241461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 626087180999485876373977229 234782692874807203640241461)
          ·
            refine ⟨22010877457013175341272637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234782692874807203640241461 22010877457013175341272637)
            ·
              refine ⟨8254079046379940752977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22010877457013175341272637 8254079046379940752977239)
              ·
                refine ⟨12381118569569911129465859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254079046379940752977239 12381118569569911129465859)
                ·
                  refine ⟨18571677854354866694198789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12381118569569911129465859 18571677854354866694198789)
                  ·
                    refine ⟨3482189597691537505162273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18571677854354866694198789 3482189597691537505162273)
                    ·
                      refine ⟨2611642198268653128871705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482189597691537505162273 2611642198268653128871705)
                      ·
                        rfl

theorem cell23_5086155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4, 2].length) (baseStart_5086155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086155 prefixEnd_5086155 := by exact prefixLift 5086155
  have htrace : WordTrace (prefixWord ++ tailWord_5086155) baseStart_5086155 baseEnd_5086155 := by
    simpa [prefixWord, tailWord_5086155, baseEnd_5086155] using wordTrace_append hprefix tailTrace_5086155
  have hstable : (prefixWord ++ tailWord_5086155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086155).length < 2 ^ (prefixWord ++ tailWord_5086155).sum := by decide
  have hdescent : baseEnd_5086155 < baseStart_5086155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086161 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 7]
def baseStart_5086161 : Nat := 118140960795 + 5086161 * 2 ^ 59
def prefixEnd_5086161 : Nat := 4983230072969 + 3 ^ 40 * 5086161 * 2
def baseEnd_5086161 : Nat := 290182808794731122821853

theorem tailTrace_5086161 : CollatzResearch.WordTrace tailWord_5086161 prefixEnd_5086161 290182808794731122821853 := by
  unfold tailWord_5086161
  simp only [CollatzResearch.WordTrace]
  refine ⟨185507531726714818987378337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123671687817809879324918891 185507531726714818987378337)
  ·
    refine ⟨139130648795036114240533753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185507531726714818987378337 139130648795036114240533753)
    ·
      refine ⟨104347986596277085680400315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139130648795036114240533753 104347986596277085680400315)
      ·
        refine ⟨156521979894415628520600473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104347986596277085680400315 156521979894415628520600473)
        ·
          refine ⟨117391484920811721390450355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156521979894415628520600473 117391484920811721390450355)
          ·
            refine ⟨176087227381217582085675533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117391484920811721390450355 176087227381217582085675533)
            ·
              refine ⟨66032710267956593282128325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176087227381217582085675533 66032710267956593282128325)
              ·
                refine ⟨12381133175241861240399061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66032710267956593282128325 12381133175241861240399061)
                ·
                  refine ⟨290182808794731122821853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12381133175241861240399061 290182808794731122821853)
                  ·
                    rfl

theorem cell23_5086161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_5086161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086161 prefixEnd_5086161 := by exact prefixLift 5086161
  have htrace : WordTrace (prefixWord ++ tailWord_5086161) baseStart_5086161 baseEnd_5086161 := by
    simpa [prefixWord, tailWord_5086161, baseEnd_5086161] using wordTrace_append hprefix tailTrace_5086161
  have hstable : (prefixWord ++ tailWord_5086161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086161).length < 2 ^ (prefixWord ++ tailWord_5086161).sum := by decide
  have hdescent : baseEnd_5086161 < baseStart_5086161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086206 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5086206 : Nat := 118140960795 + 5086206 * 2 ^ 59
def prefixEnd_5086206 : Nat := 4983230072969 + 3 ^ 40 * 5086206 * 2
def baseEnd_5086206 : Nat := 2611668385782032429333971

theorem tailTrace_5086206 : CollatzResearch.WordTrace tailWord_5086206 prefixEnd_5086206 2611668385782032429333971 := by
  unfold tailWord_5086206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188646626443973959095809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123672782007701194448510981 23188646626443973959095809)
  ·
    refine ⟨17391484969832980469321857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23188646626443973959095809 17391484969832980469321857)
    ·
      refine ⟨13043613727374735351991393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17391484969832980469321857 13043613727374735351991393)
      ·
        refine ⟨9782710295531051513993545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13043613727374735351991393 9782710295531051513993545)
        ·
          refine ⟨7337032721648288635495159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782710295531051513993545 7337032721648288635495159)
          ·
            refine ⟨11005549082472432953242739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337032721648288635495159 11005549082472432953242739)
            ·
              refine ⟨16508323623708649429864109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11005549082472432953242739 16508323623708649429864109)
              ·
                refine ⟨6190621358890743536199041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16508323623708649429864109 6190621358890743536199041)
                ·
                  refine ⟨4642966019168057652149281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6190621358890743536199041 4642966019168057652149281)
                  ·
                    refine ⟨3482224514376043239111961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4642966019168057652149281 3482224514376043239111961)
                    ·
                      refine ⟨2611668385782032429333971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482224514376043239111961 2611668385782032429333971)
                      ·
                        rfl

theorem cell23_5086206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5086206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086206 prefixEnd_5086206 := by exact prefixLift 5086206
  have htrace : WordTrace (prefixWord ++ tailWord_5086206) baseStart_5086206 baseEnd_5086206 := by
    simpa [prefixWord, tailWord_5086206, baseEnd_5086206] using wordTrace_append hprefix tailTrace_5086206
  have hstable : (prefixWord ++ tailWord_5086206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086206).length < 2 ^ (prefixWord ++ tailWord_5086206).sum := by decide
  have hdescent : baseEnd_5086206 < baseStart_5086206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086245 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_5086245 : Nat := 118140960795 + 5086245 * 2 ^ 59
def prefixEnd_5086245 : Nat := 4983230072969 + 3 ^ 40 * 5086245 * 2
def baseEnd_5086245 : Nat := 2611688411527557776746291

theorem tailTrace_5086245 : CollatzResearch.WordTrace tailWord_5086245 prefixEnd_5086245 2611688411527557776746291 := by
  unfold tailWord_5086245
  simp only [CollatzResearch.WordTrace]
  refine ⟨185510595458410501333436189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123673730305607000888957459 185510595458410501333436189)
  ·
    refine ⟨69566473296903938000038571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185510595458410501333436189 69566473296903938000038571)
    ·
      refine ⟨104349709945355907000057857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69566473296903938000038571 104349709945355907000057857)
      ·
        refine ⟨78262282459016930250043393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104349709945355907000057857 78262282459016930250043393)
        ·
          refine ⟨58696711844262697687532545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78262282459016930250043393 58696711844262697687532545)
          ·
            refine ⟨44022533883197023265649409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58696711844262697687532545 44022533883197023265649409)
            ·
              refine ⟨33016900412397767449237057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44022533883197023265649409 33016900412397767449237057)
              ·
                refine ⟨24762675309298325586927793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33016900412397767449237057 24762675309298325586927793)
                ·
                  refine ⟨18572006481973744190195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24762675309298325586927793 18572006481973744190195845)
                  ·
                    refine ⟨3482251215370077035661721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18572006481973744190195845 3482251215370077035661721)
                    ·
                      refine ⟨2611688411527557776746291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482251215370077035661721 2611688411527557776746291)
                      ·
                        rfl

theorem cell23_5086245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_5086245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086245 prefixEnd_5086245 := by exact prefixLift 5086245
  have htrace : WordTrace (prefixWord ++ tailWord_5086245) baseStart_5086245 baseEnd_5086245 := by
    simpa [prefixWord, tailWord_5086245, baseEnd_5086245] using wordTrace_append hprefix tailTrace_5086245
  have hstable : (prefixWord ++ tailWord_5086245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086245).length < 2 ^ (prefixWord ++ tailWord_5086245).sum := by decide
  have hdescent : baseEnd_5086245 < baseStart_5086245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086262 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5086262 : Nat := 118140960795 + 5086262 * 2 ^ 59
def prefixEnd_5086262 : Nat := 4983230072969 + 3 ^ 40 * 5086262 * 2
def baseEnd_5086262 : Nat := 2611697140698684210233713

theorem tailTrace_5086262 : CollatzResearch.WordTrace tailWord_5086262 prefixEnd_5086262 2611697140698684210233713 := by
  unfold tailWord_5086262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594450968709307077300315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123674143666232608824536693 11594450968709307077300315)
  ·
    refine ⟨17391676453063960615950473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11594450968709307077300315 17391676453063960615950473)
    ·
      refine ⟨13043757339797970461962855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17391676453063960615950473 13043757339797970461962855)
      ·
        refine ⟨19565636009696955692944283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13043757339797970461962855 19565636009696955692944283)
        ·
          refine ⟨29348454014545433539416425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19565636009696955692944283 29348454014545433539416425)
          ·
            refine ⟨22011340510909075154562319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29348454014545433539416425 22011340510909075154562319)
            ·
              refine ⟨33017010766363612731843479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22011340510909075154562319 33017010766363612731843479)
              ·
                refine ⟨49525516149545419097765219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33017010766363612731843479 49525516149545419097765219)
                ·
                  refine ⟨74288274224318128646647829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49525516149545419097765219 74288274224318128646647829)
                  ·
                    refine ⟨3482262854264912280311617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74288274224318128646647829 3482262854264912280311617)
                    ·
                      refine ⟨2611697140698684210233713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482262854264912280311617 2611697140698684210233713)
                      ·
                        rfl

theorem cell23_5086262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5086262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086262 prefixEnd_5086262 := by exact prefixLift 5086262
  have htrace : WordTrace (prefixWord ++ tailWord_5086262) baseStart_5086262 baseEnd_5086262 := by
    simpa [prefixWord, tailWord_5086262, baseEnd_5086262] using wordTrace_append hprefix tailTrace_5086262
  have hstable : (prefixWord ++ tailWord_5086262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086262).length < 2 ^ (prefixWord ++ tailWord_5086262).sum := by decide
  have hdescent : baseEnd_5086262 < baseStart_5086262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086295 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_5086295 : Nat := 118140960795 + 5086295 * 2 ^ 59
def prefixEnd_5086295 : Nat := 4983230072969 + 3 ^ 40 * 5086295 * 2
def baseEnd_5086295 : Nat := 2611714085560282581121061

theorem tailTrace_5086295 : CollatzResearch.WordTrace tailWord_5086295 prefixEnd_5086295 2611714085560282581121061 := by
  unfold tailWord_5086295
  simp only [CollatzResearch.WordTrace]
  refine ⟨185512419108229359872756339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123674946072152906581837559 185512419108229359872756339)
  ·
    refine ⟨278268628662344039809134509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185512419108229359872756339 278268628662344039809134509)
    ·
      refine ⟨104350735748379014928425441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278268628662344039809134509 104350735748379014928425441)
      ·
        refine ⟨78263051811284261196319081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104350735748379014928425441 78263051811284261196319081)
        ·
          refine ⟨58697288858463195897239311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78263051811284261196319081 58697288858463195897239311)
          ·
            refine ⟨88045933287694793845858967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58697288858463195897239311 88045933287694793845858967)
            ·
              refine ⟨132068899931542190768788451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88045933287694793845858967 132068899931542190768788451)
              ·
                refine ⟨198103349897313286153182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132068899931542190768788451 198103349897313286153182677)
                ·
                  refine ⟨4643047263218280144215219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 198103349897313286153182677 4643047263218280144215219)
                  ·
                    refine ⟨6964570894827420216322829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4643047263218280144215219 6964570894827420216322829)
                    ·
                      refine ⟨2611714085560282581121061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964570894827420216322829 2611714085560282581121061)
                      ·
                        rfl

theorem cell23_5086295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_5086295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086295 prefixEnd_5086295 := by exact prefixLift 5086295
  have htrace : WordTrace (prefixWord ++ tailWord_5086295) baseStart_5086295 baseEnd_5086295 := by
    simpa [prefixWord, tailWord_5086295, baseEnd_5086295] using wordTrace_append hprefix tailTrace_5086295
  have hstable : (prefixWord ++ tailWord_5086295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086295).length < 2 ^ (prefixWord ++ tailWord_5086295).sum := by decide
  have hdescent : baseEnd_5086295 < baseStart_5086295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086298 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_5086298 : Nat := 118140960795 + 5086298 * 2 ^ 59
def prefixEnd_5086298 : Nat := 4983230072969 + 3 ^ 40 * 5086298 * 2
def baseEnd_5086298 : Nat := 870571875334082023127849

theorem tailTrace_5086298 : CollatzResearch.WordTrace tailWord_5086298 prefixEnd_5086298 870571875334082023127849 := by
  unfold tailWord_5086298
  simp only [CollatzResearch.WordTrace]
  refine ⟨46378132131804622846278887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123675019018145660923410365 46378132131804622846278887)
  ·
    refine ⟨69567198197706934269418331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46378132131804622846278887 69567198197706934269418331)
    ·
      refine ⟨104350797296560401404127497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69567198197706934269418331 104350797296560401404127497)
      ·
        refine ⟨78263097972420301053095623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104350797296560401404127497 78263097972420301053095623)
        ·
          refine ⟨117394646958630451579643435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78263097972420301053095623 117394646958630451579643435)
          ·
            refine ⟨176091970437945677369465153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117394646958630451579643435 176091970437945677369465153)
            ·
              refine ⟨132068977828459258027098865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176091970437945677369465153 132068977828459258027098865)
              ·
                refine ⟨99051733371344443520324149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132068977828459258027098865 99051733371344443520324149)
                ·
                  refine ⟨9286100003563541580030389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99051733371344443520324149 9286100003563541580030389)
                  ·
                    refine ⟨870571875334082023127849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9286100003563541580030389 870571875334082023127849)
                    ·
                      rfl

theorem cell23_5086298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_5086298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086298 prefixEnd_5086298 := by exact prefixLift 5086298
  have htrace : WordTrace (prefixWord ++ tailWord_5086298) baseStart_5086298 baseEnd_5086298 := by
    simpa [prefixWord, tailWord_5086298, baseEnd_5086298] using wordTrace_append hprefix tailTrace_5086298
  have hstable : (prefixWord ++ tailWord_5086298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086298).length < 2 ^ (prefixWord ++ tailWord_5086298).sum := by decide
  have hdescent : baseEnd_5086298 < baseStart_5086298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086345 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_5086345 : Nat := 118140960795 + 5086345 * 2 ^ 59
def prefixEnd_5086345 : Nat := 4983230072969 + 3 ^ 40 * 5086345 * 2
def baseEnd_5086345 : Nat := 870579919864335795165277

theorem tailTrace_5086345 : CollatzResearch.WordTrace tailWord_5086345 prefixEnd_5086345 870579919864335795165277 := by
  unfold tailWord_5086345
  simp only [CollatzResearch.WordTrace]
  refine ⟨185514242758048218412076489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123676161838698812274717659 185514242758048218412076489)
  ·
    refine ⟨139135682068536163809057367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185514242758048218412076489 139135682068536163809057367)
    ·
      refine ⟨208703523102804245713586051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139135682068536163809057367 208703523102804245713586051)
      ·
        refine ⟨313055284654206368570379077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208703523102804245713586051 313055284654206368570379077)
        ·
          refine ⟨58697865872663694106946077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313055284654206368570379077 58697865872663694106946077)
          ·
            refine ⟨22011699702248885290104779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58697865872663694106946077 22011699702248885290104779)
            ·
              refine ⟨33017549553373327935157169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22011699702248885290104779 33017549553373327935157169)
              ·
                refine ⟨24763162165029995951367877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33017549553373327935157169 24763162165029995951367877)
                ·
                  refine ⟨4643092905943124240881477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24763162165029995951367877 4643092905943124240881477)
                  ·
                    refine ⟨870579919864335795165277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643092905943124240881477 870579919864335795165277)
                    ·
                      rfl

theorem cell23_5086345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_5086345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086345 prefixEnd_5086345 := by exact prefixLift 5086345
  have htrace : WordTrace (prefixWord ++ tailWord_5086345) baseStart_5086345 baseEnd_5086345 := by
    simpa [prefixWord, tailWord_5086345, baseEnd_5086345] using wordTrace_append hprefix tailTrace_5086345
  have hstable : (prefixWord ++ tailWord_5086345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086345).length < 2 ^ (prefixWord ++ tailWord_5086345).sum := by decide
  have hdescent : baseEnd_5086345 < baseStart_5086345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086362 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_5086362 : Nat := 118140960795 + 5086362 * 2 ^ 59
def prefixEnd_5086362 : Nat := 4983230072969 + 3 ^ 40 * 5086362 * 2
def baseEnd_5086362 : Nat := 870582829588044606327751

theorem tailTrace_5086362 : CollatzResearch.WordTrace tailWord_5086362 prefixEnd_5086362 870582829588044606327751 := by
  unfold tailWord_5086362
  simp only [CollatzResearch.WordTrace]
  refine ⟨46378715699746657578861335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123676575199324420210296893 46378715699746657578861335)
  ·
    refine ⟨69568073549619986368292003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46378715699746657578861335 69568073549619986368292003)
    ·
      refine ⟨104352110324429979552438005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69568073549619986368292003 104352110324429979552438005)
      ·
        refine ⟨9783010342915310583041063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104352110324429979552438005 9783010342915310583041063)
        ·
          refine ⟨14674515514372965874561595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783010342915310583041063 14674515514372965874561595)
          ·
            refine ⟨22011773271559448811842393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14674515514372965874561595 22011773271559448811842393)
            ·
              refine ⟨16508829953669586608881795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22011773271559448811842393 16508829953669586608881795)
              ·
                refine ⟨24763244930504379913322693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16508829953669586608881795 24763244930504379913322693)
                ·
                  refine ⟨4643108424469571233748005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24763244930504379913322693 4643108424469571233748005)
                  ·
                    refine ⟨870582829588044606327751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643108424469571233748005 870582829588044606327751)
                    ·
                      rfl

theorem cell23_5086362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_5086362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086362 prefixEnd_5086362 := by exact prefixLift 5086362
  have htrace : WordTrace (prefixWord ++ tailWord_5086362) baseStart_5086362 baseEnd_5086362 := by
    simpa [prefixWord, tailWord_5086362, baseEnd_5086362] using wordTrace_append hprefix tailTrace_5086362
  have hstable : (prefixWord ++ tailWord_5086362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086362).length < 2 ^ (prefixWord ++ tailWord_5086362).sum := by decide
  have hdescent : baseEnd_5086362 < baseStart_5086362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086375 : List Nat := [1, 1, 6, 2, 1, 1, 1, 10]
def baseStart_5086375 : Nat := 118140960795 + 5086375 * 2 ^ 59
def prefixEnd_5086375 : Nat := 4983230072969 + 3 ^ 40 * 5086375 * 2
def baseEnd_5086375 : Nat := 96731672741208972893359

theorem tailTrace_5086375 : CollatzResearch.WordTrace tailWord_5086375 prefixEnd_5086375 96731672741208972893359 := by
  unfold tailWord_5086375
  simp only [CollatzResearch.WordTrace]
  refine ⟨185515336947939533535668579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123676891298626355690445719 185515336947939533535668579)
  ·
    refine ⟨278273005421909300303502869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185515336947939533535668579 278273005421909300303502869)
    ·
      refine ⟨13044047129151998451726697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 278273005421909300303502869 13044047129151998451726697)
      ·
        refine ⟨9783035346863998838795023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13044047129151998451726697 9783035346863998838795023)
        ·
          refine ⟨14674553020295998258192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783035346863998838795023 14674553020295998258192535)
          ·
            refine ⟨22011829530443997387288803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14674553020295998258192535 22011829530443997387288803)
            ·
              refine ⟨33017744295665996080933205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22011829530443997387288803 33017744295665996080933205)
              ·
                refine ⟨96731672741208972893359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33017744295665996080933205 96731672741208972893359)
                ·
                  rfl

theorem cell23_5086375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 10].length) (baseStart_5086375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086375 prefixEnd_5086375 := by exact prefixLift 5086375
  have htrace : WordTrace (prefixWord ++ tailWord_5086375) baseStart_5086375 baseEnd_5086375 := by
    simpa [prefixWord, tailWord_5086375, baseEnd_5086375] using wordTrace_append hprefix tailTrace_5086375
  have hstable : (prefixWord ++ tailWord_5086375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086375).length < 2 ^ (prefixWord ++ tailWord_5086375).sum := by decide
  have hdescent : baseEnd_5086375 < baseStart_5086375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086413 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5086413 : Nat := 118140960795 + 5086413 * 2 ^ 59
def prefixEnd_5086413 : Nat := 4983230072969 + 3 ^ 40 * 5086413 * 2
def baseEnd_5086413 : Nat := 870591558759171039815173

theorem tailTrace_5086413 : CollatzResearch.WordTrace tailWord_5086413 prefixEnd_5086413 870591558759171039815173 := by
  unfold tailWord_5086413
  simp only [CollatzResearch.WordTrace]
  refine ⟨185516722921801866025551893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123677815281201244017034595 185516722921801866025551893)
  ·
    refine ⟨8696096386959462469947745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185516722921801866025551893 8696096386959462469947745)
    ·
      refine ⟨6522072290219596852460809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8696096386959462469947745 6522072290219596852460809)
      ·
        refine ⟨4891554217664697639345607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6522072290219596852460809 4891554217664697639345607)
        ·
          refine ⟨7337331326497046459018411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891554217664697639345607 7337331326497046459018411)
          ·
            refine ⟨11005996989745569688527617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337331326497046459018411 11005996989745569688527617)
            ·
              refine ⟨8254497742309177266395713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11005996989745569688527617 8254497742309177266395713)
              ·
                refine ⟨6190873306731882949796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254497742309177266395713 6190873306731882949796785)
                ·
                  refine ⟨4643154980048912212347589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6190873306731882949796785 4643154980048912212347589)
                  ·
                    refine ⟨870591558759171039815173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643154980048912212347589 870591558759171039815173)
                    ·
                      rfl

theorem cell23_5086413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5086413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086413 prefixEnd_5086413 := by exact prefixLift 5086413
  have htrace : WordTrace (prefixWord ++ tailWord_5086413) baseStart_5086413 baseEnd_5086413 := by
    simpa [prefixWord, tailWord_5086413, baseEnd_5086413] using wordTrace_append hprefix tailTrace_5086413
  have hstable : (prefixWord ++ tailWord_5086413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086413).length < 2 ^ (prefixWord ++ tailWord_5086413).sum := by decide
  have hdescent : baseEnd_5086413 < baseStart_5086413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086420 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5086420 : Nat := 118140960795 + 5086420 * 2 ^ 59
def prefixEnd_5086420 : Nat := 4983230072969 + 3 ^ 40 * 5086420 * 2
def baseEnd_5086420 : Nat := 2611778270642094592057987

theorem tailTrace_5086420 : CollatzResearch.WordTrace tailWord_5086420 prefixEnd_5086420 2611778270642094592057987 := by
  unfold tailWord_5086420
  simp only [CollatzResearch.WordTrace]
  refine ⟨92758489116388253110528357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123677985488517670814037809 92758489116388253110528357)
  ·
    refine ⟨17392216709322797458224067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92758489116388253110528357 17392216709322797458224067)
    ·
      refine ⟨26088325063984196187336101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17392216709322797458224067 26088325063984196187336101)
      ·
        refine ⟨4891560949497036785125519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26088325063984196187336101 4891560949497036785125519)
        ·
          refine ⟨7337341424245555177688279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891560949497036785125519 7337341424245555177688279)
          ·
            refine ⟨11006012136368332766532419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337341424245555177688279 11006012136368332766532419)
            ·
              refine ⟨16509018204552499149798629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006012136368332766532419 16509018204552499149798629)
              ·
                refine ⟨3095440913353593590587243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16509018204552499149798629 3095440913353593590587243)
                ·
                  refine ⟨4643161370030390385880865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095440913353593590587243 4643161370030390385880865)
                  ·
                    refine ⟨3482371027522792789410649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643161370030390385880865 3482371027522792789410649)
                    ·
                      refine ⟨2611778270642094592057987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482371027522792789410649 2611778270642094592057987)
                      ·
                        rfl

theorem cell23_5086420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5086420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086420 prefixEnd_5086420 := by exact prefixLift 5086420
  have htrace : WordTrace (prefixWord ++ tailWord_5086420) baseStart_5086420 baseEnd_5086420 := by
    simpa [prefixWord, tailWord_5086420, baseEnd_5086420] using wordTrace_append hprefix tailTrace_5086420
  have hstable : (prefixWord ++ tailWord_5086420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086420).length < 2 ^ (prefixWord ++ tailWord_5086420).sum := by decide
  have hdescent : baseEnd_5086420 < baseStart_5086420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086476 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_5086476 : Nat := 118140960795 + 5086476 * 2 ^ 59
def prefixEnd_5086476 : Nat := 4983230072969 + 3 ^ 40 * 5086476 * 2
def baseEnd_5086476 : Nat := 2611807025558746372957729

theorem tailTrace_5086476 : CollatzResearch.WordTrace tailWord_5086476 prefixEnd_5086476 2611807025558746372957729 := by
  unfold tailWord_5086476
  simp only [CollatzResearch.WordTrace]
  refine ⟨92759510360286813892547641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123679347147049085190063521 92759510360286813892547641)
  ·
    refine ⟨69569632770215110419410731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92759510360286813892547641 69569632770215110419410731)
    ·
      refine ⟨104354449155322665629116097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69569632770215110419410731 104354449155322665629116097)
      ·
        refine ⟨78265836866491999221837073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104354449155322665629116097 78265836866491999221837073)
        ·
          refine ⟨58699377649868999416377805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78265836866491999221837073 58699377649868999416377805)
          ·
            refine ⟨22012266618700874781141677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58699377649868999416377805 22012266618700874781141677)
            ·
              refine ⟨8254599982012828042928129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22012266618700874781141677 8254599982012828042928129)
              ·
                refine ⟨6190949986509621032196097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254599982012828042928129 6190949986509621032196097)
                ·
                  refine ⟨4643212489882215774147073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6190949986509621032196097 4643212489882215774147073)
                  ·
                    refine ⟨3482409367411661830610305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643212489882215774147073 3482409367411661830610305)
                    ·
                      refine ⟨2611807025558746372957729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482409367411661830610305 2611807025558746372957729)
                      ·
                        rfl

theorem cell23_5086476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_5086476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086476 prefixEnd_5086476 := by exact prefixLift 5086476
  have htrace : WordTrace (prefixWord ++ tailWord_5086476) baseStart_5086476 baseEnd_5086476 := by
    simpa [prefixWord, tailWord_5086476, baseEnd_5086476] using wordTrace_append hprefix tailTrace_5086476
  have hstable : (prefixWord ++ tailWord_5086476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086476).length < 2 ^ (prefixWord ++ tailWord_5086476).sum := by decide
  have hdescent : baseEnd_5086476 < baseStart_5086476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086492 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5086492 : Nat := 118140960795 + 5086492 * 2 ^ 59
def prefixEnd_5086492 : Nat := 4983230072969 + 3 ^ 40 * 5086492 * 2
def baseEnd_5086492 : Nat := 2611815241249218310357655

theorem tailTrace_5086492 : CollatzResearch.WordTrace tailWord_5086492 prefixEnd_5086492 2611815241249218310357655 := by
  unfold tailWord_5086492
  simp only [CollatzResearch.WordTrace]
  refine ⟨92759802144257831258838865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123679736192343775011785153 92759802144257831258838865)
  ·
    refine ⟨69569851608193373444129149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92759802144257831258838865 69569851608193373444129149)
    ·
      refine ⟨26088694353072515041548431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69569851608193373444129149 26088694353072515041548431)
      ·
        refine ⟨39133041529608772562322647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26088694353072515041548431 39133041529608772562322647)
        ·
          refine ⟨58699562294413158843483971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39133041529608772562322647 58699562294413158843483971)
          ·
            refine ⟨88049343441619738265225957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58699562294413158843483971 88049343441619738265225957)
            ·
              refine ⟨16509251895303700924729867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88049343441619738265225957 16509251895303700924729867)
              ·
                refine ⟨24763877842955551387094801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16509251895303700924729867 24763877842955551387094801)
                ·
                  refine ⟨18572908382216663540321101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24763877842955551387094801 18572908382216663540321101)
                  ·
                    refine ⟨6964840643331248827620413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18572908382216663540321101 6964840643331248827620413)
                    ·
                      refine ⟨2611815241249218310357655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964840643331248827620413 2611815241249218310357655)
                      ·
                        rfl

theorem cell23_5086492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5086492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086492 prefixEnd_5086492 := by exact prefixLift 5086492
  have htrace : WordTrace (prefixWord ++ tailWord_5086492) baseStart_5086492 baseEnd_5086492 := by
    simpa [prefixWord, tailWord_5086492, baseEnd_5086492] using wordTrace_append hprefix tailTrace_5086492
  have hstable : (prefixWord ++ tailWord_5086492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086492).length < 2 ^ (prefixWord ++ tailWord_5086492).sum := by decide
  have hdescent : baseEnd_5086492 < baseStart_5086492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086529 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5086529 : Nat := 118140960795 + 5086529 * 2 ^ 59
def prefixEnd_5086529 : Nat := 4983230072969 + 3 ^ 40 * 5086529 * 2
def baseEnd_5086529 : Nat := 870611413344478221864995

theorem tailTrace_5086529 : CollatzResearch.WordTrace tailWord_5086529 prefixEnd_5086529 870611413344478221864995 := by
  unfold tailWord_5086529
  simp only [CollatzResearch.WordTrace]
  refine ⟨185520953789381617836774641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123680635859587745224516427 185520953789381617836774641)
  ·
    refine ⟨139140715342036213377580981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185520953789381617836774641 139140715342036213377580981)
    ·
      refine ⟨13044442063315895004148217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139140715342036213377580981 13044442063315895004148217)
      ·
        refine ⟨9783331547486921253111163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13044442063315895004148217 9783331547486921253111163)
        ·
          refine ⟨14674997321230381879666745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783331547486921253111163 14674997321230381879666745)
          ·
            refine ⟨11006247990922786409750059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14674997321230381879666745 11006247990922786409750059)
            ·
              refine ⟨16509371986384179614625089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006247990922786409750059 16509371986384179614625089)
              ·
                refine ⟨12382028989788134710968817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16509371986384179614625089 12382028989788134710968817)
                ·
                  refine ⟨9286521742341101033226613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12382028989788134710968817 9286521742341101033226613)
                  ·
                    refine ⟨870611413344478221864995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9286521742341101033226613 870611413344478221864995)
                    ·
                      rfl

theorem cell23_5086529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5086529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086529 prefixEnd_5086529 := by exact prefixLift 5086529
  have htrace : WordTrace (prefixWord ++ tailWord_5086529) baseStart_5086529 baseEnd_5086529 := by
    simpa [prefixWord, tailWord_5086529, baseEnd_5086529] using wordTrace_append hprefix tailTrace_5086529
  have hstable : (prefixWord ++ tailWord_5086529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086529).length < 2 ^ (prefixWord ++ tailWord_5086529).sum := by decide
  have hdescent : baseEnd_5086529 < baseStart_5086529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086552 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_5086552 : Nat := 118140960795 + 5086552 * 2 ^ 59
def prefixEnd_5086552 : Nat := 4983230072969 + 3 ^ 40 * 5086552 * 2
def baseEnd_5086552 : Nat := 2611846050088488075607379

theorem tailTrace_5086552 : CollatzResearch.WordTrace tailWord_5086552 prefixEnd_5086552 2611846050088488075607379 := by
  unfold tailWord_5086552
  simp only [CollatzResearch.WordTrace]
  refine ⟨92760896334149146382430955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123681195112198861843241273 92760896334149146382430955)
  ·
    refine ⟨139141344501223719573646433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92760896334149146382430955 139141344501223719573646433)
    ·
      refine ⟨104356008375917789680234825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139141344501223719573646433 104356008375917789680234825)
      ·
        refine ⟨78267006281938342260176119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104356008375917789680234825 78267006281938342260176119)
        ·
          refine ⟨117400509422907513390264179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78267006281938342260176119 117400509422907513390264179)
          ·
            refine ⟨176100764134361270085396269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117400509422907513390264179 176100764134361270085396269)
            ·
              refine ⟨66037786550385476282023601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176100764134361270085396269 66037786550385476282023601)
              ·
                refine ⟨49528339912789107211517701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66037786550385476282023601 49528339912789107211517701)
                ·
                  refine ⟨9286563733647957602159569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49528339912789107211517701 9286563733647957602159569)
                  ·
                    refine ⟨6964922800235968201619677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9286563733647957602159569 6964922800235968201619677)
                    ·
                      refine ⟨2611846050088488075607379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6964922800235968201619677 2611846050088488075607379)
                      ·
                        rfl

theorem cell23_5086552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_5086552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086552 prefixEnd_5086552 := by exact prefixLift 5086552
  have htrace : WordTrace (prefixWord ++ tailWord_5086552) baseStart_5086552 baseEnd_5086552 := by
    simpa [prefixWord, tailWord_5086552, baseEnd_5086552] using wordTrace_append hprefix tailTrace_5086552
  have hstable : (prefixWord ++ tailWord_5086552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086552).length < 2 ^ (prefixWord ++ tailWord_5086552).sum := by decide
  have hdescent : baseEnd_5086552 < baseStart_5086552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086593 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5086593 : Nat := 118140960795 + 5086593 * 2 ^ 59
def prefixEnd_5086593 : Nat := 4983230072969 + 3 ^ 40 * 5086593 * 2
def baseEnd_5086593 : Nat := 870622367598440805064897

theorem tailTrace_5086593 : CollatzResearch.WordTrace tailWord_5086593 prefixEnd_5086593 870622367598440805064897 := by
  unfold tailWord_5086593
  simp only [CollatzResearch.WordTrace]
  refine ⟨185523288061149756767104433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123682192040766504511402955 185523288061149756767104433)
  ·
    refine ⟨139142466045862317575328325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185523288061149756767104433 139142466045862317575328325)
    ·
      refine ⟨26089212383599184545374061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139142466045862317575328325 26089212383599184545374061)
      ·
        refine ⟨9783454643849694204515273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26089212383599184545374061 9783454643849694204515273)
        ·
          refine ⟨7337590982887270653386455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9783454643849694204515273 7337590982887270653386455)
          ·
            refine ⟨11006386474330905980079683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337590982887270653386455 11006386474330905980079683)
            ·
              refine ⟨16509579711496358970119525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006386474330905980079683 16509579711496358970119525)
              ·
                refine ⟨3095546195905567306897411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16509579711496358970119525 3095546195905567306897411)
                ·
                  refine ⟨4643319293858350960346117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095546195905567306897411 4643319293858350960346117)
                  ·
                    refine ⟨870622367598440805064897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643319293858350960346117 870622367598440805064897)
                    ·
                      rfl

theorem cell23_5086593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5086593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086593 prefixEnd_5086593 := by exact prefixLift 5086593
  have htrace : WordTrace (prefixWord ++ tailWord_5086593) baseStart_5086593 baseEnd_5086593 := by
    simpa [prefixWord, tailWord_5086593, baseEnd_5086593] using wordTrace_append hprefix tailTrace_5086593
  have hstable : (prefixWord ++ tailWord_5086593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086593).length < 2 ^ (prefixWord ++ tailWord_5086593).sum := by decide
  have hdescent : baseEnd_5086593 < baseStart_5086593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086620 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5086620 : Nat := 118140960795 + 5086620 * 2 ^ 59
def prefixEnd_5086620 : Nat := 4983230072969 + 3 ^ 40 * 5086620 * 2
def baseEnd_5086620 : Nat := 2611880966772993809557067

theorem tailTrace_5086620 : CollatzResearch.WordTrace tailWord_5086620 prefixEnd_5086620 2611880966772993809557067 := by
  unfold tailWord_5086620
  simp only [CollatzResearch.WordTrace]
  refine ⟨92762136416025970189168657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123682848554701293585558209 92762136416025970189168657)
  ·
    refine ⟨69571602312019477641876493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92762136416025970189168657 69571602312019477641876493)
    ·
      refine ⟨26089350867007304115703685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69571602312019477641876493 26089350867007304115703685)
      ·
        refine ⟨4891753287563869521694441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26089350867007304115703685 4891753287563869521694441)
        ·
          refine ⟨3668814965672902141270831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4891753287563869521694441 3668814965672902141270831)
          ·
            refine ⟨5503222448509353211906247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668814965672902141270831 5503222448509353211906247)
            ·
              refine ⟨8254833672764029817859371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5503222448509353211906247 8254833672764029817859371)
              ·
                refine ⟨12382250509146044726789057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254833672764029817859371 12382250509146044726789057)
                ·
                  refine ⟨9286687881859533545091793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12382250509146044726789057 9286687881859533545091793)
                  ·
                    refine ⟨6965015911394650158818845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9286687881859533545091793 6965015911394650158818845)
                    ·
                      refine ⟨2611880966772993809557067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965015911394650158818845 2611880966772993809557067)
                      ·
                        rfl

theorem cell23_5086620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5086620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086620 prefixEnd_5086620 := by exact prefixLift 5086620
  have htrace : WordTrace (prefixWord ++ tailWord_5086620) baseStart_5086620 baseEnd_5086620 := by
    simpa [prefixWord, tailWord_5086620, baseEnd_5086620] using wordTrace_append hprefix tailTrace_5086620
  have hstable : (prefixWord ++ tailWord_5086620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086620).length < 2 ^ (prefixWord ++ tailWord_5086620).sum := by decide
  have hdescent : baseEnd_5086620 < baseStart_5086620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086626 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5086626 : Nat := 118140960795 + 5086626 * 2 ^ 59
def prefixEnd_5086626 : Nat := 4983230072969 + 3 ^ 40 * 5086626 * 2
def baseEnd_5086626 : Nat := 2611884047656920786082039

theorem tailTrace_5086626 : CollatzResearch.WordTrace tailWord_5086626 prefixEnd_5086626 2611884047656920786082039 := by
  unfold tailWord_5086626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46381122917507550850763933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123682994446686802268703821 46381122917507550850763933)
  ·
    refine ⟨17392921094065331569036475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46381122917507550850763933 17392921094065331569036475)
    ·
      refine ⟨26089381641097997353554713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17392921094065331569036475 26089381641097997353554713)
      ·
        refine ⟨19567036230823498015166035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26089381641097997353554713 19567036230823498015166035)
        ·
          refine ⟨29350554346235247022749053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19567036230823498015166035 29350554346235247022749053)
          ·
            refine ⟨11006457879838217633530895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29350554346235247022749053 11006457879838217633530895)
            ·
              refine ⟨16509686819757326450296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006457879838217633530895 16509686819757326450296343)
              ·
                refine ⟨24764530229635989675444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16509686819757326450296343 24764530229635989675444515)
                ·
                  refine ⟨37146795344453984513166773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24764530229635989675444515 37146795344453984513166773)
                  ·
                    refine ⟨3482512063542561048109385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37146795344453984513166773 3482512063542561048109385)
                    ·
                      refine ⟨2611884047656920786082039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482512063542561048109385 2611884047656920786082039)
                      ·
                        rfl

theorem cell23_5086626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5086626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086626 prefixEnd_5086626 := by exact prefixLift 5086626
  have htrace : WordTrace (prefixWord ++ tailWord_5086626) baseStart_5086626 baseEnd_5086626 := by
    simpa [prefixWord, tailWord_5086626, baseEnd_5086626] using wordTrace_append hprefix tailTrace_5086626
  have hstable : (prefixWord ++ tailWord_5086626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086626).length < 2 ^ (prefixWord ++ tailWord_5086626).sum := by decide
  have hdescent : baseEnd_5086626 < baseStart_5086626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086656 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2]
def baseStart_5086656 : Nat := 118140960795 + 5086656 * 2 ^ 59
def prefixEnd_5086656 : Nat := 4983230072969 + 3 ^ 40 * 5086656 * 2
def baseEnd_5086656 : Nat := 2611899452076555668706901

theorem tailTrace_5086656 : CollatzResearch.WordTrace tailWord_5086656 prefixEnd_5086656 2611899452076555668706901 := by
  unfold tailWord_5086656
  simp only [CollatzResearch.WordTrace]
  refine ⟨92762792929960759263323911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123683723906614345684431881 92762792929960759263323911)
  ·
    refine ⟨139144189394941138894985867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92762792929960759263323911 139144189394941138894985867)
    ·
      refine ⟨208716284092411708342478801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139144189394941138894985867 208716284092411708342478801)
      ·
        refine ⟨156537213069308781256859101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208716284092411708342478801 156537213069308781256859101)
        ·
          refine ⟨58701454900990792971322163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156537213069308781256859101 58701454900990792971322163)
          ·
            refine ⟨88052182351486189456983245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58701454900990792971322163 88052182351486189456983245)
            ·
              refine ⟨33019568381807321046368717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88052182351486189456983245 33019568381807321046368717)
              ·
                refine ⟨12382338143177745392388269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33019568381807321046368717 12382338143177745392388269)
                ·
                  refine ⟨4643376803691654522145601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12382338143177745392388269 4643376803691654522145601)
                  ·
                    refine ⟨3482532602768740891609201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643376803691654522145601 3482532602768740891609201)
                    ·
                      refine ⟨2611899452076555668706901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482532602768740891609201 2611899452076555668706901)
                      ·
                        rfl

theorem cell23_5086656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_5086656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086656 prefixEnd_5086656 := by exact prefixLift 5086656
  have htrace : WordTrace (prefixWord ++ tailWord_5086656) baseStart_5086656 baseEnd_5086656 := by
    simpa [prefixWord, tailWord_5086656, baseEnd_5086656] using wordTrace_append hprefix tailTrace_5086656
  have hstable : (prefixWord ++ tailWord_5086656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086656).length < 2 ^ (prefixWord ++ tailWord_5086656).sum := by decide
  have hdescent : baseEnd_5086656 < baseStart_5086656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086749 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5086749 : Nat := 118140960795 + 5086749 * 2 ^ 59
def prefixEnd_5086749 : Nat := 4983230072969 + 3 ^ 40 * 5086749 * 2
def baseEnd_5086749 : Nat := 2611947205777423804843973

theorem tailTrace_5086749 : CollatzResearch.WordTrace tailWord_5086749 prefixEnd_5086749 2611947205777423804843973 := by
  unfold tailWord_5086749
  simp only [CollatzResearch.WordTrace]
  refine ⟨185528977848584595409783301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123685985232389730273188867 185528977848584595409783301)
  ·
    refine ⟨34786683346609611639334369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185528977848584595409783301 34786683346609611639334369)
    ·
      refine ⟨26090012509957208729500777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34786683346609611639334369 26090012509957208729500777)
      ·
        refine ⟨19567509382467906547125583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26090012509957208729500777 19567509382467906547125583)
        ·
          refine ⟨29351264073701859820688375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19567509382467906547125583 29351264073701859820688375)
          ·
            refine ⟨44026896110552789731032563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29351264073701859820688375 44026896110552789731032563)
            ·
              refine ⟨66040344165829184596548845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44026896110552789731032563 66040344165829184596548845)
              ·
                refine ⟨24765129062185944223705817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66040344165829184596548845 24765129062185944223705817)
                ·
                  refine ⟨18573846796639458167779363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24765129062185944223705817 18573846796639458167779363)
                  ·
                    refine ⟨27860770194959187251669045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18573846796639458167779363 27860770194959187251669045)
                    ·
                      refine ⟨2611947205777423804843973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27860770194959187251669045 2611947205777423804843973)
                      ·
                        rfl

theorem cell23_5086749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5086749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086749 prefixEnd_5086749 := by exact prefixLift 5086749
  have htrace : WordTrace (prefixWord ++ tailWord_5086749) baseStart_5086749 baseEnd_5086749 := by
    simpa [prefixWord, tailWord_5086749, baseEnd_5086749] using wordTrace_append hprefix tailTrace_5086749
  have hstable : (prefixWord ++ tailWord_5086749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086749).length < 2 ^ (prefixWord ++ tailWord_5086749).sum := by decide
  have hdescent : baseEnd_5086749 < baseStart_5086749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086766 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5086766 : Nat := 118140960795 + 5086766 * 2 ^ 59
def prefixEnd_5086766 : Nat := 4983230072969 + 3 ^ 40 * 5086766 * 2
def baseEnd_5086766 : Nat := 2611955934948550238331395

theorem tailTrace_5086766 : CollatzResearch.WordTrace tailWord_5086766 prefixEnd_5086766 2611955934948550238331395 := by
  unfold tailWord_5086766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23191199736190375914144019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123686398593015338208768101 23191199736190375914144019)
  ·
    refine ⟨34786799604285563871216029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23191199736190375914144019 34786799604285563871216029)
    ·
      refine ⟨13045049851607086451706011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34786799604285563871216029 13045049851607086451706011)
      ·
        refine ⟨19567574777410629677559017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13045049851607086451706011 19567574777410629677559017)
        ·
          refine ⟨14675681083057972258169263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19567574777410629677559017 14675681083057972258169263)
          ·
            refine ⟨22013521624586958387253895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14675681083057972258169263 22013521624586958387253895)
            ·
              refine ⟨33020282436880437580880843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22013521624586958387253895 33020282436880437580880843)
              ·
                refine ⟨49530423655320656371321265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33020282436880437580880843 49530423655320656371321265)
                ·
                  refine ⟨37147817741490492278490949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49530423655320656371321265 37147817741490492278490949)
                  ·
                    refine ⟨6965215826529467302217053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37147817741490492278490949 6965215826529467302217053)
                    ·
                      refine ⟨2611955934948550238331395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965215826529467302217053 2611955934948550238331395)
                      ·
                        rfl

theorem cell23_5086766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5086766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086766 prefixEnd_5086766 := by exact prefixLift 5086766
  have htrace : WordTrace (prefixWord ++ tailWord_5086766) baseStart_5086766 baseEnd_5086766 := by
    simpa [prefixWord, tailWord_5086766, baseEnd_5086766] using wordTrace_append hprefix tailTrace_5086766
  have hstable : (prefixWord ++ tailWord_5086766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086766).length < 2 ^ (prefixWord ++ tailWord_5086766).sum := by decide
  have hdescent : baseEnd_5086766 < baseStart_5086766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086896 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2]
def baseStart_5086896 : Nat := 118140960795 + 5086896 * 2 ^ 59
def prefixEnd_5086896 : Nat := 4983230072969 + 3 ^ 40 * 5086896 * 2
def baseEnd_5086896 : Nat := 2612022687433634729705797

theorem tailTrace_5086896 : CollatzResearch.WordTrace tailWord_5086896 prefixEnd_5086896 2612022687433634729705797 := by
  unfold tailWord_5086896
  simp only [CollatzResearch.WordTrace]
  refine ⟨92767169689526019757692271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123689559586034693010256361 92767169689526019757692271)
  ·
    refine ⟨139150754534289029636538407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92767169689526019757692271 139150754534289029636538407)
    ·
      refine ⟨208726131801433544454807611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139150754534289029636538407 208726131801433544454807611)
      ·
        refine ⟨313089197702150316682211417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208726131801433544454807611 313089197702150316682211417)
        ·
          refine ⟨234816898276612737511658563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313089197702150316682211417 234816898276612737511658563)
          ·
            refine ⟨352225347414919106267487845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234816898276612737511658563 352225347414919106267487845)
            ·
              refine ⟨66042252640297332425153971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 352225347414919106267487845 66042252640297332425153971)
              ·
                refine ⟨99063378960445998637730957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66042252640297332425153971 99063378960445998637730957)
                ·
                  refine ⟨37148767110167249489149109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99063378960445998637730957 37148767110167249489149109)
                  ·
                    refine ⟨3482696916578179639607729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37148767110167249489149109 3482696916578179639607729)
                    ·
                      refine ⟨2612022687433634729705797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482696916578179639607729 2612022687433634729705797)
                      ·
                        rfl

theorem cell23_5086896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2].length) (baseStart_5086896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086896 prefixEnd_5086896 := by exact prefixLift 5086896
  have htrace : WordTrace (prefixWord ++ tailWord_5086896) baseStart_5086896 baseEnd_5086896 := by
    simpa [prefixWord, tailWord_5086896, baseEnd_5086896] using wordTrace_append hprefix tailTrace_5086896
  have hstable : (prefixWord ++ tailWord_5086896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086896).length < 2 ^ (prefixWord ++ tailWord_5086896).sum := by decide
  have hdescent : baseEnd_5086896 < baseStart_5086896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086906 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_5086906 : Nat := 118140960795 + 5086906 * 2 ^ 59
def prefixEnd_5086906 : Nat := 4983230072969 + 3 ^ 40 * 5086906 * 2
def baseEnd_5086906 : Nat := 870675940746726563526917

theorem tailTrace_5086906 : CollatzResearch.WordTrace tailWord_5086906 prefixEnd_5086906 870675940746726563526917 := by
  unfold tailWord_5086906
  simp only [CollatzResearch.WordTrace]
  refine ⟨46383676027253952805812143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123689802739343874148832381 46383676027253952805812143)
  ·
    refine ⟨69575514040880929208718215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46383676027253952805812143 69575514040880929208718215)
    ·
      refine ⟨104363271061321393813077323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69575514040880929208718215 104363271061321393813077323)
      ·
        refine ⟨156544906591982090719615985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104363271061321393813077323 156544906591982090719615985)
        ·
          refine ⟨117408679943986568039711989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156544906591982090719615985 117408679943986568039711989)
          ·
            refine ⟨11007063744748740753722999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117408679943986568039711989 11007063744748740753722999)
            ·
              refine ⟨16510595617123111130584499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11007063744748740753722999 16510595617123111130584499)
              ·
                refine ⟨24765893425684666695876749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16510595617123111130584499 24765893425684666695876749)
                ·
                  refine ⟨9287210034631750010953781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24765893425684666695876749 9287210034631750010953781)
                  ·
                    refine ⟨870675940746726563526917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9287210034631750010953781 870675940746726563526917)
                    ·
                      rfl

theorem cell23_5086906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_5086906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086906 prefixEnd_5086906 := by exact prefixLift 5086906
  have htrace : WordTrace (prefixWord ++ tailWord_5086906) baseStart_5086906 baseEnd_5086906 := by
    simpa [prefixWord, tailWord_5086906, baseEnd_5086906] using wordTrace_append hprefix tailTrace_5086906
  have hstable : (prefixWord ++ tailWord_5086906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086906).length < 2 ^ (prefixWord ++ tailWord_5086906).sum := by decide
  have hdescent : baseEnd_5086906 < baseStart_5086906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086920 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_5086920 : Nat := 118140960795 + 5086920 * 2 ^ 59
def prefixEnd_5086920 : Nat := 4983230072969 + 3 ^ 40 * 5086920 * 2
def baseEnd_5086920 : Nat := 2612035010969342635805687

theorem tailTrace_5086920 : CollatzResearch.WordTrace tailWord_5086920 prefixEnd_5086920 2612035010969342635805687 := by
  unfold tailWord_5086920
  simp only [CollatzResearch.WordTrace]
  refine ⟨92767607365482545807129107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123690143153976727742838809 92767607365482545807129107)
  ·
    refine ⟨139151411048223818710693661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92767607365482545807129107 139151411048223818710693661)
    ·
      refine ⟨52181779143083932016510123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139151411048223818710693661 52181779143083932016510123)
      ·
        refine ⟨78272668714625898024765185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52181779143083932016510123 78272668714625898024765185)
        ·
          refine ⟨58704501535969423518573889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78272668714625898024765185 58704501535969423518573889)
          ·
            refine ⟨44028376151977067638930417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58704501535969423518573889 44028376151977067638930417)
            ·
              refine ⟨33021282113982800729197813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44028376151977067638930417 33021282113982800729197813)
              ·
                refine ⟨3095745198185887568362295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33021282113982800729197813 3095745198185887568362295)
                ·
                  refine ⟨4643617797278831352543443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095745198185887568362295 4643617797278831352543443)
                  ·
                    refine ⟨6965426695918247028815165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4643617797278831352543443 6965426695918247028815165)
                    ·
                      refine ⟨2612035010969342635805687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965426695918247028815165 2612035010969342635805687)
                      ·
                        rfl

theorem cell23_5086920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_5086920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086920 prefixEnd_5086920 := by exact prefixLift 5086920
  have htrace : WordTrace (prefixWord ++ tailWord_5086920) baseStart_5086920 baseEnd_5086920 := by
    simpa [prefixWord, tailWord_5086920, baseEnd_5086920] using wordTrace_append hprefix tailTrace_5086920
  have hstable : (prefixWord ++ tailWord_5086920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086920).length < 2 ^ (prefixWord ++ tailWord_5086920).sum := by decide
  have hdescent : baseEnd_5086920 < baseStart_5086920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086930 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5086930 : Nat := 118140960795 + 5086930 * 2 ^ 59
def prefixEnd_5086930 : Nat := 4983230072969 + 3 ^ 40 * 5086930 * 2
def baseEnd_5086930 : Nat := 2612040145775887596680641

theorem tailTrace_5086930 : CollatzResearch.WordTrace tailWord_5086930 prefixEnd_5086930 2612040145775887596680641 := by
  unfold tailWord_5086930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46383894865232215830530561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123690386307285908881414829 46383894865232215830530561)
  ·
    refine ⟨34787921148924161872897921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46383894865232215830530561 34787921148924161872897921)
    ·
      refine ⟨26090940861693121404673441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34787921148924161872897921 26090940861693121404673441)
      ·
        refine ⟨19568205646269841053505081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26090940861693121404673441 19568205646269841053505081)
        ·
          refine ⟨14676154234702380790128811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19568205646269841053505081 14676154234702380790128811)
          ·
            refine ⟨22014231352053571185193217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14676154234702380790128811 22014231352053571185193217)
            ·
              refine ⟨16510673514040178388894913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22014231352053571185193217 16510673514040178388894913)
              ·
                refine ⟨12383005135530133791671185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16510673514040178388894913 12383005135530133791671185)
                ·
                  refine ⟨9287253851647600343753389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12383005135530133791671185 9287253851647600343753389)
                  ·
                    refine ⟨3482720194367850128907521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9287253851647600343753389 3482720194367850128907521)
                    ·
                      refine ⟨2612040145775887596680641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482720194367850128907521 2612040145775887596680641)
                      ·
                        rfl

theorem cell23_5086930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5086930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086930 prefixEnd_5086930 := by exact prefixLift 5086930
  have htrace : WordTrace (prefixWord ++ tailWord_5086930) baseStart_5086930 baseEnd_5086930 := by
    simpa [prefixWord, tailWord_5086930, baseEnd_5086930] using wordTrace_append hprefix tailTrace_5086930
  have hstable : (prefixWord ++ tailWord_5086930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086930).length < 2 ^ (prefixWord ++ tailWord_5086930).sum := by decide
  have hdescent : baseEnd_5086930 < baseStart_5086930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086937 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 1, 1, 3]
def baseStart_5086937 : Nat := 118140960795 + 5086937 * 2 ^ 59
def prefixEnd_5086937 : Nat := 4983230072969 + 3 ^ 40 * 5086937 * 2
def baseEnd_5086937 : Nat := 2612043740140469069293109

theorem tailTrace_5086937 : CollatzResearch.WordTrace tailWord_5086937 prefixEnd_5086937 2612043740140469069293109 := by
  unfold tailWord_5086937
  simp only [CollatzResearch.WordTrace]
  refine ⟨185535834771903503517627065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123690556514602335678418043 185535834771903503517627065)
  ·
    refine ⟨139151876078927627638220299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185535834771903503517627065 139151876078927627638220299)
    ·
      refine ⟨208727814118391441457330449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139151876078927627638220299 208727814118391441457330449)
      ·
        refine ⟨156545860588793581092997837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208727814118391441457330449 156545860588793581092997837)
        ·
          refine ⟨58704697720797592909874189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156545860588793581092997837 58704697720797592909874189)
          ·
            refine ⟨22014261645299097341202821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58704697720797592909874189 22014261645299097341202821)
            ·
              refine ⟨4127674058493580751475529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22014261645299097341202821 4127674058493580751475529)
              ·
                refine ⟨3095755543870185563606647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127674058493580751475529 3095755543870185563606647)
                ·
                  refine ⟨4643633315805278345409971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095755543870185563606647 4643633315805278345409971)
                  ·
                    refine ⟨6965449973707917518114957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4643633315805278345409971 6965449973707917518114957)
                    ·
                      refine ⟨2612043740140469069293109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965449973707917518114957 2612043740140469069293109)
                      ·
                        rfl

theorem cell23_5086937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_5086937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086937 prefixEnd_5086937 := by exact prefixLift 5086937
  have htrace : WordTrace (prefixWord ++ tailWord_5086937) baseStart_5086937 baseEnd_5086937 := by
    simpa [prefixWord, tailWord_5086937, baseEnd_5086937] using wordTrace_append hprefix tailTrace_5086937
  have hstable : (prefixWord ++ tailWord_5086937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086937).length < 2 ^ (prefixWord ++ tailWord_5086937).sum := by decide
  have hdescent : baseEnd_5086937 < baseStart_5086937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086939 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_5086939 : Nat := 118140960795 + 5086939 * 2 ^ 59
def prefixEnd_5086939 : Nat := 4983230072969 + 3 ^ 40 * 5086939 * 2
def baseEnd_5086939 : Nat := 2612044767101778061468099

theorem tailTrace_5086939 : CollatzResearch.WordTrace tailWord_5086939 prefixEnd_5086939 2612044767101778061468099 := by
  unfold tailWord_5086939
  simp only [CollatzResearch.WordTrace]
  refine ⟨185535907717896257859199871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123690605145264171906133247 185535907717896257859199871)
  ·
    refine ⟨278303861576844386788799807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185535907717896257859199871 278303861576844386788799807)
    ·
      refine ⟨417455792365266580183199711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278303861576844386788799807 417455792365266580183199711)
      ·
        refine ⟨626183688547899870274799567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417455792365266580183199711 626183688547899870274799567)
        ·
          refine ⟨939275532821849805412199351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626183688547899870274799567 939275532821849805412199351)
          ·
            refine ⟨1408913299232774708118299027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939275532821849805412199351 1408913299232774708118299027)
            ·
              refine ⟨2113369948849162062177448541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408913299232774708118299027 2113369948849162062177448541)
              ·
                refine ⟨792513730818435773316543203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2113369948849162062177448541 792513730818435773316543203)
                ·
                  refine ⟨1188770596227653659974814805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792513730818435773316543203 1188770596227653659974814805)
                  ·
                    refine ⟨13930905424542816327829861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1188770596227653659974814805 13930905424542816327829861)
                    ·
                      refine ⟨2612044767101778061468099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13930905424542816327829861 2612044767101778061468099)
                      ·
                        rfl

theorem cell23_5086939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_5086939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086939 prefixEnd_5086939 := by exact prefixLift 5086939
  have htrace : WordTrace (prefixWord ++ tailWord_5086939) baseStart_5086939 baseEnd_5086939 := by
    simpa [prefixWord, tailWord_5086939, baseEnd_5086939] using wordTrace_append hprefix tailTrace_5086939
  have hstable : (prefixWord ++ tailWord_5086939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086939).length < 2 ^ (prefixWord ++ tailWord_5086939).sum := by decide
  have hdescent : baseEnd_5086939 < baseStart_5086939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086956 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_5086956 : Nat := 118140960795 + 5086956 * 2 ^ 59
def prefixEnd_5086956 : Nat := 4983230072969 + 3 ^ 40 * 5086956 * 2
def baseEnd_5086956 : Nat := 2612053496272904494955521

theorem tailTrace_5086956 : CollatzResearch.WordTrace tailWord_5086956 prefixEnd_5086956 2612053496272904494955521 := by
  unfold tailWord_5086956
  simp only [CollatzResearch.WordTrace]
  refine ⟨92768263879417334881284361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123691018505889779841712481 92768263879417334881284361)
  ·
    refine ⟨69576197909563001160963271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92768263879417334881284361 69576197909563001160963271)
    ·
      refine ⟨104364296864344501741444907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69576197909563001160963271 104364296864344501741444907)
      ·
        refine ⟨156546445296516752612167361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104364296864344501741444907 156546445296516752612167361)
        ·
          refine ⟨117409833972387564459125521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156546445296516752612167361 117409833972387564459125521)
          ·
            refine ⟨88057375479290673344344141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117409833972387564459125521 88057375479290673344344141)
            ·
              refine ⟨33021515804734002504129053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88057375479290673344344141 33021515804734002504129053)
              ·
                refine ⟨12383068426775250939048395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33021515804734002504129053 12383068426775250939048395)
                ·
                  refine ⟨18574602640162876408572593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383068426775250939048395 18574602640162876408572593)
                  ·
                    refine ⟨13930951980122157306429445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18574602640162876408572593 13930951980122157306429445)
                    ·
                      refine ⟨2612053496272904494955521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13930951980122157306429445 2612053496272904494955521)
                      ·
                        rfl

theorem cell23_5086956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_5086956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086956 prefixEnd_5086956 := by exact prefixLift 5086956
  have htrace : WordTrace (prefixWord ++ tailWord_5086956) baseStart_5086956 baseEnd_5086956 := by
    simpa [prefixWord, tailWord_5086956, baseEnd_5086956] using wordTrace_append hprefix tailTrace_5086956
  have hstable : (prefixWord ++ tailWord_5086956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086956).length < 2 ^ (prefixWord ++ tailWord_5086956).sum := by decide
  have hdescent : baseEnd_5086956 < baseStart_5086956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086964 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5086964 : Nat := 118140960795 + 5086964 * 2 ^ 59
def prefixEnd_5086964 : Nat := 4983230072969 + 3 ^ 40 * 5086964 * 2
def baseEnd_5086964 : Nat := 2612057604118140463655485

theorem tailTrace_5086964 : CollatzResearch.WordTrace tailWord_5086964 prefixEnd_5086964 2612057604118140463655485 := by
  unfold tailWord_5086964
  simp only [CollatzResearch.WordTrace]
  refine ⟨92768409771402843564429973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123691213028537124752573297 92768409771402843564429973)
  ·
    refine ⟨4348519208034508292082655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92768409771402843564429973 4348519208034508292082655)
    ·
      refine ⟨6522778812051762438123983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4348519208034508292082655 6522778812051762438123983)
      ·
        refine ⟨9784168218077643657185975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522778812051762438123983 9784168218077643657185975)
        ·
          refine ⟨14676252327116465485778963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784168218077643657185975 14676252327116465485778963)
          ·
            refine ⟨22014378490674698228668445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14676252327116465485778963 22014378490674698228668445)
            ·
              refine ⟨8255391934003011835750667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22014378490674698228668445 8255391934003011835750667)
              ·
                refine ⟨12383087901004517753626001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255391934003011835750667 12383087901004517753626001)
                ·
                  refine ⟨9287315925753388315219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12383087901004517753626001 9287315925753388315219501)
                  ·
                    refine ⟨3482743472157520618207313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9287315925753388315219501 3482743472157520618207313)
                    ·
                      refine ⟨2612057604118140463655485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482743472157520618207313 2612057604118140463655485)
                      ·
                        rfl

theorem cell23_5086964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5086964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086964 prefixEnd_5086964 := by exact prefixLift 5086964
  have htrace : WordTrace (prefixWord ++ tailWord_5086964) baseStart_5086964 baseEnd_5086964 := by
    simpa [prefixWord, tailWord_5086964, baseEnd_5086964] using wordTrace_append hprefix tailTrace_5086964
  have hstable : (prefixWord ++ tailWord_5086964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086964).length < 2 ^ (prefixWord ++ tailWord_5086964).sum := by decide
  have hdescent : baseEnd_5086964 < baseStart_5086964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086974 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_5086974 : Nat := 118140960795 + 5086974 * 2 ^ 59
def prefixEnd_5086974 : Nat := 4983230072969 + 3 ^ 40 * 5086974 * 2
def baseEnd_5086974 : Nat := 870687579641561808176813

theorem tailTrace_5086974 : CollatzResearch.WordTrace tailWord_5086974 prefixEnd_5086974 870687579641561808176813 := by
  unfold tailWord_5086974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192148034096182354590497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123691456181846305891149317 23192148034096182354590497)
  ·
    refine ⟨17394111025572136765942873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23192148034096182354590497 17394111025572136765942873)
    ·
      refine ⟨13045583269179102574457155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17394111025572136765942873 13045583269179102574457155)
      ·
        refine ⟨19568374903768653861685733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13045583269179102574457155 19568374903768653861685733)
        ·
          refine ⟨3669070294456622599066075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19568374903768653861685733 3669070294456622599066075)
          ·
            refine ⟨5503605441684933898599113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669070294456622599066075 5503605441684933898599113)
            ·
              refine ⟨4127704081263700423949335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5503605441684933898599113 4127704081263700423949335)
              ·
                refine ⟨6191556121895550635924003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127704081263700423949335 6191556121895550635924003)
                ·
                  refine ⟨9287334182843325953886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191556121895550635924003 9287334182843325953886005)
                  ·
                    refine ⟨870687579641561808176813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9287334182843325953886005 870687579641561808176813)
                    ·
                      rfl

theorem cell23_5086974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_5086974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086974 prefixEnd_5086974 := by exact prefixLift 5086974
  have htrace : WordTrace (prefixWord ++ tailWord_5086974) baseStart_5086974 baseEnd_5086974 := by
    simpa [prefixWord, tailWord_5086974, baseEnd_5086974] using wordTrace_append hprefix tailTrace_5086974
  have hstable : (prefixWord ++ tailWord_5086974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086974).length < 2 ^ (prefixWord ++ tailWord_5086974).sum := by decide
  have hdescent : baseEnd_5086974 < baseStart_5086974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086977 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5086977 : Nat := 118140960795 + 5086977 * 2 ^ 59
def prefixEnd_5086977 : Nat := 4983230072969 + 3 ^ 40 * 5086977 * 2
def baseEnd_5086977 : Nat := 2612064279366648912792925

theorem tailTrace_5086977 : CollatzResearch.WordTrace tailWord_5086977 prefixEnd_5086977 2612064279366648912792925 := by
  unfold tailWord_5086977
  simp only [CollatzResearch.WordTrace]
  refine ⟨185537293691758590349083185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123691529127839060232722123 185537293691758590349083185)
  ·
    refine ⟨139152970268818942761812389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185537293691758590349083185 139152970268818942761812389)
    ·
      refine ⟨26091181925403551767839823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139152970268818942761812389 26091181925403551767839823)
      ·
        refine ⟨39136772888105327651759735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26091181925403551767839823 39136772888105327651759735)
        ·
          refine ⟨58705159332157991477639603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39136772888105327651759735 58705159332157991477639603)
          ·
            refine ⟨88057738998236987216459405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58705159332157991477639603 88057738998236987216459405)
            ·
              refine ⟨33021652124338870206172277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88057738998236987216459405 33021652124338870206172277)
              ·
                refine ⟨3095779886656769081828651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33021652124338870206172277 3095779886656769081828651)
                ·
                  refine ⟨4643669829985153622742977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095779886656769081828651 4643669829985153622742977)
                  ·
                    refine ⟨3482752372488865217057233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643669829985153622742977 3482752372488865217057233)
                    ·
                      refine ⟨2612064279366648912792925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482752372488865217057233 2612064279366648912792925)
                      ·
                        rfl

theorem cell23_5086977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5086977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086977 prefixEnd_5086977 := by exact prefixLift 5086977
  have htrace : WordTrace (prefixWord ++ tailWord_5086977) baseStart_5086977 baseEnd_5086977 := by
    simpa [prefixWord, tailWord_5086977, baseEnd_5086977] using wordTrace_append hprefix tailTrace_5086977
  have hstable : (prefixWord ++ tailWord_5086977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086977).length < 2 ^ (prefixWord ++ tailWord_5086977).sum := by decide
  have hdescent : baseEnd_5086977 < baseStart_5086977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086980 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5086980 : Nat := 118140960795 + 5086980 * 2 ^ 59
def prefixEnd_5086980 : Nat := 4983230072969 + 3 ^ 40 * 5086980 * 2
def baseEnd_5086980 : Nat := 2612065819808612401055411

theorem tailTrace_5086980 : CollatzResearch.WordTrace tailWord_5086980 prefixEnd_5086980 2612065819808612401055411 := by
  unfold tailWord_5086980
  simp only [CollatzResearch.WordTrace]
  refine ⟨92768701555373860930721197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123691602073831814574294929 92768701555373860930721197)
  ·
    refine ⟨34788263083265197849020449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92768701555373860930721197 34788263083265197849020449)
    ·
      refine ⟨26091197312448898386765337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34788263083265197849020449 26091197312448898386765337)
      ·
        refine ⟨19568397984336673790074003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26091197312448898386765337 19568397984336673790074003)
        ·
          refine ⟨29352596976505010685111005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19568397984336673790074003 29352596976505010685111005)
          ·
            refine ⟨11007223866189379006916627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29352596976505010685111005 11007223866189379006916627)
            ·
              refine ⟨16510835799284068510374941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11007223866189379006916627 16510835799284068510374941)
              ·
                refine ⟨6191563424731525691390603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16510835799284068510374941 6191563424731525691390603)
                ·
                  refine ⟨9287345137097288537085905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191563424731525691390603 9287345137097288537085905)
                  ·
                    refine ⟨6965508852822966402814429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9287345137097288537085905 6965508852822966402814429)
                    ·
                      refine ⟨2612065819808612401055411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965508852822966402814429 2612065819808612401055411)
                      ·
                        rfl

theorem cell23_5086980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5086980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086980 prefixEnd_5086980 := by exact prefixLift 5086980
  have htrace : WordTrace (prefixWord ++ tailWord_5086980) baseStart_5086980 baseEnd_5086980 := by
    simpa [prefixWord, tailWord_5086980, baseEnd_5086980] using wordTrace_append hprefix tailTrace_5086980
  have hstable : (prefixWord ++ tailWord_5086980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086980).length < 2 ^ (prefixWord ++ tailWord_5086980).sum := by decide
  have hdescent : baseEnd_5086980 < baseStart_5086980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5086994 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5086994 : Nat := 118140960795 + 5086994 * 2 ^ 59
def prefixEnd_5086994 : Nat := 4983230072969 + 3 ^ 40 * 5086994 * 2
def baseEnd_5086994 : Nat := 2612073008537775346280347

theorem tailTrace_5086994 : CollatzResearch.WordTrace tailWord_5086994 prefixEnd_5086994 2612073008537775346280347 := by
  unfold tailWord_5086994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46384478433174250563113009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123691942488464668168301357 46384478433174250563113009)
  ·
    refine ⟨34788358824880687922334757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46384478433174250563113009 34788358824880687922334757)
    ·
      refine ⟨6522817279665128985437767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34788358824880687922334757 6522817279665128985437767)
      ·
        refine ⟨9784225919497693478156651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522817279665128985437767 9784225919497693478156651)
        ·
          refine ⟨14676338879246540217234977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784225919497693478156651 14676338879246540217234977)
          ·
            refine ⟨11007254159434905162926233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14676338879246540217234977 11007254159434905162926233)
            ·
              refine ⟨8255440619576178872194675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11007254159434905162926233 8255440619576178872194675)
              ·
                refine ⟨12383160929364268308292013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255440619576178872194675 12383160929364268308292013)
                ·
                  refine ⟨4643685348511600615609505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12383160929364268308292013 4643685348511600615609505)
                  ·
                    refine ⟨3482764011383700461707129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643685348511600615609505 3482764011383700461707129)
                    ·
                      refine ⟨2612073008537775346280347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482764011383700461707129 2612073008537775346280347)
                      ·
                        rfl

theorem cell23_5086994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5086994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5086994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5086994 prefixEnd_5086994 := by exact prefixLift 5086994
  have htrace : WordTrace (prefixWord ++ tailWord_5086994) baseStart_5086994 baseEnd_5086994 := by
    simpa [prefixWord, tailWord_5086994, baseEnd_5086994] using wordTrace_append hprefix tailTrace_5086994
  have hstable : (prefixWord ++ tailWord_5086994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5086994).length < 2 ^ (prefixWord ++ tailWord_5086994).sum := by decide
  have hdescent : baseEnd_5086994 < baseStart_5086994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5086994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087020 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_5087020 : Nat := 118140960795 + 5087020 * 2 ^ 59
def prefixEnd_5087020 : Nat := 4983230072969 + 3 ^ 40 * 5087020 * 2
def baseEnd_5087020 : Nat := 2612086359034792244555227

theorem tailTrace_5087020 : CollatzResearch.WordTrace tailWord_5087020 prefixEnd_5087020 2612086359034792244555227 := by
  unfold tailWord_5087020
  simp only [CollatzResearch.WordTrace]
  refine ⟨92769431015301404346449257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123692574687068539128599009 92769431015301404346449257)
  ·
    refine ⟨69577073261476053259836943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92769431015301404346449257 69577073261476053259836943)
    ·
      refine ⟨104365609892214079889755415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69577073261476053259836943 104365609892214079889755415)
      ·
        refine ⟨156548414838321119834633123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104365609892214079889755415 156548414838321119834633123)
        ·
          refine ⟨234822622257481679751949685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156548414838321119834633123 234822622257481679751949685)
          ·
            refine ⟨22014620836638907476745283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234822622257481679751949685 22014620836638907476745283)
            ·
              refine ⟨33021931254958361215117925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22014620836638907476745283 33021931254958361215117925)
              ·
                refine ⟨6191612110304692727834611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33021931254958361215117925 6191612110304692727834611)
                ·
                  refine ⟨9287418165457039091751917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191612110304692727834611 9287418165457039091751917)
                  ·
                    refine ⟨3482781812046389659406969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9287418165457039091751917 3482781812046389659406969)
                    ·
                      refine ⟨2612086359034792244555227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482781812046389659406969 2612086359034792244555227)
                      ·
                        rfl

theorem cell23_5087020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_5087020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087020 prefixEnd_5087020 := by exact prefixLift 5087020
  have htrace : WordTrace (prefixWord ++ tailWord_5087020) baseStart_5087020 baseEnd_5087020 := by
    simpa [prefixWord, tailWord_5087020, baseEnd_5087020] using wordTrace_append hprefix tailTrace_5087020
  have hstable : (prefixWord ++ tailWord_5087020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087020).length < 2 ^ (prefixWord ++ tailWord_5087020).sum := by decide
  have hdescent : baseEnd_5087020 < baseStart_5087020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087036 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_5087036 : Nat := 118140960795 + 5087036 * 2 ^ 59
def prefixEnd_5087036 : Nat := 4983230072969 + 3 ^ 40 * 5087036 * 2
def baseEnd_5087036 : Nat := 2612094574725264181955153

theorem tailTrace_5087036 : CollatzResearch.WordTrace tailWord_5087036 prefixEnd_5087036 2612094574725264181955153 := by
  unfold tailWord_5087036
  simp only [CollatzResearch.WordTrace]
  refine ⟨92769722799272421712740481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123692963732363228950320641 92769722799272421712740481)
  ·
    refine ⟨69577292099454316284555361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92769722799272421712740481 69577292099454316284555361)
    ·
      refine ⟨52182969074590737213416521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69577292099454316284555361 52182969074590737213416521)
      ·
        refine ⟨39137226805943052910062391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52182969074590737213416521 39137226805943052910062391)
        ·
          refine ⟨58705840208914579365093587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39137226805943052910062391 58705840208914579365093587)
          ·
            refine ⟨88058760313371869047640381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58705840208914579365093587 88058760313371869047640381)
            ·
              refine ⟨33022035117514450892865143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88058760313371869047640381 33022035117514450892865143)
              ·
                refine ⟨49533052676271676339297715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33022035117514450892865143 49533052676271676339297715)
                ·
                  refine ⟨74299579014407514508946573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49533052676271676339297715 74299579014407514508946573)
                  ·
                    refine ⟨27862342130402817940854965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74299579014407514508946573 27862342130402817940854965)
                    ·
                      refine ⟨2612094574725264181955153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27862342130402817940854965 2612094574725264181955153)
                      ·
                        rfl

theorem cell23_5087036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_5087036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087036 prefixEnd_5087036 := by exact prefixLift 5087036
  have htrace : WordTrace (prefixWord ++ tailWord_5087036) baseStart_5087036 baseEnd_5087036 := by
    simpa [prefixWord, tailWord_5087036, baseEnd_5087036] using wordTrace_append hprefix tailTrace_5087036
  have hstable : (prefixWord ++ tailWord_5087036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087036).length < 2 ^ (prefixWord ++ tailWord_5087036).sum := by decide
  have hdescent : baseEnd_5087036 < baseStart_5087036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087037 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5087037 : Nat := 118140960795 + 5087037 * 2 ^ 59
def prefixEnd_5087037 : Nat := 4983230072969 + 3 ^ 40 * 5087037 * 2
def baseEnd_5087037 : Nat := 2612095088205918678042649

theorem tailTrace_5087037 : CollatzResearch.WordTrace tailWord_5087037 prefixEnd_5087037 2612095088205918678042649 := by
  unfold tailWord_5087037
  simp only [CollatzResearch.WordTrace]
  refine ⟨185539482071541220596267365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123692988047694147064178243 185539482071541220596267365)
  ·
    refine ⟨34788652888413978861800131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185539482071541220596267365 34788652888413978861800131)
    ·
      refine ⟨52182979332620968292700197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34788652888413978861800131 52182979332620968292700197)
      ·
        refine ⟨9784308624866431554881287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52182979332620968292700197 9784308624866431554881287)
        ·
          refine ⟨14676462937299647332321931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784308624866431554881287 14676462937299647332321931)
          ·
            refine ⟨22014694405949470998482897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14676462937299647332321931 22014694405949470998482897)
            ·
              refine ⟨16511020804462103248862173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22014694405949470998482897 16511020804462103248862173)
              ·
                refine ⟨6191632801673288718323315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16511020804462103248862173 6191632801673288718323315)
                ·
                  refine ⟨9287449202509933077484973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191632801673288718323315 9287449202509933077484973)
                  ·
                    refine ⟨3482793450941224904056865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9287449202509933077484973 3482793450941224904056865)
                    ·
                      refine ⟨2612095088205918678042649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482793450941224904056865 2612095088205918678042649)
                      ·
                        rfl

theorem cell23_5087037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5087037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087037 prefixEnd_5087037 := by exact prefixLift 5087037
  have htrace : WordTrace (prefixWord ++ tailWord_5087037) baseStart_5087037 baseEnd_5087037 := by
    simpa [prefixWord, tailWord_5087037, baseEnd_5087037] using wordTrace_append hprefix tailTrace_5087037
  have hstable : (prefixWord ++ tailWord_5087037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087037).length < 2 ^ (prefixWord ++ tailWord_5087037).sum := by decide
  have hdescent : baseEnd_5087037 < baseStart_5087037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087050 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_5087050 : Nat := 118140960795 + 5087050 * 2 ^ 59
def prefixEnd_5087050 : Nat := 4983230072969 + 3 ^ 40 * 5087050 * 2
def baseEnd_5087050 : Nat := 2612101763454427127180089

theorem tailTrace_5087050 : CollatzResearch.WordTrace tailWord_5087050 prefixEnd_5087050 2612101763454427127180089 := by
  unfold tailWord_5087050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46384989055123530954122651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123693304146996082544327069 46384989055123530954122651)
  ·
    refine ⟨69577483582685296431183977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46384989055123530954122651 69577483582685296431183977)
    ·
      refine ⟨52183112687013972323387983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69577483582685296431183977 52183112687013972323387983)
      ·
        refine ⟨78274669030520958485081975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52183112687013972323387983 78274669030520958485081975)
        ·
          refine ⟨117412003545781437727622963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78274669030520958485081975 117412003545781437727622963)
          ·
            refine ⟨176118005318672156591434445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117412003545781437727622963 176118005318672156591434445)
            ·
              refine ⟨66044251994502058721787917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176118005318672156591434445 66044251994502058721787917)
              ·
                refine ⟨24766594497938272020670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66044251994502058721787917 24766594497938272020670469)
                ·
                  refine ⟨4643736468363426003875713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24766594497938272020670469 4643736468363426003875713)
                  ·
                    refine ⟨3482802351272569502906785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643736468363426003875713 3482802351272569502906785)
                    ·
                      refine ⟨2612101763454427127180089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482802351272569502906785 2612101763454427127180089)
                      ·
                        rfl

theorem cell23_5087050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_5087050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087050 prefixEnd_5087050 := by exact prefixLift 5087050
  have htrace : WordTrace (prefixWord ++ tailWord_5087050) baseStart_5087050 baseEnd_5087050 := by
    simpa [prefixWord, tailWord_5087050, baseEnd_5087050] using wordTrace_append hprefix tailTrace_5087050
  have hstable : (prefixWord ++ tailWord_5087050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087050).length < 2 ^ (prefixWord ++ tailWord_5087050).sum := by decide
  have hdescent : baseEnd_5087050 < baseStart_5087050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087107 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 5]
def baseStart_5087107 : Nat := 118140960795 + 5087107 * 2 ^ 59
def prefixEnd_5087107 : Nat := 4983230072969 + 3 ^ 40 * 5087107 * 2
def baseEnd_5087107 : Nat := 290236781316859267129703

theorem tailTrace_5087107 : CollatzResearch.WordTrace tailWord_5087107 prefixEnd_5087107 290236781316859267129703 := by
  unfold tailWord_5087107
  simp only [CollatzResearch.WordTrace]
  refine ⟨185542035181287622551315575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123694690120858415034210383 185542035181287622551315575)
  ·
    refine ⟨278313052771931433826973363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185542035181287622551315575 278313052771931433826973363)
    ·
      refine ⟨417469579157897150740460045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278313052771931433826973363 417469579157897150740460045)
      ·
        refine ⟨156551092184211431527672517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417469579157897150740460045 156551092184211431527672517)
        ·
          refine ⟨29353329784539643411438597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156551092184211431527672517 29353329784539643411438597)
          ·
            refine ⟨5503749334601183139644737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29353329784539643411438597 5503749334601183139644737)
            ·
              refine ⟨4127812000950887354733553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5503749334601183139644737 4127812000950887354733553)
              ·
                refine ⟨3095859000713165516050165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127812000950887354733553 3095859000713165516050165)
                ·
                  refine ⟨290236781316859267129703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3095859000713165516050165 290236781316859267129703)
                  ·
                    rfl

theorem cell23_5087107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 5].length) (baseStart_5087107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087107 prefixEnd_5087107 := by exact prefixLift 5087107
  have htrace : WordTrace (prefixWord ++ tailWord_5087107) baseStart_5087107 baseEnd_5087107 := by
    simpa [prefixWord, tailWord_5087107, baseEnd_5087107] using wordTrace_append hprefix tailTrace_5087107
  have hstable : (prefixWord ++ tailWord_5087107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087107).length < 2 ^ (prefixWord ++ tailWord_5087107).sum := by decide
  have hdescent : baseEnd_5087107 < baseStart_5087107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087116 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_5087116 : Nat := 118140960795 + 5087116 * 2 ^ 59
def prefixEnd_5087116 : Nat := 4983230072969 + 3 ^ 40 * 5087116 * 2
def baseEnd_5087116 : Nat := 870711884392541289651595

theorem tailTrace_5087116 : CollatzResearch.WordTrace tailWord_5087116 prefixEnd_5087116 870711884392541289651595 := by
  unfold tailWord_5087116
  simp only [CollatzResearch.WordTrace]
  refine ⟨92771181719127508544196601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123694908958836678058928801 92771181719127508544196601)
  ·
    refine ⟨69578386289345631408147451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92771181719127508544196601 69578386289345631408147451)
    ·
      refine ⟨104367579434018447112221177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69578386289345631408147451 104367579434018447112221177)
      ·
        refine ⟨78275684575513835334165883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104367579434018447112221177 78275684575513835334165883)
        ·
          refine ⟨117413526863270753001248825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78275684575513835334165883 117413526863270753001248825)
          ·
            refine ⟨88060145147453064750936619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117413526863270753001248825 88060145147453064750936619)
            ·
              refine ⟨132090217721179597126404929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88060145147453064750936619 132090217721179597126404929)
              ·
                refine ⟨99067663290884697844803697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132090217721179597126404929 99067663290884697844803697)
                ·
                  refine ⟨74300747468163523383602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99067663290884697844803697 74300747468163523383602773)
                  ·
                    refine ⟨870711884392541289651595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74300747468163523383602773 870711884392541289651595)
                    ·
                      rfl

theorem cell23_5087116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_5087116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087116 prefixEnd_5087116 := by exact prefixLift 5087116
  have htrace : WordTrace (prefixWord ++ tailWord_5087116) baseStart_5087116 baseEnd_5087116 := by
    simpa [prefixWord, tailWord_5087116, baseEnd_5087116] using wordTrace_append hprefix tailTrace_5087116
  have hstable : (prefixWord ++ tailWord_5087116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087116).length < 2 ^ (prefixWord ++ tailWord_5087116).sum := by decide
  have hdescent : baseEnd_5087116 < baseStart_5087116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087137 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_5087137 : Nat := 118140960795 + 5087137 * 2 ^ 59
def prefixEnd_5087137 : Nat := 4983230072969 + 3 ^ 40 * 5087137 * 2
def baseEnd_5087137 : Nat := 870715478757122762264063

theorem tailTrace_5087137 : CollatzResearch.WordTrace tailWord_5087137 prefixEnd_5087137 870715478757122762264063 := by
  unfold tailWord_5087137
  simp only [CollatzResearch.WordTrace]
  refine ⟨185543129371178937674907665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123695419580785958449938443 185543129371178937674907665)
  ·
    refine ⟨139157347028384203256180749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185543129371178937674907665 139157347028384203256180749)
    ·
      refine ⟨52184005135644076221067781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139157347028384203256180749 52184005135644076221067781)
      ·
        refine ⟨9784500962933264291450209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52184005135644076221067781 9784500962933264291450209)
        ·
          refine ⟨7338375722199948218587657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9784500962933264291450209 7338375722199948218587657)
          ·
            refine ⟨5503781791649961163940743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7338375722199948218587657 5503781791649961163940743)
            ·
              refine ⟨8255672687474941745911115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5503781791649961163940743 8255672687474941745911115)
              ·
                refine ⟨12383509031212412618866673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255672687474941745911115 12383509031212412618866673)
                ·
                  refine ⟨9287631773409309464150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12383509031212412618866673 9287631773409309464150005)
                  ·
                    refine ⟨870715478757122762264063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9287631773409309464150005 870715478757122762264063)
                    ·
                      rfl

theorem cell23_5087137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_5087137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087137 prefixEnd_5087137 := by exact prefixLift 5087137
  have htrace : WordTrace (prefixWord ++ tailWord_5087137) baseStart_5087137 baseEnd_5087137 := by
    simpa [prefixWord, tailWord_5087137, baseEnd_5087137] using wordTrace_append hprefix tailTrace_5087137
  have hstable : (prefixWord ++ tailWord_5087137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087137).length < 2 ^ (prefixWord ++ tailWord_5087137).sum := by decide
  have hdescent : baseEnd_5087137 < baseStart_5087137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087140 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_5087140 : Nat := 118140960795 + 5087140 * 2 ^ 59
def prefixEnd_5087140 : Nat := 4983230072969 + 3 ^ 40 * 5087140 * 2
def baseEnd_5087140 : Nat := 2612147976713331775054675

theorem tailTrace_5087140 : CollatzResearch.WordTrace tailWord_5087140 prefixEnd_5087140 2612147976713331775054675 := by
  unfold tailWord_5087140
  simp only [CollatzResearch.WordTrace]
  refine ⟨92771619395084034593633437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123695492526778712791511249 92771619395084034593633437)
  ·
    refine ⟨34789357273156512972612539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92771619395084034593633437 34789357273156512972612539)
    ·
      refine ⟨52184035909734769458918809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34789357273156512972612539 52184035909734769458918809)
      ·
        refine ⟨39138026932301077094189107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52184035909734769458918809 39138026932301077094189107)
        ·
          refine ⟨58707040398451615641283661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39138026932301077094189107 58707040398451615641283661)
          ·
            refine ⟨22015140149419355865481373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58707040398451615641283661 22015140149419355865481373)
            ·
              refine ⟨8255677556032258449555515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22015140149419355865481373 8255677556032258449555515)
              ·
                refine ⟨12383516334048387674333273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255677556032258449555515 12383516334048387674333273)
                ·
                  refine ⟨9287637250536290755749955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12383516334048387674333273 9287637250536290755749955)
                  ·
                    refine ⟨13931455875804436133624933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9287637250536290755749955 13931455875804436133624933)
                    ·
                      refine ⟨2612147976713331775054675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13931455875804436133624933 2612147976713331775054675)
                      ·
                        rfl

theorem cell23_5087140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_5087140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087140 prefixEnd_5087140 := by exact prefixLift 5087140
  have htrace : WordTrace (prefixWord ++ tailWord_5087140) baseStart_5087140 baseEnd_5087140 := by
    simpa [prefixWord, tailWord_5087140, baseEnd_5087140] using wordTrace_append hprefix tailTrace_5087140
  have hstable : (prefixWord ++ tailWord_5087140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087140).length < 2 ^ (prefixWord ++ tailWord_5087140).sum := by decide
  have hdescent : baseEnd_5087140 < baseStart_5087140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087153 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5087153 : Nat := 118140960795 + 5087153 * 2 ^ 59
def prefixEnd_5087153 : Nat := 4983230072969 + 3 ^ 40 * 5087153 * 2
def baseEnd_5087153 : Nat := 2612154651961840224192115

theorem tailTrace_5087153 : CollatzResearch.WordTrace tailWord_5087153 prefixEnd_5087153 2612154651961840224192115 := by
  unfold tailWord_5087153
  simp only [CollatzResearch.WordTrace]
  refine ⟨185543712939120972407490113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123695808626080648271660075 185543712939120972407490113)
  ·
    refine ⟨139157784704340729305617585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185543712939120972407490113 139157784704340729305617585)
    ·
      refine ⟨104368338528255546979213189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139157784704340729305617585 104368338528255546979213189)
      ·
        refine ⟨19569063474047915058602473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104368338528255546979213189 19569063474047915058602473)
        ·
          refine ⟨14676797605535936293951855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19569063474047915058602473 14676797605535936293951855)
          ·
            refine ⟨22015196408303904440927783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14676797605535936293951855 22015196408303904440927783)
            ·
              refine ⟨33022794612455856661391675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22015196408303904440927783 33022794612455856661391675)
              ·
                refine ⟨49534191918683784992087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33022794612455856661391675 49534191918683784992087513)
                ·
                  refine ⟨37150643939012838744065635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49534191918683784992087513 37150643939012838744065635)
                  ·
                    refine ⟨55725965908519258116098453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37150643939012838744065635 55725965908519258116098453)
                    ·
                      refine ⟨2612154651961840224192115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55725965908519258116098453 2612154651961840224192115)
                      ·
                        rfl

theorem cell23_5087153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5087153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087153 prefixEnd_5087153 := by exact prefixLift 5087153
  have htrace : WordTrace (prefixWord ++ tailWord_5087153) baseStart_5087153 baseEnd_5087153 := by
    simpa [prefixWord, tailWord_5087153, baseEnd_5087153] using wordTrace_append hprefix tailTrace_5087153
  have hstable : (prefixWord ++ tailWord_5087153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087153).length < 2 ^ (prefixWord ++ tailWord_5087153).sum := by decide
  have hdescent : baseEnd_5087153 < baseStart_5087153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087200 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2]
def baseStart_5087200 : Nat := 118140960795 + 5087200 * 2 ^ 59
def prefixEnd_5087200 : Nat := 4983230072969 + 3 ^ 40 * 5087200 * 2
def baseEnd_5087200 : Nat := 2612178785552601540304399

theorem tailTrace_5087200 : CollatzResearch.WordTrace tailWord_5087200 prefixEnd_5087200 2612178785552601540304399 := by
  unfold tailWord_5087200
  simp only [CollatzResearch.WordTrace]
  refine ⟨92772713584975349717225527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123696951446633799622967369 92772713584975349717225527)
  ·
    refine ⟨139159070377463024575838291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92772713584975349717225527 139159070377463024575838291)
    ·
      refine ⟨208738605566194536863757437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139159070377463024575838291 208738605566194536863757437)
      ·
        refine ⟨78276977087322951323909039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208738605566194536863757437 78276977087322951323909039)
        ·
          refine ⟨117415465630984426985863559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78276977087322951323909039 117415465630984426985863559)
          ·
            refine ⟨176123198446476640478795339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117415465630984426985863559 176123198446476640478795339)
            ·
              refine ⟨264184797669714960718193009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176123198446476640478795339 264184797669714960718193009)
              ·
                refine ⟨198138598252286220538644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264184797669714960718193009 198138598252286220538644757)
                ·
                  refine ⟨9287746793075916587748973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198138598252286220538644757 9287746793075916587748973)
                  ·
                    refine ⟨3482905047403468720405865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9287746793075916587748973 3482905047403468720405865)
                    ·
                      refine ⟨2612178785552601540304399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482905047403468720405865 2612178785552601540304399)
                      ·
                        rfl

theorem cell23_5087200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_5087200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087200 prefixEnd_5087200 := by exact prefixLift 5087200
  have htrace : WordTrace (prefixWord ++ tailWord_5087200) baseStart_5087200 baseEnd_5087200 := by
    simpa [prefixWord, tailWord_5087200, baseEnd_5087200] using wordTrace_append hprefix tailTrace_5087200
  have hstable : (prefixWord ++ tailWord_5087200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087200).length < 2 ^ (prefixWord ++ tailWord_5087200).sum := by decide
  have hdescent : baseEnd_5087200 < baseStart_5087200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087210 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_5087210 : Nat := 118140960795 + 5087210 * 2 ^ 59
def prefixEnd_5087210 : Nat := 4983230072969 + 3 ^ 40 * 5087210 * 2
def baseEnd_5087210 : Nat := 870727973453048833726451

theorem tailTrace_5087210 : CollatzResearch.WordTrace tailWord_5087210 prefixEnd_5087210 870727973453048833726451 := by
  unfold tailWord_5087210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46386447974978617785578771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123697194599942980761543389 46386447974978617785578771)
  ·
    refine ⟨69579671962467926678368157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46386447974978617785578771 69579671962467926678368157)
    ·
      refine ⟨26092376985925472504388059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69579671962467926678368157 26092376985925472504388059)
      ·
        refine ⟨39138565478888208756582089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26092376985925472504388059 39138565478888208756582089)
        ·
          refine ⟨29353924109166156567436567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39138565478888208756582089 29353924109166156567436567)
          ·
            refine ⟨44030886163749234851154851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29353924109166156567436567 44030886163749234851154851)
            ·
              refine ⟨66046329245623852276732277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44030886163749234851154851 66046329245623852276732277)
              ·
                refine ⟨6191843366777236150943651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66046329245623852276732277 6191843366777236150943651)
                ·
                  refine ⟨9287765050165854226415477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191843366777236150943651 9287765050165854226415477)
                  ·
                    refine ⟨870727973453048833726451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9287765050165854226415477 870727973453048833726451)
                    ·
                      rfl

theorem cell23_5087210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_5087210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087210 prefixEnd_5087210 := by exact prefixLift 5087210
  have htrace : WordTrace (prefixWord ++ tailWord_5087210) baseStart_5087210 baseEnd_5087210 := by
    simpa [prefixWord, tailWord_5087210, baseEnd_5087210] using wordTrace_append hprefix tailTrace_5087210
  have hstable : (prefixWord ++ tailWord_5087210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087210).length < 2 ^ (prefixWord ++ tailWord_5087210).sum := by decide
  have hdescent : baseEnd_5087210 < baseStart_5087210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087243 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_5087243 : Nat := 118140960795 + 5087243 * 2 ^ 59
def prefixEnd_5087243 : Nat := 4983230072969 + 3 ^ 40 * 5087243 * 2
def baseEnd_5087243 : Nat := 2612200865220744872066701

theorem tailTrace_5087243 : CollatzResearch.WordTrace tailWord_5087243 prefixEnd_5087243 2612200865220744872066701 := by
  unfold tailWord_5087243
  simp only [CollatzResearch.WordTrace]
  refine ⟨185546995508794917778266383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123697997005863278518844255 185546995508794917778266383)
  ·
    refine ⟨278320493263192376667399575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185546995508794917778266383 278320493263192376667399575)
    ·
      refine ⟨417480739894788565001099363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278320493263192376667399575 417480739894788565001099363)
      ·
        refine ⟨626221109842182847501649045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417480739894788565001099363 626221109842182847501649045)
        ·
          refine ⟨29354114523852320976639799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 626221109842182847501649045 29354114523852320976639799)
          ·
            refine ⟨44031171785778481464959699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29354114523852320976639799 44031171785778481464959699)
            ·
              refine ⟨66046757678667722197439549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44031171785778481464959699 66046757678667722197439549)
              ·
                refine ⟨24767534129500395824039831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66046757678667722197439549 24767534129500395824039831)
                ·
                  refine ⟨37151301194250593736059747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24767534129500395824039831 37151301194250593736059747)
                  ·
                    refine ⟨55726951791375890604089621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37151301194250593736059747 55726951791375890604089621)
                    ·
                      refine ⟨2612200865220744872066701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55726951791375890604089621 2612200865220744872066701)
                      ·
                        rfl

theorem cell23_5087243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_5087243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087243 prefixEnd_5087243 := by exact prefixLift 5087243
  have htrace : WordTrace (prefixWord ++ tailWord_5087243) baseStart_5087243 baseEnd_5087243 := by
    simpa [prefixWord, tailWord_5087243, baseEnd_5087243] using wordTrace_append hprefix tailTrace_5087243
  have hstable : (prefixWord ++ tailWord_5087243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087243).length < 2 ^ (prefixWord ++ tailWord_5087243).sum := by decide
  have hdescent : baseEnd_5087243 < baseStart_5087243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087260 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5087260 : Nat := 118140960795 + 5087260 * 2 ^ 59
def prefixEnd_5087260 : Nat := 4983230072969 + 3 ^ 40 * 5087260 * 2
def baseEnd_5087260 : Nat := 2612209594391871305554123

theorem tailTrace_5087260 : CollatzResearch.WordTrace tailWord_5087260 prefixEnd_5087260 2612209594391871305554123 := by
  unfold tailWord_5087260
  simp only [CollatzResearch.WordTrace]
  refine ⟨92773807774866664840817617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123698410366488886454423489 92773807774866664840817617)
  ·
    refine ⟨69580355831149998630613213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92773807774866664840817617 69580355831149998630613213)
    ·
      refine ⟨26092633436681249486479955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69580355831149998630613213 26092633436681249486479955)
      ·
        refine ⟨39138950155021874229719933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26092633436681249486479955 39138950155021874229719933)
        ·
          refine ⟨14677106308133202836144975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39138950155021874229719933 14677106308133202836144975)
          ·
            refine ⟨22015659462199804254217463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14677106308133202836144975 22015659462199804254217463)
            ·
              refine ⟨33023489193299706381326195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22015659462199804254217463 33023489193299706381326195)
              ·
                refine ⟨49535233789949559571989293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33023489193299706381326195 49535233789949559571989293)
                ·
                  refine ⟨18575712671231084839495985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49535233789949559571989293 18575712671231084839495985)
                  ·
                    refine ⟨13931784503423313629621989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18575712671231084839495985 13931784503423313629621989)
                    ·
                      refine ⟨2612209594391871305554123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13931784503423313629621989 2612209594391871305554123)
                      ·
                        rfl

theorem cell23_5087260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5087260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087260 prefixEnd_5087260 := by exact prefixLift 5087260
  have htrace : WordTrace (prefixWord ++ tailWord_5087260) baseStart_5087260 baseEnd_5087260 := by
    simpa [prefixWord, tailWord_5087260, baseEnd_5087260] using wordTrace_append hprefix tailTrace_5087260
  have hstable : (prefixWord ++ tailWord_5087260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087260).length < 2 ^ (prefixWord ++ tailWord_5087260).sum := by decide
  have hdescent : baseEnd_5087260 < baseStart_5087260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087274 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_5087274 : Nat := 118140960795 + 5087274 * 2 ^ 59
def prefixEnd_5087274 : Nat := 4983230072969 + 3 ^ 40 * 5087274 * 2
def baseEnd_5087274 : Nat := 870738927707011416926353

theorem tailTrace_5087274 : CollatzResearch.WordTrace tailWord_5087274 prefixEnd_5087274 870738927707011416926353 := by
  unfold tailWord_5087274
  simp only [CollatzResearch.WordTrace]
  refine ⟨46387031542920652518161219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123698750781121740048429917 46387031542920652518161219)
  ·
    refine ⟨69580547314380978777241829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46387031542920652518161219 69580547314380978777241829)
    ·
      refine ⟨13046352621446433520732843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69580547314380978777241829 13046352621446433520732843)
      ·
        refine ⟨19569528932169650281099265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13046352621446433520732843 19569528932169650281099265)
        ·
          refine ⟨14677146699127237710824449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19569528932169650281099265 14677146699127237710824449)
          ·
            refine ⟨11007860024345428283118337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14677146699127237710824449 11007860024345428283118337)
            ·
              refine ⟨8255895018259071212338753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11007860024345428283118337 8255895018259071212338753)
              ·
                refine ⟨6191921263694303409254065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8255895018259071212338753 6191921263694303409254065)
                ·
                  refine ⟨4643940947770727556940549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6191921263694303409254065 4643940947770727556940549)
                  ·
                    refine ⟨870738927707011416926353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643940947770727556940549 870738927707011416926353)
                    ·
                      rfl

theorem cell23_5087274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_5087274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087274 prefixEnd_5087274 := by exact prefixLift 5087274
  have htrace : WordTrace (prefixWord ++ tailWord_5087274) baseStart_5087274 baseEnd_5087274 := by
    simpa [prefixWord, tailWord_5087274, baseEnd_5087274] using wordTrace_append hprefix tailTrace_5087274
  have hstable : (prefixWord ++ tailWord_5087274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087274).length < 2 ^ (prefixWord ++ tailWord_5087274).sum := by decide
  have hdescent : baseEnd_5087274 < baseStart_5087274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087281 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5087281 : Nat := 118140960795 + 5087281 * 2 ^ 59
def prefixEnd_5087281 : Nat := 4983230072969 + 3 ^ 40 * 5087281 * 2
def baseEnd_5087281 : Nat := 2612220377485615723391527

theorem tailTrace_5087281 : CollatzResearch.WordTrace tailWord_5087281 prefixEnd_5087281 2612220377485615723391527 := by
  unfold tailWord_5087281
  simp only [CollatzResearch.WordTrace]
  refine ⟨185548381482657250268149697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123698920988438166845433131 185548381482657250268149697)
  ·
    refine ⟨139161286111992937701112273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185548381482657250268149697 139161286111992937701112273)
    ·
      refine ⟨104370964583994703275834205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139161286111992937701112273 104370964583994703275834205)
      ·
        refine ⟨39139111718998013728437827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104370964583994703275834205 39139111718998013728437827)
        ·
          refine ⟨58708667578497020592656741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39139111718998013728437827 58708667578497020592656741)
          ·
            refine ⟨11007875170968191361123139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58708667578497020592656741 11007875170968191361123139)
            ·
              refine ⟨16511812756452287041684709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11007875170968191361123139 16511812756452287041684709)
              ·
                refine ⟨3095964891834803820315883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16511812756452287041684709 3095964891834803820315883)
                ·
                  refine ⟨4643947337752205730473825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095964891834803820315883 4643947337752205730473825)
                  ·
                    refine ⟨3482960503314154297855369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643947337752205730473825 3482960503314154297855369)
                    ·
                      refine ⟨2612220377485615723391527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3482960503314154297855369 2612220377485615723391527)
                      ·
                        rfl

theorem cell23_5087281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5087281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087281 prefixEnd_5087281 := by exact prefixLift 5087281
  have htrace : WordTrace (prefixWord ++ tailWord_5087281) baseStart_5087281 baseEnd_5087281 := by
    simpa [prefixWord, tailWord_5087281, baseEnd_5087281] using wordTrace_append hprefix tailTrace_5087281
  have hstable : (prefixWord ++ tailWord_5087281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087281).length < 2 ^ (prefixWord ++ tailWord_5087281).sum := by decide
  have hdescent : baseEnd_5087281 < baseStart_5087281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087283 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 7]
def baseStart_5087283 : Nat := 118140960795 + 5087283 * 2 ^ 59
def prefixEnd_5087283 : Nat := 4983230072969 + 3 ^ 40 * 5087283 * 2
def baseEnd_5087283 : Nat := 870740468148974905188839

theorem tailTrace_5087283 : CollatzResearch.WordTrace tailWord_5087283 prefixEnd_5087283 870740468148974905188839 := by
  unfold tailWord_5087283
  simp only [CollatzResearch.WordTrace]
  refine ⟨185548454428650004609722503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123698969619100003073148335 185548454428650004609722503)
  ·
    refine ⟨278322681642975006914583755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185548454428650004609722503 278322681642975006914583755)
    ·
      refine ⟨417484022464462510371875633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278322681642975006914583755 417484022464462510371875633)
      ·
        refine ⟨313113016848346882778906725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417484022464462510371875633 313113016848346882778906725)
        ·
          refine ⟨58708690659065040521045011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313113016848346882778906725 58708690659065040521045011)
          ·
            refine ⟨88063035988597560781567517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58708690659065040521045011 88063035988597560781567517)
            ·
              refine ⟨33023638495724085293087819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88063035988597560781567517 33023638495724085293087819)
              ·
                refine ⟨49535457743586127939631729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33023638495724085293087819 49535457743586127939631729)
                ·
                  refine ⟨37151593307689595954723797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49535457743586127939631729 37151593307689595954723797)
                  ·
                    refine ⟨870740468148974905188839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37151593307689595954723797 870740468148974905188839)
                    ·
                      rfl

theorem cell23_5087283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_5087283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087283 prefixEnd_5087283 := by exact prefixLift 5087283
  have htrace : WordTrace (prefixWord ++ tailWord_5087283) baseStart_5087283 baseEnd_5087283 := by
    simpa [prefixWord, tailWord_5087283, baseEnd_5087283] using wordTrace_append hprefix tailTrace_5087283
  have hstable : (prefixWord ++ tailWord_5087283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087283).length < 2 ^ (prefixWord ++ tailWord_5087283).sum := by decide
  have hdescent : baseEnd_5087283 < baseStart_5087283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087294 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5087294 : Nat := 118140960795 + 5087294 * 2 ^ 59
def prefixEnd_5087294 : Nat := 4983230072969 + 3 ^ 40 * 5087294 * 2
def baseEnd_5087294 : Nat := 2612227052734124172528967

theorem tailTrace_5087294 : CollatzResearch.WordTrace tailWord_5087294 prefixEnd_5087294 2612227052734124172528967 := by
  unfold tailWord_5087294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23193606953951269186046617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123699237087740102325581957 23193606953951269186046617)
  ·
    refine ⟨17395205215463451889534963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23193606953951269186046617 17395205215463451889534963)
    ·
      refine ⟨26092807823195177834302445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395205215463451889534963 26092807823195177834302445)
      ·
        refine ⟨9784802933698191687863417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26092807823195177834302445 9784802933698191687863417)
        ·
          refine ⟨7338602200273643765897563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9784802933698191687863417 7338602200273643765897563)
          ·
            refine ⟨11007903300410465648846345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7338602200273643765897563 11007903300410465648846345)
            ·
              refine ⟨8255927475307849236634759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11007903300410465648846345 8255927475307849236634759)
              ·
                refine ⟨12383891212961773854952139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255927475307849236634759 12383891212961773854952139)
                ·
                  refine ⟨18575836819442660782428209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383891212961773854952139 18575836819442660782428209)
                  ·
                    refine ⟨13931877614581995586821157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18575836819442660782428209 13931877614581995586821157)
                    ·
                      refine ⟨2612227052734124172528967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13931877614581995586821157 2612227052734124172528967)
                      ·
                        rfl

theorem cell23_5087294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5087294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087294 prefixEnd_5087294 := by exact prefixLift 5087294
  have htrace : WordTrace (prefixWord ++ tailWord_5087294) baseStart_5087294 baseEnd_5087294 := by
    simpa [prefixWord, tailWord_5087294, baseEnd_5087294] using wordTrace_append hprefix tailTrace_5087294
  have hstable : (prefixWord ++ tailWord_5087294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087294).length < 2 ^ (prefixWord ++ tailWord_5087294).sum := by decide
  have hdescent : baseEnd_5087294 < baseStart_5087294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087297 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5087297 : Nat := 118140960795 + 5087297 * 2 ^ 59
def prefixEnd_5087297 : Nat := 4983230072969 + 3 ^ 40 * 5087297 * 2
def baseEnd_5087297 : Nat := 2612228593176087660791453

theorem tailTrace_5087297 : CollatzResearch.WordTrace tailWord_5087297 prefixEnd_5087297 2612228593176087660791453 := by
  unfold tailWord_5087297
  simp only [CollatzResearch.WordTrace]
  refine ⟨185548965050599285000732145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123699310033732856667154763 185548965050599285000732145)
  ·
    refine ⟨139161723787949463750549109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185548965050599285000732145 139161723787949463750549109)
    ·
      refine ⟨13046411605120262226613979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139161723787949463750549109 13046411605120262226613979)
      ·
        refine ⟨19569617407680393339920969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13046411605120262226613979 19569617407680393339920969)
        ·
          refine ⟨14677213055760295004940727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19569617407680393339920969 14677213055760295004940727)
          ·
            refine ⟨22015819583640442507411091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14677213055760295004940727 22015819583640442507411091)
            ·
              refine ⟨33023729375460663761116637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22015819583640442507411091 33023729375460663761116637)
              ·
                refine ⟨12383898515797748910418739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33023729375460663761116637 12383898515797748910418739)
                ·
                  refine ⟨18575847773696623365628109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383898515797748910418739 18575847773696623365628109)
                  ·
                    refine ⟨6965942915136233762110541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18575847773696623365628109 6965942915136233762110541)
                    ·
                      refine ⟨2612228593176087660791453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965942915136233762110541 2612228593176087660791453)
                      ·
                        rfl

theorem cell23_5087297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5087297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087297 prefixEnd_5087297 := by exact prefixLift 5087297
  have htrace : WordTrace (prefixWord ++ tailWord_5087297) baseStart_5087297 baseEnd_5087297 := by
    simpa [prefixWord, tailWord_5087297, baseEnd_5087297] using wordTrace_append hprefix tailTrace_5087297
  have hstable : (prefixWord ++ tailWord_5087297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087297).length < 2 ^ (prefixWord ++ tailWord_5087297).sum := by decide
  have hdescent : baseEnd_5087297 < baseStart_5087297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087313 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_5087313 : Nat := 118140960795 + 5087313 * 2 ^ 59
def prefixEnd_5087313 : Nat := 4983230072969 + 3 ^ 40 * 5087313 * 2
def baseEnd_5087313 : Nat := 870745602955519866063793

theorem tailTrace_5087313 : CollatzResearch.WordTrace tailWord_5087313 prefixEnd_5087313 870745602955519866063793 := by
  unfold tailWord_5087313
  simp only [CollatzResearch.WordTrace]
  refine ⟨185549548618541319733314593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123699699079027546488876395 185549548618541319733314593)
  ·
    refine ⟨139162161463905989799985945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185549548618541319733314593 139162161463905989799985945)
    ·
      refine ⟨104371621097929492349989459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139162161463905989799985945 104371621097929492349989459)
      ·
        refine ⟨156557431646894238524984189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104371621097929492349989459 156557431646894238524984189)
        ·
          refine ⟨58709036867585339446869071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156557431646894238524984189 58709036867585339446869071)
          ·
            refine ⟨88063555301378009170303607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58709036867585339446869071 88063555301378009170303607)
            ·
              refine ⟨132095332952067013755455411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88063555301378009170303607 132095332952067013755455411)
              ·
                refine ⟨198142999428100520633183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132095332952067013755455411 198142999428100520633183117)
                ·
                  refine ⟨74303624785537695237443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198142999428100520633183117 74303624785537695237443669)
                  ·
                    refine ⟨870745602955519866063793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74303624785537695237443669 870745602955519866063793)
                    ·
                      rfl

theorem cell23_5087313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_5087313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087313 prefixEnd_5087313 := by exact prefixLift 5087313
  have htrace : WordTrace (prefixWord ++ tailWord_5087313) baseStart_5087313 baseEnd_5087313 := by
    simpa [prefixWord, tailWord_5087313, baseEnd_5087313] using wordTrace_append hprefix tailTrace_5087313
  have hstable : (prefixWord ++ tailWord_5087313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087313).length < 2 ^ (prefixWord ++ tailWord_5087313).sum := by decide
  have hdescent : baseEnd_5087313 < baseStart_5087313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087318 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5087318 : Nat := 118140960795 + 5087318 * 2 ^ 59
def prefixEnd_5087318 : Nat := 4983230072969 + 3 ^ 40 * 5087318 * 2
def baseEnd_5087318 : Nat := 2612239376269832078628857

theorem tailTrace_5087318 : CollatzResearch.WordTrace tailWord_5087318 prefixEnd_5087318 2612239376269832078628857 := by
  unfold tailWord_5087318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11596858186470200349202913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123699820655682137058164405 11596858186470200349202913)
  ·
    refine ⟨8697643639852650261902185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11596858186470200349202913 8697643639852650261902185)
    ·
      refine ⟨6523232729889487696426639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8697643639852650261902185 6523232729889487696426639)
      ·
        refine ⟨9784849094834231544639959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6523232729889487696426639 9784849094834231544639959)
        ·
          refine ⟨14677273642251347316959939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784849094834231544639959 14677273642251347316959939)
          ·
            refine ⟨22015910463377020975439909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14677273642251347316959939 22015910463377020975439909)
            ·
              refine ⟨4127983211883191432894983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22015910463377020975439909 4127983211883191432894983)
              ·
                refine ⟨6191974817824787149342475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127983211883191432894983 6191974817824787149342475)
                ·
                  refine ⟨9287962226737180724013713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191974817824787149342475 9287962226737180724013713)
                  ·
                    refine ⟨6965971670052885543010285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9287962226737180724013713 6965971670052885543010285)
                    ·
                      refine ⟨2612239376269832078628857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6965971670052885543010285 2612239376269832078628857)
                      ·
                        rfl

theorem cell23_5087318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5087318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087318 prefixEnd_5087318 := by exact prefixLift 5087318
  have htrace : WordTrace (prefixWord ++ tailWord_5087318) baseStart_5087318 baseEnd_5087318 := by
    simpa [prefixWord, tailWord_5087318, baseEnd_5087318] using wordTrace_append hprefix tailTrace_5087318
  have hstable : (prefixWord ++ tailWord_5087318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087318).length < 2 ^ (prefixWord ++ tailWord_5087318).sum := by decide
  have hdescent : baseEnd_5087318 < baseStart_5087318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087394 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_5087394 : Nat := 118140960795 + 5087394 * 2 ^ 59
def prefixEnd_5087394 : Nat := 4983230072969 + 3 ^ 40 * 5087394 * 2
def baseEnd_5087394 : Nat := 290253155644397086808723

theorem tailTrace_5087394 : CollatzResearch.WordTrace tailWord_5087394 prefixEnd_5087394 290253155644397086808723 := by
  unfold tailWord_5087394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46388125732811967641753309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123701668620831913711342157 46388125732811967641753309)
  ·
    refine ⟨17395547149804487865657491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46388125732811967641753309 17395547149804487865657491)
    ·
      refine ⟨26093320724706731798486237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395547149804487865657491 26093320724706731798486237)
      ·
        refine ⟨9784995271765024424432339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26093320724706731798486237 9784995271765024424432339)
        ·
          refine ⟨14677492907647536636648509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784995271765024424432339 14677492907647536636648509)
          ·
            refine ⟨5504059840367826238743191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14677492907647536636648509 5504059840367826238743191)
            ·
              refine ⟨8256089760551739358114787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504059840367826238743191 8256089760551739358114787)
              ·
                refine ⟨12384134640827609037172181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256089760551739358114787 12384134640827609037172181)
                ·
                  refine ⟨290253155644397086808723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12384134640827609037172181 290253155644397086808723)
                  ·
                    rfl

theorem cell23_5087394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_5087394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087394 prefixEnd_5087394 := by exact prefixLift 5087394
  have htrace : WordTrace (prefixWord ++ tailWord_5087394) baseStart_5087394 baseEnd_5087394 := by
    simpa [prefixWord, tailWord_5087394, baseEnd_5087394] using wordTrace_append hprefix tailTrace_5087394
  have hstable : (prefixWord ++ tailWord_5087394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087394).length < 2 ^ (prefixWord ++ tailWord_5087394).sum := by decide
  have hdescent : baseEnd_5087394 < baseStart_5087394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087397 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_5087397 : Nat := 118140960795 + 5087397 * 2 ^ 59
def prefixEnd_5087397 : Nat := 4983230072969 + 3 ^ 40 * 5087397 * 2
def baseEnd_5087397 : Nat := 2612279941241537269540993

theorem tailTrace_5087397 : CollatzResearch.WordTrace tailWord_5087397 prefixEnd_5087397 2612279941241537269540993 := by
  unfold tailWord_5087397
  simp only [CollatzResearch.WordTrace]
  refine ⟨185552612350237002079372445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123701741566824668052914963 185552612350237002079372445)
  ·
    refine ⟨69582229631338875779764667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185552612350237002079372445 69582229631338875779764667)
    ·
      refine ⟨104373344447008313669647001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69582229631338875779764667 104373344447008313669647001)
      ·
        refine ⟨78280008335256235252235251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104373344447008313669647001 78280008335256235252235251)
        ·
          refine ⟨117420012502884352878352877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78280008335256235252235251 117420012502884352878352877)
          ·
            refine ⟨44032504688581632329382329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117420012502884352878352877 44032504688581632329382329)
            ·
              refine ⟨33024378516436224247036747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44032504688581632329382329 33024378516436224247036747)
              ·
                refine ⟨49536567774654336370555121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33024378516436224247036747 49536567774654336370555121)
                ·
                  refine ⟨37152425830990752277916341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49536567774654336370555121 37152425830990752277916341)
                  ·
                    refine ⟨3483039921655383026054657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37152425830990752277916341 3483039921655383026054657)
                    ·
                      refine ⟨2612279941241537269540993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483039921655383026054657 2612279941241537269540993)
                      ·
                        rfl

theorem cell23_5087397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_5087397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087397 prefixEnd_5087397 := by exact prefixLift 5087397
  have htrace : WordTrace (prefixWord ++ tailWord_5087397) baseStart_5087397 baseEnd_5087397 := by
    simpa [prefixWord, tailWord_5087397, baseEnd_5087397] using wordTrace_append hprefix tailTrace_5087397
  have hstable : (prefixWord ++ tailWord_5087397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087397).length < 2 ^ (prefixWord ++ tailWord_5087397).sum := by decide
  have hdescent : baseEnd_5087397 < baseStart_5087397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087405 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5087405 : Nat := 118140960795 + 5087405 * 2 ^ 59
def prefixEnd_5087405 : Nat := 4983230072969 + 3 ^ 40 * 5087405 * 2
def baseEnd_5087405 : Nat := 2612284049086773238240957

theorem tailTrace_5087405 : CollatzResearch.WordTrace tailWord_5087405 prefixEnd_5087405 2612284049086773238240957 := by
  unfold tailWord_5087405
  simp only [CollatzResearch.WordTrace]
  refine ⟨185552904134208019445663669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123701936089472012963775779 185552904134208019445663669)
  ·
    refine ⟨17395584762582001823030969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185552904134208019445663669 17395584762582001823030969)
    ·
      refine ⟨13046688571936501367273227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17395584762582001823030969 13046688571936501367273227)
      ·
        refine ⟨19570032857904752050909841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13046688571936501367273227 19570032857904752050909841)
        ·
          refine ⟨14677524643428564038182381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19570032857904752050909841 14677524643428564038182381)
          ·
            refine ⟨5504071741285711514318393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14677524643428564038182381 5504071741285711514318393)
            ·
              refine ⟨4128053805964283635738795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504071741285711514318393 4128053805964283635738795)
              ·
                refine ⟨6192080708946425453608193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128053805964283635738795 6192080708946425453608193)
                ·
                  refine ⟨4644060531709819090206145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192080708946425453608193 4644060531709819090206145)
                  ·
                    refine ⟨3483045398782364317654609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644060531709819090206145 3483045398782364317654609)
                    ·
                      refine ⟨2612284049086773238240957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483045398782364317654609 2612284049086773238240957)
                      ·
                        rfl

theorem cell23_5087405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5087405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087405 prefixEnd_5087405 := by exact prefixLift 5087405
  have htrace : WordTrace (prefixWord ++ tailWord_5087405) baseStart_5087405 baseEnd_5087405 := by
    simpa [prefixWord, tailWord_5087405, baseEnd_5087405] using wordTrace_append hprefix tailTrace_5087405
  have hstable : (prefixWord ++ tailWord_5087405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087405).length < 2 ^ (prefixWord ++ tailWord_5087405).sum := by decide
  have hdescent : baseEnd_5087405 < baseStart_5087405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087450 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_5087450 : Nat := 118140960795 + 5087450 * 2 ^ 59
def prefixEnd_5087450 : Nat := 4983230072969 + 3 ^ 40 * 5087450 * 2
def baseEnd_5087450 : Nat := 290256350635136173575361

theorem tailTrace_5087450 : CollatzResearch.WordTrace tailWord_5087450 prefixEnd_5087450 290256350635136173575361 := by
  unfold tailWord_5087450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46388636354761248032762951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123703030279363328087367869 46388636354761248032762951)
  ·
    refine ⟨69582954532141872049144427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46388636354761248032762951 69582954532141872049144427)
    ·
      refine ⟨104374431798212808073716641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69582954532141872049144427 104374431798212808073716641)
      ·
        refine ⟨78280823848659606055287481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104374431798212808073716641 78280823848659606055287481)
        ·
          refine ⟨58710617886494704541465611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78280823848659606055287481 58710617886494704541465611)
          ·
            refine ⟨88065926829742056812198417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58710617886494704541465611 88065926829742056812198417)
            ·
              refine ⟨66049445122306542609148813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88065926829742056812198417 66049445122306542609148813)
              ·
                refine ⟨24768541920864953478430805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66049445122306542609148813 24768541920864953478430805)
                ·
                  refine ⟨290256350635136173575361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24768541920864953478430805 290256350635136173575361)
                  ·
                    rfl

theorem cell23_5087450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_5087450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087450 prefixEnd_5087450 := by exact prefixLift 5087450
  have htrace : WordTrace (prefixWord ++ tailWord_5087450) baseStart_5087450 baseEnd_5087450 := by
    simpa [prefixWord, tailWord_5087450, baseEnd_5087450] using wordTrace_append hprefix tailTrace_5087450
  have hstable : (prefixWord ++ tailWord_5087450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087450).length < 2 ^ (prefixWord ++ tailWord_5087450).sum := by decide
  have hdescent : baseEnd_5087450 < baseStart_5087450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087511 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5087511 : Nat := 118140960795 + 5087511 * 2 ^ 59
def prefixEnd_5087511 : Nat := 4983230072969 + 3 ^ 40 * 5087511 * 2
def baseEnd_5087511 : Nat := 2612338478036149823515469

theorem tailTrace_5087511 : CollatzResearch.WordTrace tailWord_5087511 prefixEnd_5087511 2612338478036149823515469 := by
  unfold tailWord_5087511
  simp only [CollatzResearch.WordTrace]
  refine ⟨185556770271823999549022387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123704513514549333032681591 185556770271823999549022387)
  ·
    refine ⟨278335155407735999323533581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185556770271823999549022387 278335155407735999323533581)
    ·
      refine ⟨104375683277900999746325093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278335155407735999323533581 104375683277900999746325093)
      ·
        refine ⟨19570440614606437452435955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104375683277900999746325093 19570440614606437452435955)
        ·
          refine ⟨29355660921909656178653933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19570440614606437452435955 29355660921909656178653933)
          ·
            refine ⟨11008372845716121066995225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29355660921909656178653933 11008372845716121066995225)
            ·
              refine ⟨8256279634287090800246419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11008372845716121066995225 8256279634287090800246419)
              ·
                refine ⟨12384419451430636200369629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256279634287090800246419 12384419451430636200369629)
                ·
                  refine ⟨4644157294286488575138611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12384419451430636200369629 4644157294286488575138611)
                  ·
                    refine ⟨6966235941429732862707917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644157294286488575138611 6966235941429732862707917)
                    ·
                      refine ⟨2612338478036149823515469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966235941429732862707917 2612338478036149823515469)
                      ·
                        rfl

theorem cell23_5087511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5087511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087511 prefixEnd_5087511 := by exact prefixLift 5087511
  have htrace : WordTrace (prefixWord ++ tailWord_5087511) baseStart_5087511 baseEnd_5087511 := by
    simpa [prefixWord, tailWord_5087511, baseEnd_5087511] using wordTrace_append hprefix tailTrace_5087511
  have hstable : (prefixWord ++ tailWord_5087511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087511).length < 2 ^ (prefixWord ++ tailWord_5087511).sum := by decide
  have hdescent : baseEnd_5087511 < baseStart_5087511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087518 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_5087518 : Nat := 118140960795 + 5087518 * 2 ^ 59
def prefixEnd_5087518 : Nat := 4983230072969 + 3 ^ 40 * 5087518 * 2
def baseEnd_5087518 : Nat := 290260230266747921791993

theorem tailTrace_5087518 : CollatzResearch.WordTrace tailWord_5087518 prefixEnd_5087518 290260230266747921791993 := by
  unfold tailWord_5087518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23194628197849829968065901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123704683721865759829684805 23194628197849829968065901)
  ·
    refine ⟨8697985574193686238024713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23194628197849829968065901 8697985574193686238024713)
    ·
      refine ⟨6523489180645264678518535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8697985574193686238024713 6523489180645264678518535)
      ·
        refine ⟨9785233770967897017777803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6523489180645264678518535 9785233770967897017777803)
        ·
          refine ⟨14677850656451845526666705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9785233770967897017777803 14677850656451845526666705)
          ·
            refine ⟨11008387992338884145000029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14677850656451845526666705 11008387992338884145000029)
            ·
              refine ⟨4128145497127081554375011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11008387992338884145000029 4128145497127081554375011)
              ·
                refine ⟨6192218245690622331562517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128145497127081554375011 6192218245690622331562517)
                ·
                  refine ⟨290260230266747921791993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6192218245690622331562517 290260230266747921791993)
                  ·
                    rfl

theorem cell23_5087518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_5087518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087518 prefixEnd_5087518 := by exact prefixLift 5087518
  have htrace : WordTrace (prefixWord ++ tailWord_5087518) baseStart_5087518 baseEnd_5087518 := by
    simpa [prefixWord, tailWord_5087518, baseEnd_5087518] using wordTrace_append hprefix tailTrace_5087518
  have hstable : (prefixWord ++ tailWord_5087518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087518).length < 2 ^ (prefixWord ++ tailWord_5087518).sum := by decide
  have hdescent : baseEnd_5087518 < baseStart_5087518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087545 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5087545 : Nat := 118140960795 + 5087545 * 2 ^ 59
def prefixEnd_5087545 : Nat := 4983230072969 + 3 ^ 40 * 5087545 * 2
def baseEnd_5087545 : Nat := 2612355936378402690490313

theorem tailTrace_5087545 : CollatzResearch.WordTrace tailWord_5087545 prefixEnd_5087545 2612355936378402690490313 := by
  unfold tailWord_5087545
  simp only [CollatzResearch.WordTrace]
  refine ⟨185558010353700823355760089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123705340235800548903840059 185558010353700823355760089)
  ·
    refine ⟨139168507765275617516820067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185558010353700823355760089 139168507765275617516820067)
    ·
      refine ⟨208752761647913426275230101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139168507765275617516820067 208752761647913426275230101)
      ·
        refine ⟨9785285702245941856651411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208752761647913426275230101 9785285702245941856651411)
        ·
          refine ⟨14677928553368912784977117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9785285702245941856651411 14677928553368912784977117)
          ·
            refine ⟨5504223207513342294366419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14677928553368912784977117 5504223207513342294366419)
            ·
              refine ⟨8256334811270013441549629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504223207513342294366419 8256334811270013441549629)
              ·
                refine ⟨3096125554226255040581111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8256334811270013441549629 3096125554226255040581111)
                ·
                  refine ⟨4644188331339382560871667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096125554226255040581111 4644188331339382560871667)
                  ·
                    refine ⟨6966282497009073841307501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644188331339382560871667 6966282497009073841307501)
                    ·
                      refine ⟨2612355936378402690490313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966282497009073841307501 2612355936378402690490313)
                      ·
                        rfl

theorem cell23_5087545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5087545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087545 prefixEnd_5087545 := by exact prefixLift 5087545
  have htrace : WordTrace (prefixWord ++ tailWord_5087545) baseStart_5087545 baseEnd_5087545 := by
    simpa [prefixWord, tailWord_5087545, baseEnd_5087545] using wordTrace_append hprefix tailTrace_5087545
  have hstable : (prefixWord ++ tailWord_5087545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087545).length < 2 ^ (prefixWord ++ tailWord_5087545).sum := by decide
  have hdescent : baseEnd_5087545 < baseStart_5087545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_5087567 : Nat := 118140960795 + 5087567 * 2 ^ 59
def prefixEnd_5087567 : Nat := 4983230072969 + 3 ^ 40 * 5087567 * 2
def baseEnd_5087567 : Nat := 2612367232952801604415211

theorem tailTrace_5087567 : CollatzResearch.WordTrace tailWord_5087567 prefixEnd_5087567 2612367232952801604415211 := by
  unfold tailWord_5087567
  simp only [CollatzResearch.WordTrace]
  refine ⟨185558812759621121113060955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123705875173080747408707303 185558812759621121113060955)
  ·
    refine ⟨278338219139431681669591433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185558812759621121113060955 278338219139431681669591433)
    ·
      refine ⟨208753664354573761252193575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278338219139431681669591433 208753664354573761252193575)
      ·
        refine ⟨313130496531860641878290363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208753664354573761252193575 313130496531860641878290363)
        ·
          refine ⟨469695744797790962817435545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313130496531860641878290363 469695744797790962817435545)
          ·
            refine ⟨352271808598343222113076659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469695744797790962817435545 352271808598343222113076659)
            ·
              refine ⟨528407712897514833169614989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352271808598343222113076659 528407712897514833169614989)
              ·
                refine ⟨198152892336568062438605621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528407712897514833169614989 198152892336568062438605621)
                ·
                  refine ⟨18576833656553255853619277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198152892336568062438605621 18576833656553255853619277)
                  ·
                    refine ⟨6966312621207470945107229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18576833656553255853619277 6966312621207470945107229)
                    ·
                      refine ⟨2612367232952801604415211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966312621207470945107229 2612367232952801604415211)
                      ·
                        rfl

theorem cell23_5087567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_5087567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087567 prefixEnd_5087567 := by exact prefixLift 5087567
  have htrace : WordTrace (prefixWord ++ tailWord_5087567) baseStart_5087567 baseEnd_5087567 := by
    simpa [prefixWord, tailWord_5087567, baseEnd_5087567] using wordTrace_append hprefix tailTrace_5087567
  have hstable : (prefixWord ++ tailWord_5087567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087567).length < 2 ^ (prefixWord ++ tailWord_5087567).sum := by decide
  have hdescent : baseEnd_5087567 < baseStart_5087567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087568 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2]
def baseStart_5087568 : Nat := 118140960795 + 5087568 * 2 ^ 59
def prefixEnd_5087568 : Nat := 4983230072969 + 3 ^ 40 * 5087568 * 2
def baseEnd_5087568 : Nat := 2612367746433456100502707

theorem tailTrace_5087568 : CollatzResearch.WordTrace tailWord_5087568 prefixEnd_5087568 2612367746433456100502707 := by
  unfold tailWord_5087568
  simp only [CollatzResearch.WordTrace]
  refine ⟨92779424616308749141923679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123705899488411665522564905 92779424616308749141923679)
  ·
    refine ⟨139169136924463123712885519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92779424616308749141923679 139169136924463123712885519)
    ·
      refine ⟨208753705386694685569328279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139169136924463123712885519 208753705386694685569328279)
      ·
        refine ⟨313130558080042028353992419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208753705386694685569328279 313130558080042028353992419)
        ·
          refine ⟨469695837120063042530988629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313130558080042028353992419 469695837120063042530988629)
          ·
            refine ⟨5504248091250738779660023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 469695837120063042530988629 5504248091250738779660023)
            ·
              refine ⟨8256372136876108169490035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504248091250738779660023 8256372136876108169490035)
              ·
                refine ⟨12384558205314162254235053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256372136876108169490035 12384558205314162254235053)
                ·
                  refine ⟨4644209326992810845338145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12384558205314162254235053 4644209326992810845338145)
                  ·
                    refine ⟨3483156995244608134003609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644209326992810845338145 3483156995244608134003609)
                    ·
                      refine ⟨2612367746433456100502707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483156995244608134003609 2612367746433456100502707)
                      ·
                        rfl

theorem cell23_5087568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2].length) (baseStart_5087568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087568 prefixEnd_5087568 := by exact prefixLift 5087568
  have htrace : WordTrace (prefixWord ++ tailWord_5087568) baseStart_5087568 baseEnd_5087568 := by
    simpa [prefixWord, tailWord_5087568, baseEnd_5087568] using wordTrace_append hprefix tailTrace_5087568
  have hstable : (prefixWord ++ tailWord_5087568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087568).length < 2 ^ (prefixWord ++ tailWord_5087568).sum := by decide
  have hdescent : baseEnd_5087568 < baseStart_5087568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087619 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 1, 2, 2]
def baseStart_5087619 : Nat := 118140960795 + 5087619 * 2 ^ 59
def prefixEnd_5087619 : Nat := 4983230072969 + 3 ^ 40 * 5087619 * 2
def baseEnd_5087619 : Nat := 2612393933946835400964973

theorem tailTrace_5087619 : CollatzResearch.WordTrace tailWord_5087619 prefixEnd_5087619 2612393933946835400964973 := by
  unfold tailWord_5087619
  simp only [CollatzResearch.WordTrace]
  refine ⟨185560709355432733993953911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123707139570288489329302607 185560709355432733993953911)
  ·
    refine ⟨278341064033149100990930867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185560709355432733993953911 278341064033149100990930867)
    ·
      refine ⟨417511596049723651486396301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278341064033149100990930867 417511596049723651486396301)
      ·
        refine ⟨156566848518646369307398613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417511596049723651486396301 156566848518646369307398613)
        ·
          refine ⟨3669535512155774280642155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156566848518646369307398613 3669535512155774280642155)
          ·
            refine ⟨5504303268233661420963233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669535512155774280642155 5504303268233661420963233)
            ·
              refine ⟨4128227451175246065722425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504303268233661420963233 4128227451175246065722425)
              ·
                refine ⟨3096170588381434549291819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128227451175246065722425 3096170588381434549291819)
                ·
                  refine ⟨4644255882572151823937729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096170588381434549291819 4644255882572151823937729)
                  ·
                    refine ⟨3483191911929113867953297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644255882572151823937729 3483191911929113867953297)
                    ·
                      refine ⟨2612393933946835400964973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483191911929113867953297 2612393933946835400964973)
                      ·
                        rfl

theorem cell23_5087619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_5087619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087619 prefixEnd_5087619 := by exact prefixLift 5087619
  have htrace : WordTrace (prefixWord ++ tailWord_5087619) baseStart_5087619 baseEnd_5087619 := by
    simpa [prefixWord, tailWord_5087619, baseEnd_5087619] using wordTrace_append hprefix tailTrace_5087619
  have hstable : (prefixWord ++ tailWord_5087619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087619).length < 2 ^ (prefixWord ++ tailWord_5087619).sum := by decide
  have hdescent : baseEnd_5087619 < baseStart_5087619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087641 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 4, 2]
def baseStart_5087641 : Nat := 118140960795 + 5087641 * 2 ^ 59
def prefixEnd_5087641 : Nat := 4983230072969 + 3 ^ 40 * 5087641 * 2
def baseEnd_5087641 : Nat := 2612405230521234314889871

theorem tailTrace_5087641 : CollatzResearch.WordTrace tailWord_5087641 prefixEnd_5087641 2612405230521234314889871 := by
  unfold tailWord_5087641
  simp only [CollatzResearch.WordTrace]
  refine ⟨185561511761353031751254777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123707674507568687834169851 185561511761353031751254777)
  ·
    refine ⟨139171133821014773813441083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185561511761353031751254777 139171133821014773813441083)
    ·
      refine ⟨208756700731522160720161625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139171133821014773813441083 208756700731522160720161625)
      ·
        refine ⟨156567525548641620540121219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208756700731522160720161625 156567525548641620540121219)
        ·
          refine ⟨234851288322962430810181829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156567525548641620540121219 234851288322962430810181829)
          ·
            refine ⟨44034616560555455776909093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234851288322962430810181829 44034616560555455776909093)
            ·
              refine ⟨8256490605104147958170455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44034616560555455776909093 8256490605104147958170455)
              ·
                refine ⟨12384735907656221937255683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256490605104147958170455 12384735907656221937255683)
                ·
                  refine ⟨18577103861484332905883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12384735907656221937255683 18577103861484332905883525)
                  ·
                    refine ⟨3483206974028312419853161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18577103861484332905883525 3483206974028312419853161)
                    ·
                      refine ⟨2612405230521234314889871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483206974028312419853161 2612405230521234314889871)
                      ·
                        rfl

theorem cell23_5087641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_5087641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087641 prefixEnd_5087641 := by exact prefixLift 5087641
  have htrace : WordTrace (prefixWord ++ tailWord_5087641) baseStart_5087641 baseEnd_5087641 := by
    simpa [prefixWord, tailWord_5087641, baseEnd_5087641] using wordTrace_append hprefix tailTrace_5087641
  have hstable : (prefixWord ++ tailWord_5087641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087641).length < 2 ^ (prefixWord ++ tailWord_5087641).sum := by decide
  have hdescent : baseEnd_5087641 < baseStart_5087641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087692 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5087692 : Nat := 118140960795 + 5087692 * 2 ^ 59
def prefixEnd_5087692 : Nat := 4983230072969 + 3 ^ 40 * 5087692 * 2
def baseEnd_5087692 : Nat := 2612431418034613615352137

theorem tailTrace_5087692 : CollatzResearch.WordTrace tailWord_5087692 prefixEnd_5087692 2612431418034613615352137 := by
  unfold tailWord_5087692
  simp only [CollatzResearch.WordTrace]
  refine ⟨92781685942084133730680665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123708914589445511640907553 92781685942084133730680665)
  ·
    refine ⟨69586264456563100298010499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92781685942084133730680665 69586264456563100298010499)
    ·
      refine ⟨104379396684844650447015749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69586264456563100298010499 104379396684844650447015749)
      ·
        refine ⟨19571136878408371958815453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104379396684844650447015749 19571136878408371958815453)
        ·
          refine ⟨7339176329403139484555795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19571136878408371958815453 7339176329403139484555795)
          ·
            refine ⟨11008764494104709226833693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7339176329403139484555795 11008764494104709226833693)
            ·
              refine ⟨4128286685289265960062635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11008764494104709226833693 4128286685289265960062635)
              ·
                refine ⟨6192430027933898940093953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128286685289265960062635 6192430027933898940093953)
                ·
                  refine ⟨4644322520950424205070465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192430027933898940093953 4644322520950424205070465)
                  ·
                    refine ⟨3483241890712818153802849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644322520950424205070465 3483241890712818153802849)
                    ·
                      refine ⟨2612431418034613615352137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483241890712818153802849 2612431418034613615352137)
                      ·
                        rfl

theorem cell23_5087692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5087692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087692 prefixEnd_5087692 := by exact prefixLift 5087692
  have htrace : WordTrace (prefixWord ++ tailWord_5087692) baseStart_5087692 baseEnd_5087692 := by
    simpa [prefixWord, tailWord_5087692, baseEnd_5087692] using wordTrace_append hprefix tailTrace_5087692
  have hstable : (prefixWord ++ tailWord_5087692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087692).length < 2 ^ (prefixWord ++ tailWord_5087692).sum := by decide
  have hdescent : baseEnd_5087692 < baseStart_5087692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087715 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 5]
def baseStart_5087715 : Nat := 118140960795 + 5087715 * 2 ^ 59
def prefixEnd_5087715 : Nat := 4983230072969 + 3 ^ 40 * 5087715 * 2
def baseEnd_5087715 : Nat := 290271469787740780596059

theorem tailTrace_5087715 : CollatzResearch.WordTrace tailWord_5087715 prefixEnd_5087715 290271469787740780596059 := by
  unfold tailWord_5087715
  simp only [CollatzResearch.WordTrace]
  refine ⟨185564210763084942389448599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123709473842056628259632399 185564210763084942389448599)
  ·
    refine ⟨278346316144627413584172899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185564210763084942389448599 278346316144627413584172899)
    ·
      refine ⟨417519474216941120376259349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278346316144627413584172899 417519474216941120376259349)
      ·
        refine ⟨19571225353919115017637157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 417519474216941120376259349 19571225353919115017637157)
        ·
          refine ⟨3669604753859834065806967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19571225353919115017637157 3669604753859834065806967)
          ·
            refine ⟨5504407130789751098710451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669604753859834065806967 5504407130789751098710451)
            ·
              refine ⟨8256610696184626648065677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504407130789751098710451 8256610696184626648065677)
              ·
                refine ⟨3096229011069234993024629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8256610696184626648065677 3096229011069234993024629)
                ·
                  refine ⟨290271469787740780596059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096229011069234993024629 290271469787740780596059)
                  ·
                    rfl

theorem cell23_5087715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 5].length) (baseStart_5087715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087715 prefixEnd_5087715 := by exact prefixLift 5087715
  have htrace : WordTrace (prefixWord ++ tailWord_5087715) baseStart_5087715 baseEnd_5087715 := by
    simpa [prefixWord, tailWord_5087715, baseEnd_5087715] using wordTrace_append hprefix tailTrace_5087715
  have hstable : (prefixWord ++ tailWord_5087715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087715).length < 2 ^ (prefixWord ++ tailWord_5087715).sum := by decide
  have hdescent : baseEnd_5087715 < baseStart_5087715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087768 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5087768 : Nat := 118140960795 + 5087768 * 2 ^ 59
def prefixEnd_5087768 : Nat := 4983230072969 + 3 ^ 40 * 5087768 * 2
def baseEnd_5087768 : Nat := 2612470442564355318001787

theorem tailTrace_5087768 : CollatzResearch.WordTrace tailWord_5087768 prefixEnd_5087768 2612470442564355318001787 := by
  unfold tailWord_5087768
  simp only [CollatzResearch.WordTrace]
  refine ⟨92783071915946466220563979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123710762554595288294085305 92783071915946466220563979)
  ·
    refine ⟨139174607873919699330845969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92783071915946466220563979 139174607873919699330845969)
    ·
      refine ⟨104380955905439774498134477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139174607873919699330845969 104380955905439774498134477)
      ·
        refine ⟨39142858464539915436800429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104380955905439774498134477 39142858464539915436800429)
        ·
          refine ⟨14678571924202468288800161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39142858464539915436800429 14678571924202468288800161)
          ·
            refine ⟨11008928943151851216600121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14678571924202468288800161 11008928943151851216600121)
            ·
              refine ⟨8256696707363888412450091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11008928943151851216600121 8256696707363888412450091)
              ·
                refine ⟨12385045061045832618675137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256696707363888412450091 12385045061045832618675137)
                ·
                  refine ⟨9288783795784374464006353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12385045061045832618675137 9288783795784374464006353)
                  ·
                    refine ⟨6966587846838280848004765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9288783795784374464006353 6966587846838280848004765)
                    ·
                      refine ⟨2612470442564355318001787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966587846838280848004765 2612470442564355318001787)
                      ·
                        rfl

theorem cell23_5087768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5087768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087768 prefixEnd_5087768 := by exact prefixLift 5087768
  have htrace : WordTrace (prefixWord ++ tailWord_5087768) baseStart_5087768 baseEnd_5087768 := by
    simpa [prefixWord, tailWord_5087768, baseEnd_5087768] using wordTrace_append hprefix tailTrace_5087768
  have hstable : (prefixWord ++ tailWord_5087768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087768).length < 2 ^ (prefixWord ++ tailWord_5087768).sum := by decide
  have hdescent : baseEnd_5087768 < baseStart_5087768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_5087824 : Nat := 118140960795 + 5087824 * 2 ^ 59
def prefixEnd_5087824 : Nat := 4983230072969 + 3 ^ 40 * 5087824 * 2
def baseEnd_5087824 : Nat := 2612499197481007098901529

theorem tailTrace_5087824 : CollatzResearch.WordTrace tailWord_5087824 prefixEnd_5087824 2612499197481007098901529 := by
  unfold tailWord_5087824
  simp only [CollatzResearch.WordTrace]
  refine ⟨92784093159845027002583263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123712124213126702670111017 92784093159845027002583263)
  ·
    refine ⟨139176139739767540503874895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92784093159845027002583263 139176139739767540503874895)
    ·
      refine ⟨208764209609651310755812343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139176139739767540503874895 208764209609651310755812343)
      ·
        refine ⟨313146314414476966133718515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208764209609651310755812343 313146314414476966133718515)
        ·
          refine ⟨469719471621715449200577773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313146314414476966133718515 469719471621715449200577773)
          ·
            refine ⟨176144801858143293450216665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469719471621715449200577773 176144801858143293450216665)
            ·
              refine ⟨132108601393607470087662499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176144801858143293450216665 132108601393607470087662499)
              ·
                refine ⟨198162902090411205131493749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132108601393607470087662499 198162902090411205131493749)
                ·
                  refine ⟨18577772070976050481077539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198162902090411205131493749 18577772070976050481077539)
                  ·
                    refine ⟨27866658106464075721616309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18577772070976050481077539 27866658106464075721616309)
                    ·
                      refine ⟨2612499197481007098901529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27866658106464075721616309 2612499197481007098901529)
                      ·
                        rfl

theorem cell23_5087824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_5087824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087824 prefixEnd_5087824 := by exact prefixLift 5087824
  have htrace : WordTrace (prefixWord ++ tailWord_5087824) baseStart_5087824 baseEnd_5087824 := by
    simpa [prefixWord, tailWord_5087824, baseEnd_5087824] using wordTrace_append hprefix tailTrace_5087824
  have hstable : (prefixWord ++ tailWord_5087824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087824).length < 2 ^ (prefixWord ++ tailWord_5087824).sum := by decide
  have hdescent : baseEnd_5087824 < baseStart_5087824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087825 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_5087825 : Nat := 118140960795 + 5087825 * 2 ^ 59
def prefixEnd_5087825 : Nat := 4983230072969 + 3 ^ 40 * 5087825 * 2
def baseEnd_5087825 : Nat := 2612499710961661594989025

theorem tailTrace_5087825 : CollatzResearch.WordTrace tailWord_5087825 prefixEnd_5087825 2612499710961661594989025 := by
  unfold tailWord_5087825
  simp only [CollatzResearch.WordTrace]
  refine ⟨185568222792686431175952929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123712148528457620783968619 185568222792686431175952929)
  ·
    refine ⟨139176167094514823381964697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185568222792686431175952929 139176167094514823381964697)
    ·
      refine ⟨104382125320886117536473523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139176167094514823381964697 104382125320886117536473523)
      ·
        refine ⟨156573187981329176304710285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104382125320886117536473523 156573187981329176304710285)
        ·
          refine ⟨58714945492998441114266357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156573187981329176304710285 58714945492998441114266357)
          ·
            refine ⟨5504526139968603854462471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58714945492998441114266357 5504526139968603854462471)
            ·
              refine ⟨8256789209952905781693707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504526139968603854462471 8256789209952905781693707)
              ·
                refine ⟨12385183814929358672540561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256789209952905781693707 12385183814929358672540561)
                ·
                  refine ⟨9288887861197019004405421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12385183814929358672540561 9288887861197019004405421)
                  ·
                    refine ⟨3483332947948882126652033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9288887861197019004405421 3483332947948882126652033)
                    ·
                      refine ⟨2612499710961661594989025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483332947948882126652033 2612499710961661594989025)
                      ·
                        rfl

theorem cell23_5087825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_5087825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087825 prefixEnd_5087825 := by exact prefixLift 5087825
  have htrace : WordTrace (prefixWord ++ tailWord_5087825) baseStart_5087825 baseEnd_5087825 := by
    simpa [prefixWord, tailWord_5087825, baseEnd_5087825] using wordTrace_append hprefix tailTrace_5087825
  have hstable : (prefixWord ++ tailWord_5087825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087825).length < 2 ^ (prefixWord ++ tailWord_5087825).sum := by decide
  have hdescent : baseEnd_5087825 < baseStart_5087825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087831 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 4, 4]
def baseStart_5087831 : Nat := 118140960795 + 5087831 * 2 ^ 59
def prefixEnd_5087831 : Nat := 4983230072969 + 3 ^ 40 * 5087831 * 2
def baseEnd_5087831 : Nat := 870834263948529523837999

theorem tailTrace_5087831 : CollatzResearch.WordTrace tailWord_5087831 prefixEnd_5087831 870834263948529523837999 := by
  unfold tailWord_5087831
  simp only [CollatzResearch.WordTrace]
  refine ⟨185568441630664694200671347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123712294420443129467114231 185568441630664694200671347)
  ·
    refine ⟨278352662445997041301007021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185568441630664694200671347 278352662445997041301007021)
    ·
      refine ⟨104382248417248890487877633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278352662445997041301007021 104382248417248890487877633)
      ·
        refine ⟨78286686312936667865908225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104382248417248890487877633 78286686312936667865908225)
        ·
          refine ⟨58715014734702500899431169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78286686312936667865908225 58715014734702500899431169)
          ·
            refine ⟨44036261051026875674573377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58715014734702500899431169 44036261051026875674573377)
            ·
              refine ⟨33027195788270156755930033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44036261051026875674573377 33027195788270156755930033)
              ·
                refine ⟨24770396841202617566947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33027195788270156755930033 24770396841202617566947525)
                ·
                  refine ⟨4644449407725490793802661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24770396841202617566947525 4644449407725490793802661)
                  ·
                    refine ⟨870834263948529523837999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644449407725490793802661 870834263948529523837999)
                    ·
                      rfl

theorem cell23_5087831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_5087831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087831 prefixEnd_5087831 := by exact prefixLift 5087831
  have htrace : WordTrace (prefixWord ++ tailWord_5087831) baseStart_5087831 baseEnd_5087831 := by
    simpa [prefixWord, tailWord_5087831, baseEnd_5087831] using wordTrace_append hprefix tailTrace_5087831
  have hstable : (prefixWord ++ tailWord_5087831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087831).length < 2 ^ (prefixWord ++ tailWord_5087831).sum := by decide
  have hdescent : baseEnd_5087831 < baseStart_5087831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087834 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5087834 : Nat := 118140960795 + 5087834 * 2 ^ 59
def prefixEnd_5087834 : Nat := 4983230072969 + 3 ^ 40 * 5087834 * 2
def baseEnd_5087834 : Nat := 2612504332287552059776483

theorem tailTrace_5087834 : CollatzResearch.WordTrace tailWord_5087834 prefixEnd_5087834 2612504332287552059776483 := by
  unfold tailWord_5087834
  simp only [CollatzResearch.WordTrace]
  refine ⟨46392137762413456428257639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123712367366435883808687037 46392137762413456428257639)
  ·
    refine ⟨69588206643620184642386459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46392137762413456428257639 69588206643620184642386459)
    ·
      refine ⟨104382309965430276963579689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69588206643620184642386459 104382309965430276963579689)
      ·
        refine ⟨78286732474072707722684767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104382309965430276963579689 78286732474072707722684767)
        ·
          refine ⟨117430098711109061584027151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78286732474072707722684767 117430098711109061584027151)
          ·
            refine ⟨176145148066663592376040727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117430098711109061584027151 176145148066663592376040727)
            ·
              refine ⟨264217722099995388564061091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176145148066663592376040727 264217722099995388564061091)
              ·
                refine ⟨396326583149993082846091637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264217722099995388564061091 396326583149993082846091637)
                ·
                  refine ⟨37155617170311851516821091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396326583149993082846091637 37155617170311851516821091)
                  ·
                    refine ⟨55733425755467777275231637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37155617170311851516821091 55733425755467777275231637)
                    ·
                      refine ⟨2612504332287552059776483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55733425755467777275231637 2612504332287552059776483)
                      ·
                        rfl

theorem cell23_5087834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5087834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087834 prefixEnd_5087834 := by exact prefixLift 5087834
  have htrace : WordTrace (prefixWord ++ tailWord_5087834) baseStart_5087834 baseEnd_5087834 := by
    simpa [prefixWord, tailWord_5087834, baseEnd_5087834] using wordTrace_append hprefix tailTrace_5087834
  have hstable : (prefixWord ++ tailWord_5087834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087834).length < 2 ^ (prefixWord ++ tailWord_5087834).sum := by decide
  have hdescent : baseEnd_5087834 < baseStart_5087834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087844 : List Nat := [2, 3, 1, 1, 2, 2, 12]
def baseStart_5087844 : Nat := 118140960795 + 5087844 * 2 ^ 59
def prefixEnd_5087844 : Nat := 4983230072969 + 3 ^ 40 * 5087844 * 2
def baseEnd_5087844 : Nat := 32253203297457987909277

theorem tailTrace_5087844 : CollatzResearch.WordTrace tailWord_5087844 prefixEnd_5087844 32253203297457987909277 := by
  unfold tailWord_5087844
  simp only [CollatzResearch.WordTrace]
  refine ⟨92784457889808798710447293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123712610519745064947263057 92784457889808798710447293)
  ·
    refine ⟨34794171708678299516417735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92784457889808798710447293 34794171708678299516417735)
    ·
      refine ⟨52191257563017449274626603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34794171708678299516417735 52191257563017449274626603)
      ·
        refine ⟨78286886344526173911939905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52191257563017449274626603 78286886344526173911939905)
        ·
          refine ⟨58715164758394630433954929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78286886344526173911939905 58715164758394630433954929)
          ·
            refine ⟨44036373568795972825466197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58715164758394630433954929 44036373568795972825466197)
            ·
              refine ⟨32253203297457987909277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44036373568795972825466197 32253203297457987909277)
              ·
                rfl

theorem cell23_5087844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 12].length) (baseStart_5087844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087844 prefixEnd_5087844 := by exact prefixLift 5087844
  have htrace : WordTrace (prefixWord ++ tailWord_5087844) baseStart_5087844 baseEnd_5087844 := by
    simpa [prefixWord, tailWord_5087844, baseEnd_5087844] using wordTrace_append hprefix tailTrace_5087844
  have hstable : (prefixWord ++ tailWord_5087844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087844).length < 2 ^ (prefixWord ++ tailWord_5087844).sum := by decide
  have hdescent : baseEnd_5087844 < baseStart_5087844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087858 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5087858 : Nat := 118140960795 + 5087858 * 2 ^ 59
def prefixEnd_5087858 : Nat := 4983230072969 + 3 ^ 40 * 5087858 * 2
def baseEnd_5087858 : Nat := 2612516655823259965876373

theorem tailTrace_5087858 : CollatzResearch.WordTrace tailWord_5087858 prefixEnd_5087858 2612516655823259965876373 := by
  unfold tailWord_5087858
  simp only [CollatzResearch.WordTrace]
  refine ⟨46392356600391719452976057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123712950934377918541269485 46392356600391719452976057)
  ·
    refine ⟨34794267450293789589732043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46392356600391719452976057 34794267450293789589732043)
    ·
      refine ⟨52191401175440684384598065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34794267450293789589732043 52191401175440684384598065)
      ·
        refine ⟨39143550881580513288448549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52191401175440684384598065 39143550881580513288448549)
        ·
          refine ⟨7339415790296346241584103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39143550881580513288448549 7339415790296346241584103)
          ·
            refine ⟨11009123685444519362376155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7339415790296346241584103 11009123685444519362376155)
            ·
              refine ⟨16513685528166779043564233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009123685444519362376155 16513685528166779043564233)
              ·
                refine ⟨12385264146125084282673175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16513685528166779043564233 12385264146125084282673175)
                ·
                  refine ⟨18577896219187626424009763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385264146125084282673175 18577896219187626424009763)
                  ·
                    refine ⟨27866844328781439636014645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18577896219187626424009763 27866844328781439636014645)
                    ·
                      refine ⟨2612516655823259965876373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27866844328781439636014645 2612516655823259965876373)
                      ·
                        rfl

theorem cell23_5087858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5087858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087858 prefixEnd_5087858 := by exact prefixLift 5087858
  have htrace : WordTrace (prefixWord ++ tailWord_5087858) baseStart_5087858 baseEnd_5087858 := by
    simpa [prefixWord, tailWord_5087858, baseEnd_5087858] using wordTrace_append hprefix tailTrace_5087858
  have hstable : (prefixWord ++ tailWord_5087858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087858).length < 2 ^ (prefixWord ++ tailWord_5087858).sum := by decide
  have hdescent : baseEnd_5087858 < baseStart_5087858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087864 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_5087864 : Nat := 118140960795 + 5087864 * 2 ^ 59
def prefixEnd_5087864 : Nat := 4983230072969 + 3 ^ 40 * 5087864 * 2
def baseEnd_5087864 : Nat := 2612519736707186942401345

theorem tailTrace_5087864 : CollatzResearch.WordTrace tailWord_5087864 prefixEnd_5087864 2612519736707186942401345 := by
  unfold tailWord_5087864
  simp only [CollatzResearch.WordTrace]
  refine ⟨92784822619772570418311323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123713096826363427224415097 92784822619772570418311323)
  ·
    refine ⟨139177233929658855627466985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92784822619772570418311323 139177233929658855627466985)
    ·
      refine ⟨104382925447244141720600239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139177233929658855627466985 104382925447244141720600239)
      ·
        refine ⟨156574388170866212580900359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104382925447244141720600239 156574388170866212580900359)
        ·
          refine ⟨234861582256299318871350539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156574388170866212580900359 234861582256299318871350539)
          ·
            refine ⟨352292373384448978307025809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234861582256299318871350539 352292373384448978307025809)
            ·
              refine ⟨264219280038336733730269357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352292373384448978307025809 264219280038336733730269357)
              ·
                refine ⟨99082230014376275148851009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264219280038336733730269357 99082230014376275148851009)
                ·
                  refine ⟨74311672510782206361638257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99082230014376275148851009 74311672510782206361638257)
                  ·
                    refine ⟨55733754383086654771228693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74311672510782206361638257 55733754383086654771228693)
                    ·
                      refine ⟨2612519736707186942401345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55733754383086654771228693 2612519736707186942401345)
                      ·
                        rfl

theorem cell23_5087864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_5087864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087864 prefixEnd_5087864 := by exact prefixLift 5087864
  have htrace : WordTrace (prefixWord ++ tailWord_5087864) baseStart_5087864 baseEnd_5087864 := by
    simpa [prefixWord, tailWord_5087864, baseEnd_5087864] using wordTrace_append hprefix tailTrace_5087864
  have hstable : (prefixWord ++ tailWord_5087864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087864).length < 2 ^ (prefixWord ++ tailWord_5087864).sum := by decide
  have hdescent : baseEnd_5087864 < baseStart_5087864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087865 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_5087865 : Nat := 118140960795 + 5087865 * 2 ^ 59
def prefixEnd_5087865 : Nat := 4983230072969 + 3 ^ 40 * 5087865 * 2
def baseEnd_5087865 : Nat := 870840083395947146162947

theorem tailTrace_5087865 : CollatzResearch.WordTrace tailWord_5087865 prefixEnd_5087865 870840083395947146162947 := by
  unfold tailWord_5087865
  simp only [CollatzResearch.WordTrace]
  refine ⟨185569681712541518007409049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123713121141694345338272699 185569681712541518007409049)
  ·
    refine ⟨139177261284406138505556787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185569681712541518007409049 139177261284406138505556787)
    ·
      refine ⟨208765891926609207758335181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139177261284406138505556787 208765891926609207758335181)
      ·
        refine ⟨78287209472478452909375693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208765891926609207758335181 78287209472478452909375693)
        ·
          refine ⟨29357703552179419841015885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78287209472478452909375693 29357703552179419841015885)
          ·
            refine ⟨11009138832067282440380957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29357703552179419841015885 11009138832067282440380957)
            ·
              refine ⟨4128427062025230915142859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11009138832067282440380957 4128427062025230915142859)
              ·
                refine ⟨6192640593037846372714289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128427062025230915142859 6192640593037846372714289)
                ·
                  refine ⟨4644480444778384779535717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192640593037846372714289 4644480444778384779535717)
                  ·
                    refine ⟨870840083395947146162947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644480444778384779535717 870840083395947146162947)
                    ·
                      rfl

theorem cell23_5087865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_5087865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087865 prefixEnd_5087865 := by exact prefixLift 5087865
  have htrace : WordTrace (prefixWord ++ tailWord_5087865) baseStart_5087865 baseEnd_5087865 := by
    simpa [prefixWord, tailWord_5087865, baseEnd_5087865] using wordTrace_append hprefix tailTrace_5087865
  have hstable : (prefixWord ++ tailWord_5087865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087865).length < 2 ^ (prefixWord ++ tailWord_5087865).sum := by decide
  have hdescent : baseEnd_5087865 < baseStart_5087865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087871 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_5087871 : Nat := 118140960795 + 5087871 * 2 ^ 59
def prefixEnd_5087871 : Nat := 4983230072969 + 3 ^ 40 * 5087871 * 2
def baseEnd_5087871 : Nat := 2612523331071768415013813

theorem tailTrace_5087871 : CollatzResearch.WordTrace tailWord_5087871 prefixEnd_5087871 2612523331071768415013813 := by
  unfold tailWord_5087871
  simp only [CollatzResearch.WordTrace]
  refine ⟨185569900550519781032127467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123713267033679854021418311 185569900550519781032127467)
  ·
    refine ⟨278354850825779671548191201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185569900550519781032127467 278354850825779671548191201)
    ·
      refine ⟨208766138119334753661143401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278354850825779671548191201 208766138119334753661143401)
      ·
        refine ⟨156574603589501065245857551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208766138119334753661143401 156574603589501065245857551)
        ·
          refine ⟨234861905384251597868786327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156574603589501065245857551 234861905384251597868786327)
          ·
            refine ⟨352292858076377396803179491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234861905384251597868786327 352292858076377396803179491)
            ·
              refine ⟨528439287114566095204769237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352292858076377396803179491 528439287114566095204769237)
              ·
                refine ⟨12385295791747642856361779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 528439287114566095204769237 12385295791747642856361779)
                ·
                  refine ⟨18577943687621464284542669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385295791747642856361779 18577943687621464284542669)
                  ·
                    refine ⟨6966728882858049106703501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18577943687621464284542669 6966728882858049106703501)
                    ·
                      refine ⟨2612523331071768415013813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966728882858049106703501 2612523331071768415013813)
                      ·
                        rfl

theorem cell23_5087871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_5087871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087871 prefixEnd_5087871 := by exact prefixLift 5087871
  have htrace : WordTrace (prefixWord ++ tailWord_5087871) baseStart_5087871 baseEnd_5087871 := by
    simpa [prefixWord, tailWord_5087871, baseEnd_5087871] using wordTrace_append hprefix tailTrace_5087871
  have hstable : (prefixWord ++ tailWord_5087871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087871).length < 2 ^ (prefixWord ++ tailWord_5087871).sum := by decide
  have hdescent : baseEnd_5087871 < baseStart_5087871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087926 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5087926 : Nat := 118140960795 + 5087926 * 2 ^ 59
def prefixEnd_5087926 : Nat := 4983230072969 + 3 ^ 40 * 5087926 * 2
def baseEnd_5087926 : Nat := 2612551572507765699826061

theorem tailTrace_5087926 : CollatzResearch.WordTrace tailWord_5087926 prefixEnd_5087926 2612551572507765699826061 := by
  unfold tailWord_5087926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598244160332532839086227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123714604376880350283586421 11598244160332532839086227)
  ·
    refine ⟨17397366240498799258629341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11598244160332532839086227 17397366240498799258629341)
    ·
      refine ⟨6524012340187049721986003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17397366240498799258629341 6524012340187049721986003)
      ·
        refine ⟨9786018510280574582979005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524012340187049721986003 9786018510280574582979005)
        ·
          refine ⟨3669756941355215468617127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9786018510280574582979005 3669756941355215468617127)
          ·
            refine ⟨5504635412032823202925691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669756941355215468617127 5504635412032823202925691)
            ·
              refine ⟨8256953118049234804388537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504635412032823202925691 8256953118049234804388537)
              ·
                refine ⟨6192714838536926103291403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8256953118049234804388537 6192714838536926103291403)
                ·
                  refine ⟨9289072257805389154937105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6192714838536926103291403 9289072257805389154937105)
                  ·
                    refine ⟨6966804193354041866202829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9289072257805389154937105 6966804193354041866202829)
                    ·
                      refine ⟨2612551572507765699826061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6966804193354041866202829 2612551572507765699826061)
                      ·
                        rfl

theorem cell23_5087926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5087926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087926 prefixEnd_5087926 := by exact prefixLift 5087926
  have htrace : WordTrace (prefixWord ++ tailWord_5087926) baseStart_5087926 baseEnd_5087926 := by
    simpa [prefixWord, tailWord_5087926, baseEnd_5087926] using wordTrace_append hprefix tailTrace_5087926
  have hstable : (prefixWord ++ tailWord_5087926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087926).length < 2 ^ (prefixWord ++ tailWord_5087926).sum := by decide
  have hdescent : baseEnd_5087926 < baseStart_5087926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087948 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5087948 : Nat := 118140960795 + 5087948 * 2 ^ 59
def prefixEnd_5087948 : Nat := 4983230072969 + 3 ^ 40 * 5087948 * 2
def baseEnd_5087948 : Nat := 2612562869082164613750959

theorem tailTrace_5087948 : CollatzResearch.WordTrace tailWord_5087948 prefixEnd_5087948 2612562869082164613750959 := by
  unfold tailWord_5087948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92786354485620411591340249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123715139314160548788453665 92786354485620411591340249)
  ·
    refine ⟨69589765864215308693505187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92786354485620411591340249 69589765864215308693505187)
    ·
      refine ⟨104384648796322963040257781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69589765864215308693505187 104384648796322963040257781)
      ·
        refine ⟨9786060824655277785024167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104384648796322963040257781 9786060824655277785024167)
        ·
          refine ⟨14679091236982916677536251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9786060824655277785024167 14679091236982916677536251)
          ·
            refine ⟨22018636855474375016304377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679091236982916677536251 22018636855474375016304377)
            ·
              refine ⟨16513977641605781262228283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22018636855474375016304377 16513977641605781262228283)
              ·
                refine ⟨24770966462408671893342425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16513977641605781262228283 24770966462408671893342425)
                ·
                  refine ⟨18578224846806503920006819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24770966462408671893342425 18578224846806503920006819)
                  ·
                    refine ⟨27867337270209755880010229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18578224846806503920006819 27867337270209755880010229)
                    ·
                      refine ⟨2612562869082164613750959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27867337270209755880010229 2612562869082164613750959)
                      ·
                        rfl

theorem cell23_5087948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5087948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087948 prefixEnd_5087948 := by exact prefixLift 5087948
  have htrace : WordTrace (prefixWord ++ tailWord_5087948) baseStart_5087948 baseEnd_5087948 := by
    simpa [prefixWord, tailWord_5087948, baseEnd_5087948] using wordTrace_append hprefix tailTrace_5087948
  have hstable : (prefixWord ++ tailWord_5087948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087948).length < 2 ^ (prefixWord ++ tailWord_5087948).sum := by decide
  have hdescent : baseEnd_5087948 < baseStart_5087948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5087962 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_5087962 : Nat := 118140960795 + 5087962 * 2 ^ 59
def prefixEnd_5087962 : Nat := 4983230072969 + 3 ^ 40 * 5087962 * 2
def baseEnd_5087962 : Nat := 2612570057811327558975895

theorem tailTrace_5087962 : CollatzResearch.WordTrace tailWord_5087962 prefixEnd_5087962 2612570057811327558975895 := by
  unfold tailWord_5087962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46393304898297525893422535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123715479728793402382460093 46393304898297525893422535)
  ·
    refine ⟨69589957347446288840133803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46393304898297525893422535 69589957347446288840133803)
    ·
      refine ⟨104384936021169433260200705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69589957347446288840133803 104384936021169433260200705)
      ·
        refine ⟨78288702015877074945150529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104384936021169433260200705 78288702015877074945150529)
        ·
          refine ⟨58716526511907806208862897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78288702015877074945150529 58716526511907806208862897)
          ·
            refine ⟨44037394883930854656647173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58716526511907806208862897 44037394883930854656647173)
            ·
              refine ⟨8257011540737035248121345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44037394883930854656647173 8257011540737035248121345)
              ·
                refine ⟨6192758655552776436091009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8257011540737035248121345 6192758655552776436091009)
                ·
                  refine ⟨4644568991664582327068257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192758655552776436091009 4644568991664582327068257)
                  ·
                    refine ⟨3483426743748436745301193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644568991664582327068257 3483426743748436745301193)
                    ·
                      refine ⟨2612570057811327558975895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483426743748436745301193 2612570057811327558975895)
                      ·
                        rfl

theorem cell23_5087962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_5087962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5087962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5087962 prefixEnd_5087962 := by exact prefixLift 5087962
  have htrace : WordTrace (prefixWord ++ tailWord_5087962) baseStart_5087962 baseEnd_5087962 := by
    simpa [prefixWord, tailWord_5087962, baseEnd_5087962] using wordTrace_append hprefix tailTrace_5087962
  have hstable : (prefixWord ++ tailWord_5087962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5087962).length < 2 ^ (prefixWord ++ tailWord_5087962).sum := by decide
  have hdescent : baseEnd_5087962 < baseStart_5087962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5087962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088002 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_5088002 : Nat := 118140960795 + 5088002 * 2 ^ 59
def prefixEnd_5088002 : Nat := 4983230072969 + 3 ^ 40 * 5088002 * 2
def baseEnd_5088002 : Nat := 290287844115278600275079

theorem tailTrace_5088002 : CollatzResearch.WordTrace tailWord_5088002 prefixEnd_5088002 290287844115278600275079 := by
  unfold tailWord_5088002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46393669628261297601286565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123716452342030126936764173 46393669628261297601286565)
  ·
    refine ⟨8698813055298993300241231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46393669628261297601286565 8698813055298993300241231)
    ·
      refine ⟨13048219582948489950361847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8698813055298993300241231 13048219582948489950361847)
      ·
        refine ⟨19572329374422734925542771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13048219582948489950361847 19572329374422734925542771)
        ·
          refine ⟨29358494061634102388314157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19572329374422734925542771 29358494061634102388314157)
          ·
            refine ⟨11009435273112788395617809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29358494061634102388314157 11009435273112788395617809)
            ·
              refine ⟨8257076454834591296713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11009435273112788395617809 8257076454834591296713357)
              ·
                refine ⟨3096403670562971736267509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8257076454834591296713357 3096403670562971736267509)
                ·
                  refine ⟨290287844115278600275079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096403670562971736267509 290287844115278600275079)
                  ·
                    rfl

theorem cell23_5088002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_5088002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088002 prefixEnd_5088002 := by exact prefixLift 5088002
  have htrace : WordTrace (prefixWord ++ tailWord_5088002) baseStart_5088002 baseEnd_5088002 := by
    simpa [prefixWord, tailWord_5088002, baseEnd_5088002] using wordTrace_append hprefix tailTrace_5088002
  have hstable : (prefixWord ++ tailWord_5088002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088002).length < 2 ^ (prefixWord ++ tailWord_5088002).sum := by decide
  have hdescent : baseEnd_5088002 < baseStart_5088002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088092 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 6]
def baseStart_5088092 : Nat := 118140960795 + 5088092 * 2 ^ 59
def prefixEnd_5088092 : Nat := 4983230072969 + 3 ^ 40 * 5088092 * 2
def baseEnd_5088092 : Nat := 290292978921823561150033

theorem tailTrace_5088092 : CollatzResearch.WordTrace tailWord_5088092 prefixEnd_5088092 290292978921823561150033 := by
  unfold tailWord_5088092
  simp only [CollatzResearch.WordTrace]
  refine ⟨92788980541359567887961265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123718640721812757183948353 92788980541359567887961265)
  ·
    refine ⟨69591735406019675915970949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92788980541359567887961265 69591735406019675915970949)
    ·
      refine ⟨13048450388628689234244553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69591735406019675915970949 13048450388628689234244553)
      ·
        refine ⟨9786337791471516925683415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13048450388628689234244553 9786337791471516925683415)
        ·
          refine ⟨14679506687207275388525123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9786337791471516925683415 14679506687207275388525123)
          ·
            refine ⟨22019260030810913082787685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679506687207275388525123 22019260030810913082787685)
            ·
              refine ⟨4128611255777046203022691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22019260030810913082787685 4128611255777046203022691)
              ·
                refine ⟨6192916883665569304534037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128611255777046203022691 6192916883665569304534037)
                ·
                  refine ⟨290292978921823561150033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6192916883665569304534037 290292978921823561150033)
                  ·
                    rfl

theorem cell23_5088092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_5088092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088092 prefixEnd_5088092 := by exact prefixLift 5088092
  have htrace : WordTrace (prefixWord ++ tailWord_5088092) baseStart_5088092 baseEnd_5088092 := by
    simpa [prefixWord, tailWord_5088092, baseEnd_5088092] using wordTrace_append hprefix tailTrace_5088092
  have hstable : (prefixWord ++ tailWord_5088092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088092).length < 2 ^ (prefixWord ++ tailWord_5088092).sum := by decide
  have hdescent : baseEnd_5088092 < baseStart_5088092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088095 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 4, 3, 2]
def baseStart_5088095 : Nat := 118140960795 + 5088095 * 2 ^ 59
def prefixEnd_5088095 : Nat := 4983230072969 + 3 ^ 40 * 5088095 * 2
def baseEnd_5088095 : Nat := 2612638350738375538612783

theorem tailTrace_5088095 : CollatzResearch.WordTrace tailWord_5088095 prefixEnd_5088095 2612638350738375538612783 := by
  unfold tailWord_5088095
  simp only [CollatzResearch.WordTrace]
  refine ⟨185578070501708267288281739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123718713667805511525521159 185578070501708267288281739)
  ·
    refine ⟨278367105752562400932422609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185578070501708267288281739 278367105752562400932422609)
    ·
      refine ⟨208775329314421800699316957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278367105752562400932422609 208775329314421800699316957)
      ·
        refine ⟨78290748492908175262243859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208775329314421800699316957 78290748492908175262243859)
        ·
          refine ⟨117436122739362262893365789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78290748492908175262243859 117436122739362262893365789)
          ·
            refine ⟨44038546027260848585012171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117436122739362262893365789 44038546027260848585012171)
            ·
              refine ⟨66057819040891272877518257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44038546027260848585012171 66057819040891272877518257)
              ·
                refine ⟨49543364280668454658138693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66057819040891272877518257 49543364280668454658138693)
                ·
                  refine ⟨9289380802625335248401005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49543364280668454658138693 9289380802625335248401005)
                  ·
                    refine ⟨3483517800984500718150377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9289380802625335248401005 3483517800984500718150377)
                    ·
                      refine ⟨2612638350738375538612783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483517800984500718150377 2612638350738375538612783)
                      ·
                        rfl

theorem cell23_5088095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_5088095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088095 prefixEnd_5088095 := by exact prefixLift 5088095
  have htrace : WordTrace (prefixWord ++ tailWord_5088095) baseStart_5088095 baseEnd_5088095 := by
    simpa [prefixWord, tailWord_5088095, baseEnd_5088095] using wordTrace_append hprefix tailTrace_5088095
  have hstable : (prefixWord ++ tailWord_5088095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088095).length < 2 ^ (prefixWord ++ tailWord_5088095).sum := by decide
  have hdescent : baseEnd_5088095 < baseStart_5088095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088125 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_5088125 : Nat := 118140960795 + 5088125 * 2 ^ 59
def prefixEnd_5088125 : Nat := 4983230072969 + 3 ^ 40 * 5088125 * 2
def baseEnd_5088125 : Nat := 2612653755158010421237645

theorem tailTrace_5088125 : CollatzResearch.WordTrace tailWord_5088125 prefixEnd_5088125 2612653755158010421237645 := by
  unfold tailWord_5088125
  simp only [CollatzResearch.WordTrace]
  refine ⟨185579164691599582411873829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123719443127733054941249219 185579164691599582411873829)
  ·
    refine ⟨34796093379674921702226343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185579164691599582411873829 34796093379674921702226343)
    ·
      refine ⟨52194140069512382553339515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34796093379674921702226343 52194140069512382553339515)
      ·
        refine ⟨78291210104268573830009273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52194140069512382553339515 78291210104268573830009273)
        ·
          refine ⟨58718407578201430372506955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78291210104268573830009273 58718407578201430372506955)
          ·
            refine ⟨88077611367302145558760433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58718407578201430372506955 88077611367302145558760433)
            ·
              refine ⟨66058208525476609169070325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88077611367302145558760433 66058208525476609169070325)
              ·
                refine ⟨6192957049263432109600343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66058208525476609169070325 6192957049263432109600343)
                ·
                  refine ⟨9289435573895148164400515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6192957049263432109600343 9289435573895148164400515)
                  ·
                    refine ⟨13934153360842722246600773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9289435573895148164400515 13934153360842722246600773)
                    ·
                      refine ⟨2612653755158010421237645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13934153360842722246600773 2612653755158010421237645)
                      ·
                        rfl

theorem cell23_5088125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_5088125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088125 prefixEnd_5088125 := by exact prefixLift 5088125
  have htrace : WordTrace (prefixWord ++ tailWord_5088125) baseStart_5088125 baseEnd_5088125 := by
    simpa [prefixWord, tailWord_5088125, baseEnd_5088125] using wordTrace_append hprefix tailTrace_5088125
  have hstable : (prefixWord ++ tailWord_5088125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088125).length < 2 ^ (prefixWord ++ tailWord_5088125).sum := by decide
  have hdescent : baseEnd_5088125 < baseStart_5088125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088128 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_5088128 : Nat := 118140960795 + 5088128 * 2 ^ 59
def prefixEnd_5088128 : Nat := 4983230072969 + 3 ^ 40 * 5088128 * 2
def baseEnd_5088128 : Nat := 2612655295599973909500131

theorem tailTrace_5088128 : CollatzResearch.WordTrace tailWord_5088128 prefixEnd_5088128 2612655295599973909500131 := by
  unfold tailWord_5088128
  simp only [CollatzResearch.WordTrace]
  refine ⟨92789637055294356962116519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123719516073725809282822025 92789637055294356962116519)
  ·
    refine ⟨139184455582941535443174779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92789637055294356962116519 139184455582941535443174779)
    ·
      refine ⟨208776683374412303164762169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139184455582941535443174779 208776683374412303164762169)
      ·
        refine ⟨156582512530809227373571627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208776683374412303164762169 156582512530809227373571627)
        ·
          refine ⟨234873768796213841060357441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156582512530809227373571627 234873768796213841060357441)
          ·
            refine ⟨176155326597160380795268081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234873768796213841060357441 176155326597160380795268081)
            ·
              refine ⟨132116494947870285596451061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176155326597160380795268081 132116494947870285596451061)
              ·
                refine ⟨12385921401362839274667287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132116494947870285596451061 12385921401362839274667287)
                ·
                  refine ⟨18578882102044258912000931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385921401362839274667287 18578882102044258912000931)
                  ·
                    refine ⟨27868323153066388368001397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18578882102044258912000931 27868323153066388368001397)
                    ·
                      refine ⟨2612655295599973909500131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27868323153066388368001397 2612655295599973909500131)
                      ·
                        rfl

theorem cell23_5088128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_5088128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088128 prefixEnd_5088128 := by exact prefixLift 5088128
  have htrace : WordTrace (prefixWord ++ tailWord_5088128) baseStart_5088128 baseEnd_5088128 := by
    simpa [prefixWord, tailWord_5088128, baseEnd_5088128] using wordTrace_append hprefix tailTrace_5088128
  have hstable : (prefixWord ++ tailWord_5088128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088128).length < 2 ^ (prefixWord ++ tailWord_5088128).sum := by decide
  have hdescent : baseEnd_5088128 < baseStart_5088128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088130 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5088130 : Nat := 118140960795 + 5088130 * 2 ^ 59
def prefixEnd_5088130 : Nat := 4983230072969 + 3 ^ 40 * 5088130 * 2
def baseEnd_5088130 : Nat := 870885440853760967225041

theorem tailTrace_5088130 : CollatzResearch.WordTrace tailWord_5088130 prefixEnd_5088130 870885440853760967225041 := by
  unfold tailWord_5088130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46394836764145367066451461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123719564704387645510537229 46394836764145367066451461)
  ·
    refine ⟨8699031893277256324959649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46394836764145367066451461 8699031893277256324959649)
    ·
      refine ⟨6524273919957942243719737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699031893277256324959649 6524273919957942243719737)
      ·
        refine ⟨4893205439968456682789803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524273919957942243719737 4893205439968456682789803)
        ·
          refine ⟨7339808159952685024184705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893205439968456682789803 7339808159952685024184705)
          ·
            refine ⟨5504856119964513768138529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7339808159952685024184705 5504856119964513768138529)
            ·
              refine ⟨4128642089973385326103897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504856119964513768138529 4128642089973385326103897)
              ·
                refine ⟨3096481567480038994577923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128642089973385326103897 3096481567480038994577923)
                ·
                  refine ⟨4644722351220058491866885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096481567480038994577923 4644722351220058491866885)
                  ·
                    refine ⟨870885440853760967225041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644722351220058491866885 870885440853760967225041)
                    ·
                      rfl

theorem cell23_5088130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5088130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088130 prefixEnd_5088130 := by exact prefixLift 5088130
  have htrace : WordTrace (prefixWord ++ tailWord_5088130) baseStart_5088130 baseEnd_5088130 := by
    simpa [prefixWord, tailWord_5088130, baseEnd_5088130] using wordTrace_append hprefix tailTrace_5088130
  have hstable : (prefixWord ++ tailWord_5088130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088130).length < 2 ^ (prefixWord ++ tailWord_5088130).sum := by decide
  have hdescent : baseEnd_5088130 < baseStart_5088130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088136 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_5088136 : Nat := 118140960795 + 5088136 * 2 ^ 59
def prefixEnd_5088136 : Nat := 4983230072969 + 3 ^ 40 * 5088136 * 2
def baseEnd_5088136 : Nat := 2612659403445209878200095

theorem tailTrace_5088136 : CollatzResearch.WordTrace tailWord_5088136 prefixEnd_5088136 2612659403445209878200095 := by
  unfold tailWord_5088136
  simp only [CollatzResearch.WordTrace]
  refine ⟨92789782947279865645262131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123719710596373154193682841 92789782947279865645262131)
  ·
    refine ⟨139184674420919798467893197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92789782947279865645262131 139184674420919798467893197)
    ·
      refine ⟨52194252907844924425459949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139184674420919798467893197 52194252907844924425459949)
      ·
        refine ⟨19572844840441846659547481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52194252907844924425459949 19572844840441846659547481)
        ·
          refine ⟨14679633630331384994660611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19572844840441846659547481 14679633630331384994660611)
          ·
            refine ⟨22019450445497077491990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679633630331384994660611 22019450445497077491990917)
            ·
              refine ⟨4128646958530702029748297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22019450445497077491990917 4128646958530702029748297)
              ·
                refine ⟨3096485218898026522311223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128646958530702029748297 3096485218898026522311223)
                ·
                  refine ⟨4644727828347039783466835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096485218898026522311223 4644727828347039783466835)
                  ·
                    refine ⟨6967091742520559675200253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644727828347039783466835 6967091742520559675200253)
                    ·
                      refine ⟨2612659403445209878200095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967091742520559675200253 2612659403445209878200095)
                      ·
                        rfl

theorem cell23_5088136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_5088136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088136 prefixEnd_5088136 := by exact prefixLift 5088136
  have htrace : WordTrace (prefixWord ++ tailWord_5088136) baseStart_5088136 baseEnd_5088136 := by
    simpa [prefixWord, tailWord_5088136, baseEnd_5088136] using wordTrace_append hprefix tailTrace_5088136
  have hstable : (prefixWord ++ tailWord_5088136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088136).length < 2 ^ (prefixWord ++ tailWord_5088136).sum := by decide
  have hdescent : baseEnd_5088136 < baseStart_5088136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088159 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5088159 : Nat := 118140960795 + 5088159 * 2 ^ 59
def prefixEnd_5088159 : Nat := 4983230072969 + 3 ^ 40 * 5088159 * 2
def baseEnd_5088159 : Nat := 2612671213500263288212489

theorem tailTrace_5088159 : CollatzResearch.WordTrace tailWord_5088159 prefixEnd_5088159 2612671213500263288212489 := by
  unfold tailWord_5088159
  simp only [CollatzResearch.WordTrace]
  refine ⟨185580404773476406218611531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123720269848984270812407687 185580404773476406218611531)
  ·
    refine ⟨278370607160214609327917297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185580404773476406218611531 278370607160214609327917297)
    ·
      refine ⟨208777955370160956995937973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278370607160214609327917297 208777955370160956995937973)
      ·
        refine ⟨19572933315952589718369185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208777955370160956995937973 19572933315952589718369185)
        ·
          refine ⟨14679699986964442288776889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19572933315952589718369185 14679699986964442288776889)
          ·
            refine ⟨11009774990223331716582667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14679699986964442288776889 11009774990223331716582667)
            ·
              refine ⟨16514662485334997574874001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009774990223331716582667 16514662485334997574874001)
              ·
                refine ⟨12385996864001248181155501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16514662485334997574874001 12385996864001248181155501)
                ·
                  refine ⟨4644748824000468067933313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12385996864001248181155501 4644748824000468067933313)
                  ·
                    refine ⟨3483561618000351050949985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644748824000468067933313 3483561618000351050949985)
                    ·
                      refine ⟨2612671213500263288212489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483561618000351050949985 2612671213500263288212489)
                      ·
                        rfl

theorem cell23_5088159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5088159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088159 prefixEnd_5088159 := by exact prefixLift 5088159
  have htrace : WordTrace (prefixWord ++ tailWord_5088159) baseStart_5088159 baseEnd_5088159 := by
    simpa [prefixWord, tailWord_5088159, baseEnd_5088159] using wordTrace_append hprefix tailTrace_5088159
  have hstable : (prefixWord ++ tailWord_5088159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088159).length < 2 ^ (prefixWord ++ tailWord_5088159).sum := by decide
  have hdescent : baseEnd_5088159 < baseStart_5088159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088162 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_5088162 : Nat := 118140960795 + 5088162 * 2 ^ 59
def prefixEnd_5088162 : Nat := 4983230072969 + 3 ^ 40 * 5088162 * 2
def baseEnd_5088162 : Nat := 2612672753942226776474975

theorem tailTrace_5088162 : CollatzResearch.WordTrace tailWord_5088162 prefixEnd_5088162 2612672753942226776474975 := by
  unfold tailWord_5088162
  simp only [CollatzResearch.WordTrace]
  refine ⟨46395128548116384432742685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123720342794977025153980493 46395128548116384432742685)
  ·
    refine ⟨17398173205543644162278507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46395128548116384432742685 17398173205543644162278507)
    ·
      refine ⟨26097259808315466243417761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17398173205543644162278507 26097259808315466243417761)
      ·
        refine ⟨19572944856236599682563321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26097259808315466243417761 19572944856236599682563321)
        ·
          refine ⟨14679708642177449761922491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19572944856236599682563321 14679708642177449761922491)
          ·
            refine ⟨22019562963266174642883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679708642177449761922491 22019562963266174642883737)
            ·
              refine ⟨16514672222449630982162803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22019562963266174642883737 16514672222449630982162803)
              ·
                refine ⟨24772008333674446473244205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16514672222449630982162803 24772008333674446473244205)
                ·
                  refine ⟨9289503125127917427466577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24772008333674446473244205 9289503125127917427466577)
                  ·
                    refine ⟨6967127343845938070599933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9289503125127917427466577 6967127343845938070599933)
                    ·
                      refine ⟨2612672753942226776474975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967127343845938070599933 2612672753942226776474975)
                      ·
                        rfl

theorem cell23_5088162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_5088162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088162 prefixEnd_5088162 := by exact prefixLift 5088162
  have htrace : WordTrace (prefixWord ++ tailWord_5088162) baseStart_5088162 baseEnd_5088162 := by
    simpa [prefixWord, tailWord_5088162, baseEnd_5088162] using wordTrace_append hprefix tailTrace_5088162
  have hstable : (prefixWord ++ tailWord_5088162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088162).length < 2 ^ (prefixWord ++ tailWord_5088162).sum := by decide
  have hdescent : baseEnd_5088162 < baseStart_5088162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088173 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5088173 : Nat := 118140960795 + 5088173 * 2 ^ 59
def prefixEnd_5088173 : Nat := 4983230072969 + 3 ^ 40 * 5088173 * 2
def baseEnd_5088173 : Nat := 870892800743142077812475

theorem tailTrace_5088173 : CollatzResearch.WordTrace tailWord_5088173 prefixEnd_5088173 870892800743142077812475 := by
  unfold tailWord_5088173
  simp only [CollatzResearch.WordTrace]
  refine ⟨185580915395425686609621173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123720610263617124406414115 185580915395425686609621173)
  ·
    refine ⟨17398210818321158119651985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185580915395425686609621173 17398210818321158119651985)
    ·
      refine ⟨13048658113740868589738989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17398210818321158119651985 13048658113740868589738989)
      ·
        refine ⟨4893246792652825721152121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13048658113740868589738989 4893246792652825721152121)
        ·
          refine ⟨3669935094489619290864091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893246792652825721152121 3669935094489619290864091)
          ·
            refine ⟨5504902641734428936296137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669935094489619290864091 5504902641734428936296137)
            ·
              refine ⟨4128676981300821702222103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504902641734428936296137 4128676981300821702222103)
              ·
                refine ⟨6193015471951232553333155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128676981300821702222103 6193015471951232553333155)
                ·
                  refine ⟨9289523207926848829999733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193015471951232553333155 9289523207926848829999733)
                  ·
                    refine ⟨870892800743142077812475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9289523207926848829999733 870892800743142077812475)
                    ·
                      rfl

theorem cell23_5088173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5088173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088173 prefixEnd_5088173 := by exact prefixLift 5088173
  have htrace : WordTrace (prefixWord ++ tailWord_5088173) baseStart_5088173 baseEnd_5088173 := by
    simpa [prefixWord, tailWord_5088173, baseEnd_5088173] using wordTrace_append hprefix tailTrace_5088173
  have hstable : (prefixWord ++ tailWord_5088173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088173).length < 2 ^ (prefixWord ++ tailWord_5088173).sum := by decide
  have hdescent : baseEnd_5088173 < baseStart_5088173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088192 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_5088192 : Nat := 118140960795 + 5088192 * 2 ^ 59
def prefixEnd_5088192 : Nat := 4983230072969 + 3 ^ 40 * 5088192 * 2
def baseEnd_5088192 : Nat := 2612688158361861659099837

theorem tailTrace_5088192 : CollatzResearch.WordTrace tailWord_5088192 prefixEnd_5088192 2612688158361861659099837 := by
  unfold tailWord_5088192
  simp only [CollatzResearch.WordTrace]
  refine ⟨92790804191178426427281415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123721072254904568569708553 92790804191178426427281415)
  ·
    refine ⟨139186206286767639640922123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92790804191178426427281415 139186206286767639640922123)
    ·
      refine ⟨208779309430151459461383185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139186206286767639640922123 208779309430151459461383185)
      ·
        refine ⟨156584482072613594596037389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208779309430151459461383185 156584482072613594596037389)
        ·
          refine ⟨58719180777230097973514021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156584482072613594596037389 58719180777230097973514021)
          ·
            refine ⟨11009846395730643370033879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58719180777230097973514021 11009846395730643370033879)
            ·
              refine ⟨16514769593595965055050819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009846395730643370033879 16514769593595965055050819)
              ·
                refine ⟨24772154390393947582576229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16514769593595965055050819 24772154390393947582576229)
                ·
                  refine ⟨4644778948198865171733043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24772154390393947582576229 4644778948198865171733043)
                  ·
                    refine ⟨6967168422298297757599565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644778948198865171733043 6967168422298297757599565)
                    ·
                      refine ⟨2612688158361861659099837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967168422298297757599565 2612688158361861659099837)
                      ·
                        rfl

theorem cell23_5088192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_5088192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088192 prefixEnd_5088192 := by exact prefixLift 5088192
  have htrace : WordTrace (prefixWord ++ tailWord_5088192) baseStart_5088192 baseEnd_5088192 := by
    simpa [prefixWord, tailWord_5088192, baseEnd_5088192] using wordTrace_append hprefix tailTrace_5088192
  have hstable : (prefixWord ++ tailWord_5088192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088192).length < 2 ^ (prefixWord ++ tailWord_5088192).sum := by decide
  have hdescent : baseEnd_5088192 < baseStart_5088192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088209 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_5088209 : Nat := 118140960795 + 5088209 * 2 ^ 59
def prefixEnd_5088209 : Nat := 4983230072969 + 3 ^ 40 * 5088209 * 2
def baseEnd_5088209 : Nat := 2612696887532988092587259

theorem tailTrace_5088209 : CollatzResearch.WordTrace tailWord_5088209 prefixEnd_5088209 2612696887532988092587259 := by
  unfold tailWord_5088209
  simp only [CollatzResearch.WordTrace]
  refine ⟨185582228423295264757931681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123721485615530176505287787 185582228423295264757931681)
  ·
    refine ⟨139186671317471448568448761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185582228423295264757931681 139186671317471448568448761)
    ·
      refine ⟨104390003488103586426336571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139186671317471448568448761 104390003488103586426336571)
      ·
        refine ⟨156585005232155379639504857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104390003488103586426336571 156585005232155379639504857)
        ·
          refine ⟨117438753924116534729628643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156585005232155379639504857 117438753924116534729628643)
          ·
            refine ⟨176158130886174802094442965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117438753924116534729628643 176158130886174802094442965)
            ·
              refine ⟨4128706192644721924088507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176158130886174802094442965 4128706192644721924088507)
              ·
                refine ⟨6193059288967082886132761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128706192644721924088507 6193059288967082886132761)
                ·
                  refine ⟨4644794466725312164599571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193059288967082886132761 4644794466725312164599571)
                  ·
                    refine ⟨6967191700087968246899357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644794466725312164599571 6967191700087968246899357)
                    ·
                      refine ⟨2612696887532988092587259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967191700087968246899357 2612696887532988092587259)
                      ·
                        rfl

theorem cell23_5088209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_5088209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088209 prefixEnd_5088209 := by exact prefixLift 5088209
  have htrace : WordTrace (prefixWord ++ tailWord_5088209) baseStart_5088209 baseEnd_5088209 := by
    simpa [prefixWord, tailWord_5088209, baseEnd_5088209] using wordTrace_append hprefix tailTrace_5088209
  have hstable : (prefixWord ++ tailWord_5088209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088209).length < 2 ^ (prefixWord ++ tailWord_5088209).sum := by decide
  have hdescent : baseEnd_5088209 < baseStart_5088209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088232 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5088232 : Nat := 118140960795 + 5088232 * 2 ^ 59
def prefixEnd_5088232 : Nat := 4983230072969 + 3 ^ 40 * 5088232 * 2
def baseEnd_5088232 : Nat := 2612708697588041502599653

theorem tailTrace_5088232 : CollatzResearch.WordTrace tailWord_5088232 prefixEnd_5088232 2612708697588041502599653 := by
  unfold tailWord_5088232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92791533651105969843009475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123722044868141293124012633 92791533651105969843009475)
  ·
    refine ⟨139187300476658954764514213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92791533651105969843009475 139187300476658954764514213)
    ·
      refine ⟨26097618839373554018346415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139187300476658954764514213 26097618839373554018346415)
      ·
        refine ⟨39146428259060331027519623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26097618839373554018346415 39146428259060331027519623)
        ·
          refine ⟨58719642388590496541279435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39146428259060331027519623 58719642388590496541279435)
          ·
            refine ⟨88079463582885744811919153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58719642388590496541279435 88079463582885744811919153)
            ·
              refine ⟨66059597687164308608939365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88079463582885744811919153 66059597687164308608939365)
              ·
                refine ⟨12386174566343307864176131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66059597687164308608939365 12386174566343307864176131)
                ·
                  refine ⟨18579261849514961796264197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12386174566343307864176131 18579261849514961796264197)
                  ·
                    refine ⟨3483611596784055336799537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18579261849514961796264197 3483611596784055336799537)
                    ·
                      refine ⟨2612708697588041502599653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483611596784055336799537 2612708697588041502599653)
                      ·
                        rfl

theorem cell23_5088232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5088232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088232 prefixEnd_5088232 := by exact prefixLift 5088232
  have htrace : WordTrace (prefixWord ++ tailWord_5088232) baseStart_5088232 baseEnd_5088232 := by
    simpa [prefixWord, tailWord_5088232, baseEnd_5088232] using wordTrace_append hprefix tailTrace_5088232
  have hstable : (prefixWord ++ tailWord_5088232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088232).length < 2 ^ (prefixWord ++ tailWord_5088232).sum := by decide
  have hdescent : baseEnd_5088232 < baseStart_5088232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088244 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5088244 : Nat := 118140960795 + 5088244 * 2 ^ 59
def prefixEnd_5088244 : Nat := 4983230072969 + 3 ^ 40 * 5088244 * 2
def baseEnd_5088244 : Nat := 2612714859355895455649599

theorem tailTrace_5088244 : CollatzResearch.WordTrace tailWord_5088244 prefixEnd_5088244 2612714859355895455649599 := by
  unfold tailWord_5088244
  simp only [CollatzResearch.WordTrace]
  refine ⟨92791752489084232867727893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123722336652112310490303857 92791752489084232867727893)
  ·
    refine ⟨4349613397925823415674745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92791752489084232867727893 4349613397925823415674745)
    ·
      refine ⟨3262210048444367561756059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349613397925823415674745 3262210048444367561756059)
      ·
        refine ⟨4893315072666551342634089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262210048444367561756059 4893315072666551342634089)
        ·
          refine ⟨3669986304499913506975567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893315072666551342634089 3669986304499913506975567)
          ·
            refine ⟨5504979456749870260463351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669986304499913506975567 5504979456749870260463351)
            ·
              refine ⟨8257469185124805390695027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504979456749870260463351 8257469185124805390695027)
              ·
                refine ⟨12386203777687208086042541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8257469185124805390695027 12386203777687208086042541)
                ·
                  refine ⟨4644826416632703032265953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12386203777687208086042541 4644826416632703032265953)
                  ·
                    refine ⟨3483619812474527274199465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644826416632703032265953 3483619812474527274199465)
                    ·
                      refine ⟨2612714859355895455649599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483619812474527274199465 2612714859355895455649599)
                      ·
                        rfl

theorem cell23_5088244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5088244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088244 prefixEnd_5088244 := by exact prefixLift 5088244
  have htrace : WordTrace (prefixWord ++ tailWord_5088244) baseStart_5088244 baseEnd_5088244 := by
    simpa [prefixWord, tailWord_5088244, baseEnd_5088244] using wordTrace_append hprefix tailTrace_5088244
  have hstable : (prefixWord ++ tailWord_5088244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088244).length < 2 ^ (prefixWord ++ tailWord_5088244).sum := by decide
  have hdescent : baseEnd_5088244 < baseStart_5088244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088248 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_5088248 : Nat := 118140960795 + 5088248 * 2 ^ 59
def prefixEnd_5088248 : Nat := 4983230072969 + 3 ^ 40 * 5088248 * 2
def baseEnd_5088248 : Nat := 2612716913278513439999579

theorem tailTrace_5088248 : CollatzResearch.WordTrace tailWord_5088248 prefixEnd_5088248 2612716913278513439999579 := by
  unfold tailWord_5088248
  simp only [CollatzResearch.WordTrace]
  refine ⟨92791825435076987209300699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123722433913435982945734265 92791825435076987209300699)
  ·
    refine ⟨139187738152615480813951049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92791825435076987209300699 139187738152615480813951049)
    ·
      refine ⟨104390803614461610610463287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139187738152615480813951049 104390803614461610610463287)
      ·
        refine ⟨156586205421692415915694931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104390803614461610610463287 156586205421692415915694931)
        ·
          refine ⟨234879308132538623873542397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156586205421692415915694931 234879308132538623873542397)
          ·
            refine ⟨88079740549701983952578399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234879308132538623873542397 88079740549701983952578399)
            ·
              refine ⟨132119610824552975928867599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88079740549701983952578399 132119610824552975928867599)
              ·
                refine ⟨198179416236829463893301399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132119610824552975928867599 198179416236829463893301399)
                ·
                  refine ⟨297269124355244195839952099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198179416236829463893301399 297269124355244195839952099)
                  ·
                    refine ⟨445903686532866293759928149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 297269124355244195839952099 445903686532866293759928149)
                    ·
                      refine ⟨2612716913278513439999579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 445903686532866293759928149 2612716913278513439999579)
                      ·
                        rfl

theorem cell23_5088248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_5088248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088248 prefixEnd_5088248 := by exact prefixLift 5088248
  have htrace : WordTrace (prefixWord ++ tailWord_5088248) baseStart_5088248 baseEnd_5088248 := by
    simpa [prefixWord, tailWord_5088248, baseEnd_5088248] using wordTrace_append hprefix tailTrace_5088248
  have hstable : (prefixWord ++ tailWord_5088248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088248).length < 2 ^ (prefixWord ++ tailWord_5088248).sum := by decide
  have hdescent : baseEnd_5088248 < baseStart_5088248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088249 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 2, 2, 2]
def baseStart_5088249 : Nat := 118140960795 + 5088249 * 2 ^ 59
def prefixEnd_5088249 : Nat := 4983230072969 + 3 ^ 40 * 5088249 * 2
def baseEnd_5088249 : Nat := 2612717426759167936087075

theorem tailTrace_5088249 : CollatzResearch.WordTrace tailWord_5088249 prefixEnd_5088249 2612717426759167936087075 := by
  unfold tailWord_5088249
  simp only [CollatzResearch.WordTrace]
  refine ⟨185583687343150351589387801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123722458228766901059591867 185583687343150351589387801)
  ·
    refine ⟨139187765507362763692040851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185583687343150351589387801 139187765507362763692040851)
    ·
      refine ⟨208781648261044145538061277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139187765507362763692040851 208781648261044145538061277)
      ·
        refine ⟨78293118097891554576772979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208781648261044145538061277 78293118097891554576772979)
        ·
          refine ⟨117439677146837331865159469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78293118097891554576772979 117439677146837331865159469)
          ·
            refine ⟨44039878930063999449434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117439677146837331865159469 44039878930063999449434801)
            ·
              refine ⟨33029909197547999587076101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44039878930063999449434801 33029909197547999587076101)
              ·
                refine ⟨6193107974540249922576769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33029909197547999587076101 6193107974540249922576769)
                ·
                  refine ⟨4644830980905187441932577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193107974540249922576769 4644830980905187441932577)
                  ·
                    refine ⟨3483623235678890581449433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644830980905187441932577 3483623235678890581449433)
                    ·
                      refine ⟨2612717426759167936087075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483623235678890581449433 2612717426759167936087075)
                      ·
                        rfl

theorem cell23_5088249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_5088249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088249 prefixEnd_5088249 := by exact prefixLift 5088249
  have htrace : WordTrace (prefixWord ++ tailWord_5088249) baseStart_5088249 baseEnd_5088249 := by
    simpa [prefixWord, tailWord_5088249, baseEnd_5088249] using wordTrace_append hprefix tailTrace_5088249
  have hstable : (prefixWord ++ tailWord_5088249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088249).length < 2 ^ (prefixWord ++ tailWord_5088249).sum := by decide
  have hdescent : baseEnd_5088249 < baseStart_5088249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088265 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_5088265 : Nat := 118140960795 + 5088265 * 2 ^ 59
def prefixEnd_5088265 : Nat := 4983230072969 + 3 ^ 40 * 5088265 * 2
def baseEnd_5088265 : Nat := 2612725642449639873487001

theorem tailTrace_5088265 : CollatzResearch.WordTrace tailWord_5088265 prefixEnd_5088265 2612725642449639873487001 := by
  unfold tailWord_5088265
  simp only [CollatzResearch.WordTrace]
  refine ⟨185584270911092386321970249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123722847274061590881313499 185584270911092386321970249)
  ·
    refine ⟨139188203183319289741477687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185584270911092386321970249 139188203183319289741477687)
    ·
      refine ⟨208782304774978934612216531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139188203183319289741477687 208782304774978934612216531)
      ·
        refine ⟨313173457162468401918324797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208782304774978934612216531 313173457162468401918324797)
        ·
          refine ⟨117440046435925650719371799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313173457162468401918324797 117440046435925650719371799)
          ·
            refine ⟨176160069653888476079057699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117440046435925650719371799 176160069653888476079057699)
            ·
              refine ⟨264240104480832714118586549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176160069653888476079057699 264240104480832714118586549)
              ·
                refine ⟨24772509795078066948617489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264240104480832714118586549 24772509795078066948617489)
                ·
                  refine ⟨18579382346308550211463117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24772509795078066948617489 18579382346308550211463117)
                  ·
                    refine ⟨6967268379865706329298669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18579382346308550211463117 6967268379865706329298669)
                    ·
                      refine ⟨2612725642449639873487001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967268379865706329298669 2612725642449639873487001)
                      ·
                        rfl

theorem cell23_5088265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_5088265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088265 prefixEnd_5088265 := by exact prefixLift 5088265
  have htrace : WordTrace (prefixWord ++ tailWord_5088265) baseStart_5088265 baseEnd_5088265 := by
    simpa [prefixWord, tailWord_5088265, baseEnd_5088265] using wordTrace_append hprefix tailTrace_5088265
  have hstable : (prefixWord ++ tailWord_5088265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088265).length < 2 ^ (prefixWord ++ tailWord_5088265).sum := by decide
  have hdescent : baseEnd_5088265 < baseStart_5088265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088266 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_5088266 : Nat := 118140960795 + 5088266 * 2 ^ 59
def prefixEnd_5088266 : Nat := 4983230072969 + 3 ^ 40 * 5088266 * 2
def baseEnd_5088266 : Nat := 2612726155930294369574497

theorem tailTrace_5088266 : CollatzResearch.WordTrace tailWord_5088266 prefixEnd_5088266 2612726155930294369574497 := by
  unfold tailWord_5088266
  simp only [CollatzResearch.WordTrace]
  refine ⟨46396076846022190873189163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123722871589392508995171101 46396076846022190873189163)
  ·
    refine ⟨69594115269033286309783745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46396076846022190873189163 69594115269033286309783745)
    ·
      refine ⟨52195586451774964732337809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69594115269033286309783745 52195586451774964732337809)
      ·
        refine ⟨39146689838831223549253357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52195586451774964732337809 39146689838831223549253357)
        ·
          refine ⟨14680008689561708830970009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39146689838831223549253357 14680008689561708830970009)
          ·
            refine ⟨11010006517171281623227507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14680008689561708830970009 11010006517171281623227507)
            ·
              refine ⟨16515009775756922434841261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010006517171281623227507 16515009775756922434841261)
              ·
                refine ⟨6193128665908845913065473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16515009775756922434841261 6193128665908845913065473)
                ·
                  refine ⟨4644846499431634434799105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193128665908845913065473 4644846499431634434799105)
                  ·
                    refine ⟨3483634874573725826099329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644846499431634434799105 3483634874573725826099329)
                    ·
                      refine ⟨2612726155930294369574497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483634874573725826099329 2612726155930294369574497)
                      ·
                        rfl

theorem cell23_5088266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_5088266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088266 prefixEnd_5088266 := by exact prefixLift 5088266
  have htrace : WordTrace (prefixWord ++ tailWord_5088266) baseStart_5088266 baseEnd_5088266 := by
    simpa [prefixWord, tailWord_5088266, baseEnd_5088266] using wordTrace_append hprefix tailTrace_5088266
  have hstable : (prefixWord ++ tailWord_5088266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088266).length < 2 ^ (prefixWord ++ tailWord_5088266).sum := by decide
  have hdescent : baseEnd_5088266 < baseStart_5088266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088302 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5088302 : Nat := 118140960795 + 5088302 * 2 ^ 59
def prefixEnd_5088302 : Nat := 4983230072969 + 3 ^ 40 * 5088302 * 2
def baseEnd_5088302 : Nat := 870914880411285409574777

theorem tailTrace_5088302 : CollatzResearch.WordTrace tailWord_5088302 prefixEnd_5088302 870914880411285409574777 := by
  unfold tailWord_5088302
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198202551494792705133395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123723746941305561094044773 23198202551494792705133395)
  ·
    refine ⟨34797303827242189057700093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198202551494792705133395 34797303827242189057700093)
    ·
      refine ⟨13048988935215820896637535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34797303827242189057700093 13048988935215820896637535)
      ·
        refine ⟨19573483402823731344956303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13048988935215820896637535 19573483402823731344956303)
        ·
          refine ⟨29360225104235597017434455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19573483402823731344956303 29360225104235597017434455)
          ·
            refine ⟨44040337656353395526151683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29360225104235597017434455 44040337656353395526151683)
            ·
              refine ⟨66060506484530093289227525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44040337656353395526151683 66060506484530093289227525)
              ·
                refine ⟨12386344965849392491730161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66060506484530093289227525 12386344965849392491730161)
                ·
                  refine ⟨9289758724387044368797621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12386344965849392491730161 9289758724387044368797621)
                  ·
                    refine ⟨870914880411285409574777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9289758724387044368797621 870914880411285409574777)
                    ·
                      rfl

theorem cell23_5088302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5088302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088302 prefixEnd_5088302 := by exact prefixLift 5088302
  have htrace : WordTrace (prefixWord ++ tailWord_5088302) baseStart_5088302 baseEnd_5088302 := by
    simpa [prefixWord, tailWord_5088302, baseEnd_5088302] using wordTrace_append hprefix tailTrace_5088302
  have hstable : (prefixWord ++ tailWord_5088302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088302).length < 2 ^ (prefixWord ++ tailWord_5088302).sum := by decide
  have hdescent : baseEnd_5088302 < baseStart_5088302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088362 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_5088362 : Nat := 118140960795 + 5088362 * 2 ^ 59
def prefixEnd_5088362 : Nat := 4983230072969 + 3 ^ 40 * 5088362 * 2
def baseEnd_5088362 : Nat := 290308383341458443774895

theorem tailTrace_5088362 : CollatzResearch.WordTrace tailWord_5088362 prefixEnd_5088362 290308383341458443774895 := by
  unfold tailWord_5088362
  simp only [CollatzResearch.WordTrace]
  refine ⟨46396952197935242972062835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123725205861160647925500893 46396952197935242972062835)
  ·
    refine ⟨69595428296902864458094253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46396952197935242972062835 69595428296902864458094253)
    ·
      refine ⟨26098285611338574171785345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69595428296902864458094253 26098285611338574171785345)
      ·
        refine ⟨19573714208503930628839009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26098285611338574171785345 19573714208503930628839009)
        ·
          refine ⟨14680285656377947971629257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19573714208503930628839009 14680285656377947971629257)
          ·
            refine ⟨11010214242283460978721943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14680285656377947971629257 11010214242283460978721943)
            ·
              refine ⟨16515321363425191468082915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010214242283460978721943 16515321363425191468082915)
              ·
                refine ⟨24772982045137787202124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16515321363425191468082915 24772982045137787202124373)
                ·
                  refine ⟨290308383341458443774895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24772982045137787202124373 290308383341458443774895)
                  ·
                    rfl

theorem cell23_5088362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_5088362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088362 prefixEnd_5088362 := by exact prefixLift 5088362
  have htrace : WordTrace (prefixWord ++ tailWord_5088362) baseStart_5088362 baseEnd_5088362 := by
    simpa [prefixWord, tailWord_5088362, baseEnd_5088362] using wordTrace_append hprefix tailTrace_5088362
  have hstable : (prefixWord ++ tailWord_5088362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088362).length < 2 ^ (prefixWord ++ tailWord_5088362).sum := by decide
  have hdescent : baseEnd_5088362 < baseStart_5088362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088366 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5088366 : Nat := 118140960795 + 5088366 * 2 ^ 59
def prefixEnd_5088366 : Nat := 4983230072969 + 3 ^ 40 * 5088366 * 2
def baseEnd_5088366 : Nat := 870925834665247992774679

theorem tailTrace_5088366 : CollatzResearch.WordTrace tailWord_5088366 prefixEnd_5088366 870925834665247992774679 := by
  unfold tailWord_5088366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198494335465810071424619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123725303122484320380931301 23198494335465810071424619)
  ·
    refine ⟨34797741503198715107136929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198494335465810071424619 34797741503198715107136929)
    ·
      refine ⟨26098306127399036330352697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34797741503198715107136929 26098306127399036330352697)
      ·
        refine ⟨19573729595549277247764523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26098306127399036330352697 19573729595549277247764523)
        ·
          refine ⟨29360594393323915871646785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19573729595549277247764523 29360594393323915871646785)
          ·
            refine ⟨22020445794992936903735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29360594393323915871646785 22020445794992936903735089)
            ·
              refine ⟨16515334346244702677801317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22020445794992936903735089 16515334346244702677801317)
              ·
                refine ⟨3096625189920881752087747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16515334346244702677801317 3096625189920881752087747)
                ·
                  refine ⟨4644937784881322628131621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096625189920881752087747 4644937784881322628131621)
                  ·
                    refine ⟨870925834665247992774679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644937784881322628131621 870925834665247992774679)
                    ·
                      rfl

theorem cell23_5088366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5088366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088366 prefixEnd_5088366 := by exact prefixLift 5088366
  have htrace : WordTrace (prefixWord ++ tailWord_5088366) baseStart_5088366 baseEnd_5088366 := by
    simpa [prefixWord, tailWord_5088366, baseEnd_5088366] using wordTrace_append hprefix tailTrace_5088366
  have hstable : (prefixWord ++ tailWord_5088366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088366).length < 2 ^ (prefixWord ++ tailWord_5088366).sum := by decide
  have hdescent : baseEnd_5088366 < baseStart_5088366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088395 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_5088395 : Nat := 118140960795 + 5088395 * 2 ^ 59
def prefixEnd_5088395 : Nat := 4983230072969 + 3 ^ 40 * 5088395 * 2
def baseEnd_5088395 : Nat := 2612792394934724364861403

theorem tailTrace_5088395 : CollatzResearch.WordTrace tailWord_5088395 prefixEnd_5088395 2612792394934724364861403 := by
  unfold tailWord_5088395
  simp only [CollatzResearch.WordTrace]
  refine ⟨185589012400621418524202639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123726008267080945682801759 185589012400621418524202639)
  ·
    refine ⟨278383518600932127786303959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185589012400621418524202639 278383518600932127786303959)
    ·
      refine ⟨417575277901398191679455939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278383518600932127786303959 417575277901398191679455939)
      ·
        refine ⟨626362916852097287519183909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417575277901398191679455939 626362916852097287519183909)
        ·
          refine ⟨117443046909768241409846983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 626362916852097287519183909 117443046909768241409846983)
          ·
            refine ⟨176164570364652362114770475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117443046909768241409846983 176164570364652362114770475)
            ·
              refine ⟨264246855546978543172155713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176164570364652362114770475 264246855546978543172155713)
              ·
                refine ⟨198185141660233907379116785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264246855546978543172155713 198185141660233907379116785)
                ·
                  refine ⟨148638856245175430534337589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198185141660233907379116785 148638856245175430534337589)
                  ·
                    refine ⟨13934892772985196612594149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148638856245175430534337589 13934892772985196612594149)
                    ·
                      refine ⟨2612792394934724364861403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13934892772985196612594149 2612792394934724364861403)
                      ·
                        rfl

theorem cell23_5088395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_5088395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088395 prefixEnd_5088395 := by exact prefixLift 5088395
  have htrace : WordTrace (prefixWord ++ tailWord_5088395) baseStart_5088395 baseEnd_5088395 := by
    simpa [prefixWord, tailWord_5088395, baseEnd_5088395] using wordTrace_append hprefix tailTrace_5088395
  have hstable : (prefixWord ++ tailWord_5088395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088395).length < 2 ^ (prefixWord ++ tailWord_5088395).sum := by decide
  have hdescent : baseEnd_5088395 < baseStart_5088395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088423 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5088423 : Nat := 118140960795 + 5088423 * 2 ^ 59
def prefixEnd_5088423 : Nat := 4983230072969 + 3 ^ 40 * 5088423 * 2
def baseEnd_5088423 : Nat := 2612806772393050255311275

theorem tailTrace_5088423 : CollatzResearch.WordTrace tailWord_5088423 prefixEnd_5088423 2612806772393050255311275 := by
  unfold tailWord_5088423
  simp only [CollatzResearch.WordTrace]
  refine ⟨185590033644519979306221923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123726689096346652870814615 185590033644519979306221923)
  ·
    refine ⟨278385050466779968959332885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185590033644519979306221923 278385050466779968959332885)
    ·
      refine ⟨13049299240630311044968729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 278385050466779968959332885 13049299240630311044968729)
      ·
        refine ⟨9786974430472733283726547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13049299240630311044968729 9786974430472733283726547)
        ·
          refine ⟨14680461645709099925589821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9786974430472733283726547 14680461645709099925589821)
          ·
            refine ⟨5505173117140912472096183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14680461645709099925589821 5505173117140912472096183)
            ·
              refine ⟨8257759675711368708144275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505173117140912472096183 8257759675711368708144275)
              ·
                refine ⟨12386639513567053062216413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8257759675711368708144275 12386639513567053062216413)
                ·
                  refine ⟨4644989817587644898331155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12386639513567053062216413 4644989817587644898331155)
                  ·
                    refine ⟨6967484726381467347496733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644989817587644898331155 6967484726381467347496733)
                    ·
                      refine ⟨2612806772393050255311275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967484726381467347496733 2612806772393050255311275)
                      ·
                        rfl

theorem cell23_5088423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5088423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088423 prefixEnd_5088423 := by exact prefixLift 5088423
  have htrace : WordTrace (prefixWord ++ tailWord_5088423) baseStart_5088423 baseEnd_5088423 := by
    simpa [prefixWord, tailWord_5088423, baseEnd_5088423] using wordTrace_append hprefix tailTrace_5088423
  have hstable : (prefixWord ++ tailWord_5088423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088423).length < 2 ^ (prefixWord ++ tailWord_5088423).sum := by decide
  have hdescent : baseEnd_5088423 < baseStart_5088423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088432 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_5088432 : Nat := 118140960795 + 5088432 * 2 ^ 59
def prefixEnd_5088432 : Nat := 4983230072969 + 3 ^ 40 * 5088432 * 2
def baseEnd_5088432 : Nat := 2612811393718940720098733

theorem tailTrace_5088432 : CollatzResearch.WordTrace tailWord_5088432 prefixEnd_5088432 2612811393718940720098733 := by
  unfold tailWord_5088432
  simp only [CollatzResearch.WordTrace]
  refine ⟨92795180950743686921649775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123726907934324915895533033 92795180950743686921649775)
  ·
    refine ⟨139192771426115530382474663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92795180950743686921649775 139192771426115530382474663)
    ·
      refine ⟨208789157139173295573711995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139192771426115530382474663 208789157139173295573711995)
      ·
        refine ⟨313183735708759943360567993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208789157139173295573711995 313183735708759943360567993)
        ·
          refine ⟨234887801781569957520425995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313183735708759943360567993 234887801781569957520425995)
          ·
            refine ⟨352331702672354936280638993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234887801781569957520425995 352331702672354936280638993)
            ·
              refine ⟨264248777004266202210479245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352331702672354936280638993 264248777004266202210479245)
              ·
                refine ⟨99093291376599825828929717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264248777004266202210479245 99093291376599825828929717)
                ·
                  refine ⟨9289996066556233671462161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99093291376599825828929717 9289996066556233671462161)
                  ·
                    refine ⟨6967497049917175253596621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9289996066556233671462161 6967497049917175253596621)
                    ·
                      refine ⟨2612811393718940720098733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967497049917175253596621 2612811393718940720098733)
                      ·
                        rfl

theorem cell23_5088432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_5088432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088432 prefixEnd_5088432 := by exact prefixLift 5088432
  have htrace : WordTrace (prefixWord ++ tailWord_5088432) baseStart_5088432 baseEnd_5088432 := by
    simpa [prefixWord, tailWord_5088432, baseEnd_5088432] using wordTrace_append hprefix tailTrace_5088432
  have hstable : (prefixWord ++ tailWord_5088432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088432).length < 2 ^ (prefixWord ++ tailWord_5088432).sum := by decide
  have hdescent : baseEnd_5088432 < baseStart_5088432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088435 : List Nat := [1, 1, 1, 2, 3, 2, 3, 10]
def baseStart_5088435 : Nat := 118140960795 + 5088435 * 2 ^ 59
def prefixEnd_5088435 : Nat := 4983230072969 + 3 ^ 40 * 5088435 * 2
def baseEnd_5088435 : Nat := 96770849413366822531897

theorem tailTrace_5088435 : CollatzResearch.WordTrace tailWord_5088435 prefixEnd_5088435 96770849413366822531897 := by
  unfold tailWord_5088435
  simp only [CollatzResearch.WordTrace]
  refine ⟨185590471320476505355658759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123726980880317670237105839 185590471320476505355658759)
  ·
    refine ⟨278385706980714758033488139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185590471320476505355658759 278385706980714758033488139)
    ·
      refine ⟨417578560471072137050232209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278385706980714758033488139 417578560471072137050232209)
      ·
        refine ⟨313183920353304102787674157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417578560471072137050232209 313183920353304102787674157)
        ·
          refine ⟨117443970132489038545377809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313183920353304102787674157 117443970132489038545377809)
          ·
            refine ⟨88082977599366778909033357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117443970132489038545377809 88082977599366778909033357)
            ·
              refine ⟨33031116599762542090887509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88082977599366778909033357 33031116599762542090887509)
              ·
                refine ⟨96770849413366822531897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33031116599762542090887509 96770849413366822531897)
                ·
                  rfl

theorem cell23_5088435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 10].length) (baseStart_5088435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088435 prefixEnd_5088435 := by exact prefixLift 5088435
  have htrace : WordTrace (prefixWord ++ tailWord_5088435) baseStart_5088435 baseEnd_5088435 := by
    simpa [prefixWord, tailWord_5088435, baseEnd_5088435] using wordTrace_append hprefix tailTrace_5088435
  have hstable : (prefixWord ++ tailWord_5088435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088435).length < 2 ^ (prefixWord ++ tailWord_5088435).sum := by decide
  have hdescent : baseEnd_5088435 < baseStart_5088435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088439 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 2, 4]
def baseStart_5088439 : Nat := 118140960795 + 5088439 * 2 ^ 59
def prefixEnd_5088439 : Nat := 4983230072969 + 3 ^ 40 * 5088439 * 2
def baseEnd_5088439 : Nat := 870938329361174064237067

theorem tailTrace_5088439 : CollatzResearch.WordTrace tailWord_5088439 prefixEnd_5088439 870938329361174064237067 := by
  unfold tailWord_5088439
  simp only [CollatzResearch.WordTrace]
  refine ⟨185590617212462014038804371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123727078141641342692536247 185590617212462014038804371)
  ·
    refine ⟨278385925818693021058206557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185590617212462014038804371 278385925818693021058206557)
    ·
      refine ⟨104394722182009882896827459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278385925818693021058206557 104394722182009882896827459)
      ·
        refine ⟨156592083273014824345241189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104394722182009882896827459 156592083273014824345241189)
        ·
          refine ⟨29361015613690279564732723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156592083273014824345241189 29361015613690279564732723)
          ·
            refine ⟨44041523420535419347099085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29361015613690279564732723 44041523420535419347099085)
            ·
              refine ⟨16515571282700782255162157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44041523420535419347099085 16515571282700782255162157)
              ·
                refine ⟨6193339231012793345685809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16515571282700782255162157 6193339231012793345685809)
                ·
                  refine ⟨4645004423259595009264357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193339231012793345685809 4645004423259595009264357)
                  ·
                    refine ⟨870938329361174064237067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645004423259595009264357 870938329361174064237067)
                    ·
                      rfl

theorem cell23_5088439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_5088439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088439 prefixEnd_5088439 := by exact prefixLift 5088439
  have htrace : WordTrace (prefixWord ++ tailWord_5088439) baseStart_5088439 baseEnd_5088439 := by
    simpa [prefixWord, tailWord_5088439, baseEnd_5088439] using wordTrace_append hprefix tailTrace_5088439
  have hstable : (prefixWord ++ tailWord_5088439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088439).length < 2 ^ (prefixWord ++ tailWord_5088439).sum := by decide
  have hdescent : baseEnd_5088439 < baseStart_5088439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088442 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_5088442 : Nat := 118140960795 + 5088442 * 2 ^ 59
def prefixEnd_5088442 : Nat := 4983230072969 + 3 ^ 40 * 5088442 * 2
def baseEnd_5088442 : Nat := 2612816528525485680973687

theorem tailTrace_5088442 : CollatzResearch.WordTrace tailWord_5088442 prefixEnd_5088442 2612816528525485680973687 := by
  unfold tailWord_5088442
  simp only [CollatzResearch.WordTrace]
  refine ⟨46397681657862786387790895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123727151087634097034109053 46397681657862786387790895)
  ·
    refine ⟨69596522486794179581686343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46397681657862786387790895 69596522486794179581686343)
    ·
      refine ⟨104394783730191269372529515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69596522486794179581686343 104394783730191269372529515)
      ·
        refine ⟨156592175595286904058794273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104394783730191269372529515 156592175595286904058794273)
        ·
          refine ⟨117444131696465178044095705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156592175595286904058794273 117444131696465178044095705)
          ·
            refine ⟨88083098772348883533071779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117444131696465178044095705 88083098772348883533071779)
            ·
              refine ⟨132124648158523325299607669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88083098772348883533071779 132124648158523325299607669)
              ·
                refine ⟨12386685764861561746838219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132124648158523325299607669 12386685764861561746838219)
                ·
                  refine ⟨18580028647292342620257329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12386685764861561746838219 18580028647292342620257329)
                  ·
                    refine ⟨13935021485469256965192997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18580028647292342620257329 13935021485469256965192997)
                    ·
                      refine ⟨2612816528525485680973687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13935021485469256965192997 2612816528525485680973687)
                      ·
                        rfl

theorem cell23_5088442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_5088442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088442 prefixEnd_5088442 := by exact prefixLift 5088442
  have htrace : WordTrace (prefixWord ++ tailWord_5088442) baseStart_5088442 baseEnd_5088442 := by
    simpa [prefixWord, tailWord_5088442, baseEnd_5088442] using wordTrace_append hprefix tailTrace_5088442
  have hstable : (prefixWord ++ tailWord_5088442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088442).length < 2 ^ (prefixWord ++ tailWord_5088442).sum := by decide
  have hdescent : baseEnd_5088442 < baseStart_5088442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088446 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_5088446 : Nat := 118140960795 + 5088446 * 2 ^ 59
def prefixEnd_5088446 : Nat := 4983230072969 + 3 ^ 40 * 5088446 * 2
def baseEnd_5088446 : Nat := 2612818582448103665323669

theorem tailTrace_5088446 : CollatzResearch.WordTrace tailWord_5088446 prefixEnd_5088446 2612818582448103665323669 := by
  unfold tailWord_5088446
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198859065429581779288649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123727248348957769489539461 23198859065429581779288649)
  ·
    refine ⟨17399144299072186334466487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23198859065429581779288649 17399144299072186334466487)
    ·
      refine ⟨26098716448608279501699731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17399144299072186334466487 26098716448608279501699731)
      ·
        refine ⟨39148074672912419252549597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26098716448608279501699731 39148074672912419252549597)
        ·
          refine ⟨14680528002342157219706099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39148074672912419252549597 14680528002342157219706099)
          ·
            refine ⟨22020792003513235829559149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14680528002342157219706099 22020792003513235829559149)
            ·
              refine ⟨8257797001317463436084681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22020792003513235829559149 8257797001317463436084681)
              ·
                refine ⟨6193347750988097577063511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8257797001317463436084681 6193347750988097577063511)
                ·
                  refine ⟨9290021626482146365595267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193347750988097577063511 9290021626482146365595267)
                  ·
                    refine ⟨13935032439723219548392901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9290021626482146365595267 13935032439723219548392901)
                    ·
                      refine ⟨2612818582448103665323669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13935032439723219548392901 2612818582448103665323669)
                      ·
                        rfl

theorem cell23_5088446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_5088446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088446 prefixEnd_5088446 := by exact prefixLift 5088446
  have htrace : WordTrace (prefixWord ++ tailWord_5088446) baseStart_5088446 baseEnd_5088446 := by
    simpa [prefixWord, tailWord_5088446, baseEnd_5088446] using wordTrace_append hprefix tailTrace_5088446
  have hstable : (prefixWord ++ tailWord_5088446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088446).length < 2 ^ (prefixWord ++ tailWord_5088446).sum := by decide
  have hdescent : baseEnd_5088446 < baseStart_5088446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088479 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_5088479 : Nat := 118140960795 + 5088479 * 2 ^ 59
def prefixEnd_5088479 : Nat := 4983230072969 + 3 ^ 40 * 5088479 * 2
def baseEnd_5088479 : Nat := 2612835527309702036211017

theorem tailTrace_5088479 : CollatzResearch.WordTrace tailWord_5088479 prefixEnd_5088479 2612835527309702036211017 := by
  unfold tailWord_5088479
  simp only [CollatzResearch.WordTrace]
  refine ⟨185592076132317100870260491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123728050754878067246840327 185592076132317100870260491)
  ·
    refine ⟨278388114198475651305390737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185592076132317100870260491 278388114198475651305390737)
    ·
      refine ⟨208791085648856738479043053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278388114198475651305390737 208791085648856738479043053)
      ·
        refine ⟨78296657118321276929641145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208791085648856738479043053 78296657118321276929641145)
        ·
          refine ⟨58722492838740957697230859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78296657118321276929641145 58722492838740957697230859)
          ·
            refine ⟨88083739258111436545846289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58722492838740957697230859 88083739258111436545846289)
            ·
              refine ⟨66062804443583577409384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88083739258111436545846289 66062804443583577409384717)
              ·
                refine ⟨24773551666343841528519269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66062804443583577409384717 24773551666343841528519269)
                ·
                  refine ⟨4645040937439470286597363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24773551666343841528519269 4645040937439470286597363)
                  ·
                    refine ⟨6967561406159205429896045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645040937439470286597363 6967561406159205429896045)
                    ·
                      refine ⟨2612835527309702036211017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967561406159205429896045 2612835527309702036211017)
                      ·
                        rfl

theorem cell23_5088479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_5088479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088479 prefixEnd_5088479 := by exact prefixLift 5088479
  have htrace : WordTrace (prefixWord ++ tailWord_5088479) baseStart_5088479 baseEnd_5088479 := by
    simpa [prefixWord, tailWord_5088479, baseEnd_5088479] using wordTrace_append hprefix tailTrace_5088479
  have hstable : (prefixWord ++ tailWord_5088479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088479).length < 2 ^ (prefixWord ++ tailWord_5088479).sum := by decide
  have hdescent : baseEnd_5088479 < baseStart_5088479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088480 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 1, 2, 2]
def baseStart_5088480 : Nat := 118140960795 + 5088480 * 2 ^ 59
def prefixEnd_5088480 : Nat := 4983230072969 + 3 ^ 40 * 5088480 * 2
def baseEnd_5088480 : Nat := 2612836040790356532298513

theorem tailTrace_5088480 : CollatzResearch.WordTrace tailWord_5088480 prefixEnd_5088480 2612836040790356532298513 := by
  unfold tailWord_5088480
  simp only [CollatzResearch.WordTrace]
  refine ⟨92796056302656739020523447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123728075070208985360697929 92796056302656739020523447)
  ·
    refine ⟨139194084453985108530785171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92796056302656739020523447 139194084453985108530785171)
    ·
      refine ⟨208791126680977662796177757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139194084453985108530785171 208791126680977662796177757)
      ·
        refine ⟨78296672505366623548566659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208791126680977662796177757 78296672505366623548566659)
        ·
          refine ⟨117445008758049935322849989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78296672505366623548566659 117445008758049935322849989)
          ·
            refine ⟨22020939142134362873034373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117445008758049935322849989 22020939142134362873034373)
            ·
              refine ⟨4128926089150193038693945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22020939142134362873034373 4128926089150193038693945)
              ·
                refine ⟨3096694566862644779020459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128926089150193038693945 3096694566862644779020459)
                ·
                  refine ⟨4645041850293967168530689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096694566862644779020459 4645041850293967168530689)
                  ·
                    refine ⟨3483781387720475376398017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4645041850293967168530689 3483781387720475376398017)
                    ·
                      refine ⟨2612836040790356532298513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483781387720475376398017 2612836040790356532298513)
                      ·
                        rfl

theorem cell23_5088480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_5088480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088480 prefixEnd_5088480 := by exact prefixLift 5088480
  have htrace : WordTrace (prefixWord ++ tailWord_5088480) baseStart_5088480 baseEnd_5088480 := by
    simpa [prefixWord, tailWord_5088480, baseEnd_5088480] using wordTrace_append hprefix tailTrace_5088480
  have hstable : (prefixWord ++ tailWord_5088480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088480).length < 2 ^ (prefixWord ++ tailWord_5088480).sum := by decide
  have hdescent : baseEnd_5088480 < baseStart_5088480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088506 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_5088506 : Nat := 118140960795 + 5088506 * 2 ^ 59
def prefixEnd_5088506 : Nat := 4983230072969 + 3 ^ 40 * 5088506 * 2
def baseEnd_5088506 : Nat := 2612849391287373430573393

theorem tailTrace_5088506 : CollatzResearch.WordTrace tailWord_5088506 prefixEnd_5088506 2612849391287373430573393 := by
  unfold tailWord_5088506
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398265225804821120373343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123728707268812856320995581 46398265225804821120373343)
  ·
    refine ⟨69597397838707231680560015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46398265225804821120373343 69597397838707231680560015)
    ·
      refine ⟨104396096758060847520840023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69597397838707231680560015 104396096758060847520840023)
      ·
        refine ⟨156594145137091271281260035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104396096758060847520840023 156594145137091271281260035)
        ·
          refine ⟨234891217705636906921890053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156594145137091271281260035 234891217705636906921890053)
          ·
            refine ⟨44042103319806920047854385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234891217705636906921890053 44042103319806920047854385)
            ·
              refine ⟨33031577489855190035890789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44042103319806920047854385 33031577489855190035890789)
              ·
                refine ⟨6193420779347848131729523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33031577489855190035890789 6193420779347848131729523)
                ·
                  refine ⟨9290131169021772197594285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193420779347848131729523 9290131169021772197594285)
                  ·
                    refine ⟨3483799188383164574097857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9290131169021772197594285 3483799188383164574097857)
                    ·
                      refine ⟨2612849391287373430573393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483799188383164574097857 2612849391287373430573393)
                      ·
                        rfl

theorem cell23_5088506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_5088506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088506 prefixEnd_5088506 := by exact prefixLift 5088506
  have htrace : WordTrace (prefixWord ++ tailWord_5088506) baseStart_5088506 baseEnd_5088506 := by
    simpa [prefixWord, tailWord_5088506, baseEnd_5088506] using wordTrace_append hprefix tailTrace_5088506
  have hstable : (prefixWord ++ tailWord_5088506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088506).length < 2 ^ (prefixWord ++ tailWord_5088506).sum := by decide
  have hdescent : baseEnd_5088506 < baseStart_5088506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088522 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5088522 : Nat := 118140960795 + 5088522 * 2 ^ 59
def prefixEnd_5088522 : Nat := 4983230072969 + 3 ^ 40 * 5088522 * 2
def baseEnd_5088522 : Nat := 2612857606977845367973319

theorem tailTrace_5088522 : CollatzResearch.WordTrace tailWord_5088522 prefixEnd_5088522 2612857606977845367973319 := by
  unfold tailWord_5088522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398411117790329803518955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123729096314107546142717213 46398411117790329803518955)
  ·
    refine ⟨69597616676685494705278433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46398411117790329803518955 69597616676685494705278433)
    ·
      refine ⟨52198212507514121028958825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69597616676685494705278433 52198212507514121028958825)
      ·
        refine ⟨39148659380635590771719119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52198212507514121028958825 39148659380635590771719119)
        ·
          refine ⟨58722989070953386157578679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39148659380635590771719119 58722989070953386157578679)
          ·
            refine ⟨88084483606430079236368019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58722989070953386157578679 88084483606430079236368019)
            ·
              refine ⟨132126725409645118854552029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88084483606430079236368019 132126725409645118854552029)
              ·
                refine ⟨49547522028616919570457011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132126725409645118854552029 49547522028616919570457011)
                ·
                  refine ⟨74321283042925379355685517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49547522028616919570457011 74321283042925379355685517)
                  ·
                    refine ⟨27870481141097017258382069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74321283042925379355685517 27870481141097017258382069)
                    ·
                      refine ⟨2612857606977845367973319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27870481141097017258382069 2612857606977845367973319)
                      ·
                        rfl

theorem cell23_5088522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5088522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088522 prefixEnd_5088522 := by exact prefixLift 5088522
  have htrace : WordTrace (prefixWord ++ tailWord_5088522) baseStart_5088522 baseEnd_5088522 := by
    simpa [prefixWord, tailWord_5088522, baseEnd_5088522] using wordTrace_append hprefix tailTrace_5088522
  have hstable : (prefixWord ++ tailWord_5088522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088522).length < 2 ^ (prefixWord ++ tailWord_5088522).sum := by decide
  have hdescent : baseEnd_5088522 < baseStart_5088522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088523 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 1, 3, 2]
def baseStart_5088523 : Nat := 118140960795 + 5088523 * 2 ^ 59
def prefixEnd_5088523 : Nat := 4983230072969 + 3 ^ 40 * 5088523 * 2
def baseEnd_5088523 : Nat := 2612858120458499864060815

theorem tailTrace_5088523 : CollatzResearch.WordTrace tailWord_5088523 prefixEnd_5088523 2612858120458499864060815 := by
  unfold tailWord_5088523
  simp only [CollatzResearch.WordTrace]
  refine ⟨185593680944157696384862223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123729120629438464256574815 185593680944157696384862223)
  ·
    refine ⟨278390521416236544577293335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185593680944157696384862223 278390521416236544577293335)
    ·
      refine ⟨417585782124354816865940003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278390521416236544577293335 417585782124354816865940003)
      ·
        refine ⟨626378673186532225298910005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417585782124354816865940003 626378673186532225298910005)
        ·
          refine ⟨58723000611237396121772813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 626378673186532225298910005 58723000611237396121772813)
          ·
            refine ⟨22021125229214023545664805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58723000611237396121772813 22021125229214023545664805)
            ·
              refine ⟨4128960980477629414812151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22021125229214023545664805 4128960980477629414812151)
              ·
                refine ⟨6193441470716444122218227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128960980477629414812151 6193441470716444122218227)
                ·
                  refine ⟨9290162206074666183327341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193441470716444122218227 9290162206074666183327341)
                  ·
                    refine ⟨3483810827277999818747753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9290162206074666183327341 3483810827277999818747753)
                    ·
                      refine ⟨2612858120458499864060815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483810827277999818747753 2612858120458499864060815)
                      ·
                        rfl

theorem cell23_5088523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 3, 2].length) (baseStart_5088523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088523 prefixEnd_5088523 := by exact prefixLift 5088523
  have htrace : WordTrace (prefixWord ++ tailWord_5088523) baseStart_5088523 baseEnd_5088523 := by
    simpa [prefixWord, tailWord_5088523, baseEnd_5088523] using wordTrace_append hprefix tailTrace_5088523
  have hstable : (prefixWord ++ tailWord_5088523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088523).length < 2 ^ (prefixWord ++ tailWord_5088523).sum := by decide
  have hdescent : baseEnd_5088523 < baseStart_5088523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088530 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5088530 : Nat := 118140960795 + 5088530 * 2 ^ 59
def prefixEnd_5088530 : Nat := 4983230072969 + 3 ^ 40 * 5088530 * 2
def baseEnd_5088530 : Nat := 2612861714823081336673283

theorem tailTrace_5088530 : CollatzResearch.WordTrace tailWord_5088530 prefixEnd_5088530 2612861714823081336673283 := by
  unfold tailWord_5088530
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398484063783084145091761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123729290836754891053578029 46398484063783084145091761)
  ·
    refine ⟨34798863047837313108818821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46398484063783084145091761 34798863047837313108818821)
    ·
      refine ⟨6524786821469496207903529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34798863047837313108818821 6524786821469496207903529)
      ·
        refine ⟨4893590116102122155927647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524786821469496207903529 4893590116102122155927647)
        ·
          refine ⟨7340385174153183233891471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893590116102122155927647 7340385174153183233891471)
          ·
            refine ⟨11010577761229774850837207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340385174153183233891471 11010577761229774850837207)
            ·
              refine ⟨16515866641844662276255811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010577761229774850837207 16515866641844662276255811)
              ·
                refine ⟨24773799962766993414383717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16515866641844662276255811 24773799962766993414383717)
                ·
                  refine ⟨4645087493018811265196947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24773799962766993414383717 4645087493018811265196947)
                  ·
                    refine ⟨6967631239528216897795421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645087493018811265196947 6967631239528216897795421)
                    ·
                      refine ⟨2612861714823081336673283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967631239528216897795421 2612861714823081336673283)
                      ·
                        rfl

theorem cell23_5088530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5088530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088530 prefixEnd_5088530 := by exact prefixLift 5088530
  have htrace : WordTrace (prefixWord ++ tailWord_5088530) baseStart_5088530 baseEnd_5088530 := by
    simpa [prefixWord, tailWord_5088530, baseEnd_5088530] using wordTrace_append hprefix tailTrace_5088530
  have hstable : (prefixWord ++ tailWord_5088530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088530).length < 2 ^ (prefixWord ++ tailWord_5088530).sum := by decide
  have hdescent : baseEnd_5088530 < baseStart_5088530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088549 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_5088549 : Nat := 118140960795 + 5088549 * 2 ^ 59
def prefixEnd_5088549 : Nat := 4983230072969 + 3 ^ 40 * 5088549 * 2
def baseEnd_5088549 : Nat := 2612871470955516762335695

theorem tailTrace_5088549 : CollatzResearch.WordTrace tailWord_5088549 prefixEnd_5088549 2612871470955516762335695 := by
  unfold tailWord_5088549
  simp only [CollatzResearch.WordTrace]
  refine ⟨185594629242063502825308701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123729752828042335216872467 185594629242063502825308701)
  ·
    refine ⟨69597985965773813559490763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185594629242063502825308701 69597985965773813559490763)
    ·
      refine ⟨104396978948660720339236145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69597985965773813559490763 104396978948660720339236145)
      ·
        refine ⟨78297734211495540254427109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104396978948660720339236145 78297734211495540254427109)
        ·
          refine ⟨14680825164655413797705083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78297734211495540254427109 14680825164655413797705083)
          ·
            refine ⟨22021237746983120696557625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14680825164655413797705083 22021237746983120696557625)
            ·
              refine ⟨16515928310237340522418219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22021237746983120696557625 16515928310237340522418219)
              ·
                refine ⟨24773892465356010783627329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16515928310237340522418219 24773892465356010783627329)
                ·
                  refine ⟨18580419349017008087720497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24773892465356010783627329 18580419349017008087720497)
                  ·
                    refine ⟨13935314511762756065790373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18580419349017008087720497 13935314511762756065790373)
                    ·
                      refine ⟨2612871470955516762335695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13935314511762756065790373 2612871470955516762335695)
                      ·
                        rfl

theorem cell23_5088549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_5088549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088549 prefixEnd_5088549 := by exact prefixLift 5088549
  have htrace : WordTrace (prefixWord ++ tailWord_5088549) baseStart_5088549 baseEnd_5088549 := by
    simpa [prefixWord, tailWord_5088549, baseEnd_5088549] using wordTrace_append hprefix tailTrace_5088549
  have hstable : (prefixWord ++ tailWord_5088549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088549).length < 2 ^ (prefixWord ++ tailWord_5088549).sum := by decide
  have hdescent : baseEnd_5088549 < baseStart_5088549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088579 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 7, 2]
def baseStart_5088579 : Nat := 118140960795 + 5088579 * 2 ^ 59
def prefixEnd_5088579 : Nat := 4983230072969 + 3 ^ 40 * 5088579 * 2
def baseEnd_5088579 : Nat := 2612886875375151644960557

theorem tailTrace_5088579 : CollatzResearch.WordTrace tailWord_5088579 prefixEnd_5088579 2612886875375151644960557 := by
  unfold tailWord_5088579
  simp only [CollatzResearch.WordTrace]
  refine ⟨185595723431954817948900791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123730482287969878632600527 185595723431954817948900791)
  ·
    refine ⟨278393585147932226923351187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185595723431954817948900791 278393585147932226923351187)
    ·
      refine ⟨417590377721898340385026781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278393585147932226923351187 417590377721898340385026781)
      ·
        refine ⟨156596391645711877644385043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417590377721898340385026781 156596391645711877644385043)
        ·
          refine ⟨234894587468567816466577565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156596391645711877644385043 234894587468567816466577565)
          ·
            refine ⟨88085470300712931174966587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234894587468567816466577565 88085470300712931174966587)
            ·
              refine ⟨132128205451069396762449881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88085470300712931174966587 132128205451069396762449881)
              ·
                refine ⟨99096154088302047571837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132128205451069396762449881 99096154088302047571837411)
                ·
                  refine ⟨148644231132453071357756117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99096154088302047571837411 148644231132453071357756117)
                  ·
                    refine ⟨3483849167166868859947409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148644231132453071357756117 3483849167166868859947409)
                    ·
                      refine ⟨2612886875375151644960557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483849167166868859947409 2612886875375151644960557)
                      ·
                        rfl

theorem cell23_5088579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_5088579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088579 prefixEnd_5088579 := by exact prefixLift 5088579
  have htrace : WordTrace (prefixWord ++ tailWord_5088579) baseStart_5088579 baseEnd_5088579 := by
    simpa [prefixWord, tailWord_5088579, baseEnd_5088579] using wordTrace_append hprefix tailTrace_5088579
  have hstable : (prefixWord ++ tailWord_5088579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088579).length < 2 ^ (prefixWord ++ tailWord_5088579).sum := by decide
  have hdescent : baseEnd_5088579 < baseStart_5088579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088596 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_5088596 : Nat := 118140960795 + 5088596 * 2 ^ 59
def prefixEnd_5088596 : Nat := 4983230072969 + 3 ^ 40 * 5088596 * 2
def baseEnd_5088596 : Nat := 2612895604546278078447979

theorem tailTrace_5088596 : CollatzResearch.WordTrace tailWord_5088596 prefixEnd_5088596 2612895604546278078447979 := by
  unfold tailWord_5088596
  simp only [CollatzResearch.WordTrace]
  refine ⟨92798171736446614926134821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123730895648595486568179761 92798171736446614926134821)
  ·
    refine ⟨17399657200583740298650279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92798171736446614926134821 17399657200583740298650279)
    ·
      refine ⟨26099485800875610447975419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17399657200583740298650279 26099485800875610447975419)
      ·
        refine ⟨39149228701313415671963129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26099485800875610447975419 39149228701313415671963129)
        ·
          refine ⟨29361921525985061753972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39149228701313415671963129 29361921525985061753972347)
          ·
            refine ⟨44042882288977592630958521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29361921525985061753972347 44042882288977592630958521)
            ·
              refine ⟨33032161716733194473218891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44042882288977592630958521 33032161716733194473218891)
              ·
                refine ⟨49548242575099791709828337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33032161716733194473218891 49548242575099791709828337)
                ·
                  refine ⟨37161181931324843782371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49548242575099791709828337 37161181931324843782371253)
                  ·
                    refine ⟨3483860806061704104597305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37161181931324843782371253 3483860806061704104597305)
                    ·
                      refine ⟨2612895604546278078447979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3483860806061704104597305 2612895604546278078447979)
                      ·
                        rfl

theorem cell23_5088596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_5088596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088596 prefixEnd_5088596 := by exact prefixLift 5088596
  have htrace : WordTrace (prefixWord ++ tailWord_5088596) baseStart_5088596 baseEnd_5088596 := by
    simpa [prefixWord, tailWord_5088596, baseEnd_5088596] using wordTrace_append hprefix tailTrace_5088596
  have hstable : (prefixWord ++ tailWord_5088596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088596).length < 2 ^ (prefixWord ++ tailWord_5088596).sum := by decide
  have hdescent : baseEnd_5088596 < baseStart_5088596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088598 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5088598 : Nat := 118140960795 + 5088598 * 2 ^ 59
def prefixEnd_5088598 : Nat := 4983230072969 + 3 ^ 40 * 5088598 * 2
def baseEnd_5088598 : Nat := 2612896631507587070622971

theorem tailTrace_5088598 : CollatzResearch.WordTrace tailWord_5088598 prefixEnd_5088598 2612896631507587070622971 := by
  unfold tailWord_5088598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599776026180374012115153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123730944279257322795894965 11599776026180374012115153)
  ·
    refine ⟨8699832019635280509086365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11599776026180374012115153 8699832019635280509086365)
    ·
      refine ⟨3262437007363230190907387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8699832019635280509086365 3262437007363230190907387)
      ·
        refine ⟨4893655511044845286361081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262437007363230190907387 4893655511044845286361081)
        ·
          refine ⟨3670241633283633964770811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893655511044845286361081 3670241633283633964770811)
          ·
            refine ⟨5505362449925450947156217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670241633283633964770811 5505362449925450947156217)
            ·
              refine ⟨4129021837444088210367163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5505362449925450947156217 4129021837444088210367163)
              ·
                refine ⟨6193532756166132315550745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129021837444088210367163 6193532756166132315550745)
                ·
                  refine ⟨4645149567124599236663059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193532756166132315550745 4645149567124599236663059)
                  ·
                    refine ⟨6967724350686898854994589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645149567124599236663059 6967724350686898854994589)
                    ·
                      refine ⟨2612896631507587070622971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967724350686898854994589 2612896631507587070622971)
                      ·
                        rfl

theorem cell23_5088598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5088598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088598 prefixEnd_5088598 := by exact prefixLift 5088598
  have htrace : WordTrace (prefixWord ++ tailWord_5088598) baseStart_5088598 baseEnd_5088598 := by
    simpa [prefixWord, tailWord_5088598, baseEnd_5088598] using wordTrace_append hprefix tailTrace_5088598
  have hstable : (prefixWord ++ tailWord_5088598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088598).length < 2 ^ (prefixWord ++ tailWord_5088598).sum := by decide
  have hdescent : baseEnd_5088598 < baseStart_5088598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088599 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_5088599 : Nat := 118140960795 + 5088599 * 2 ^ 59
def prefixEnd_5088599 : Nat := 4983230072969 + 3 ^ 40 * 5088599 * 2
def baseEnd_5088599 : Nat := 2612897144988241566710465

theorem tailTrace_5088599 : CollatzResearch.WordTrace tailWord_5088599 prefixEnd_5088599 2612897144988241566710465 := by
  unfold tailWord_5088599
  simp only [CollatzResearch.WordTrace]
  refine ⟨185596452891882361364628851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123730968594588240909752567 185596452891882361364628851)
  ·
    refine ⟨278394679337823542046943277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185596452891882361364628851 278394679337823542046943277)
    ·
      refine ⟨104398004751683828267603729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278394679337823542046943277 104398004751683828267603729)
      ·
        refine ⟨78298503563762871200702797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104398004751683828267603729 78298503563762871200702797)
        ·
          refine ⟨29361938836411076700263549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78298503563762871200702797 29361938836411076700263549)
          ·
            refine ⟨11010727063654153762598831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29361938836411076700263549 11010727063654153762598831)
            ·
              refine ⟨16516090595481230643898247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010727063654153762598831 16516090595481230643898247)
              ·
                refine ⟨24774135893221845965847371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16516090595481230643898247 24774135893221845965847371)
                ·
                  refine ⟨37161203839832768948771057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24774135893221845965847371 37161203839832768948771057)
                  ·
                    refine ⟨27870902879874576711578293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37161203839832768948771057 27870902879874576711578293)
                    ·
                      refine ⟨2612897144988241566710465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27870902879874576711578293 2612897144988241566710465)
                      ·
                        rfl

theorem cell23_5088599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_5088599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088599 prefixEnd_5088599 := by exact prefixLift 5088599
  have htrace : WordTrace (prefixWord ++ tailWord_5088599) baseStart_5088599 baseEnd_5088599 := by
    simpa [prefixWord, tailWord_5088599, baseEnd_5088599] using wordTrace_append hprefix tailTrace_5088599
  have hstable : (prefixWord ++ tailWord_5088599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088599).length < 2 ^ (prefixWord ++ tailWord_5088599).sum := by decide
  have hdescent : baseEnd_5088599 < baseStart_5088599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088626 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5088626 : Nat := 118140960795 + 5088626 * 2 ^ 59
def prefixEnd_5088626 : Nat := 4983230072969 + 3 ^ 40 * 5088626 * 2
def baseEnd_5088626 : Nat := 2612911008965912961072841

theorem tailTrace_5088626 : CollatzResearch.WordTrace tailWord_5088626 prefixEnd_5088626 2612911008965912961072841 := by
  unfold tailWord_5088626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46399359415696136243965433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123731625108523029983907821 46399359415696136243965433)
  ·
    refine ⟨34799519561772102182974075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46399359415696136243965433 34799519561772102182974075)
    ·
      refine ⟨52199279342658153274461113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34799519561772102182974075 52199279342658153274461113)
      ·
        refine ⟨39149459506993614955845835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52199279342658153274461113 39149459506993614955845835)
        ·
          refine ⟨58724189260490422433768753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39149459506993614955845835 58724189260490422433768753)
          ·
            refine ⟨44043141945367816825326565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58724189260490422433768753 44043141945367816825326565)
            ·
              refine ⟨8258089114756465654748731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44043141945367816825326565 8258089114756465654748731)
              ·
                refine ⟨12387133672134698482123097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8258089114756465654748731 12387133672134698482123097)
                ·
                  refine ⟨9290350254101023861592323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12387133672134698482123097 9290350254101023861592323)
                  ·
                    refine ⟨13935525381151535792388485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9290350254101023861592323 13935525381151535792388485)
                    ·
                      refine ⟨2612911008965912961072841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13935525381151535792388485 2612911008965912961072841)
                      ·
                        rfl

theorem cell23_5088626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5088626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088626 prefixEnd_5088626 := by exact prefixLift 5088626
  have htrace : WordTrace (prefixWord ++ tailWord_5088626) baseStart_5088626 baseEnd_5088626 := by
    simpa [prefixWord, tailWord_5088626, baseEnd_5088626] using wordTrace_append hprefix tailTrace_5088626
  have hstable : (prefixWord ++ tailWord_5088626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088626).length < 2 ^ (prefixWord ++ tailWord_5088626).sum := by decide
  have hdescent : baseEnd_5088626 < baseStart_5088626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088670 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5088670 : Nat := 118140960795 + 5088670 * 2 ^ 59
def prefixEnd_5088670 : Nat := 4983230072969 + 3 ^ 40 * 5088670 * 2
def baseEnd_5088670 : Nat := 870977867371570262974213

theorem tailTrace_5088670 : CollatzResearch.WordTrace tailWord_5088670 prefixEnd_5088670 870977867371570262974213 := by
  unfold tailWord_5088670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199880309328142561307933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123732694983083426993642309 23199880309328142561307933)
  ·
    refine ⟨8699955115998053460490475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23199880309328142561307933 8699955115998053460490475)
    ·
      refine ⟨13049932673997080190735713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8699955115998053460490475 13049932673997080190735713)
      ·
        refine ⟨9787449505497810143051785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13049932673997080190735713 9787449505497810143051785)
        ·
          refine ⟨7340587129123357607288839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9787449505497810143051785 7340587129123357607288839)
          ·
            refine ⟨11010880693685036410933259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340587129123357607288839 11010880693685036410933259)
            ·
              refine ⟨16516321040527554616399889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010880693685036410933259 16516321040527554616399889)
              ·
                refine ⟨12387240780395665962299917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16516321040527554616399889 12387240780395665962299917)
                ·
                  refine ⟨4645215292648374735862469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12387240780395665962299917 4645215292648374735862469)
                  ·
                    refine ⟨870977867371570262974213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645215292648374735862469 870977867371570262974213)
                    ·
                      rfl

theorem cell23_5088670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5088670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088670 prefixEnd_5088670 := by exact prefixLift 5088670
  have htrace : WordTrace (prefixWord ++ tailWord_5088670) baseStart_5088670 baseEnd_5088670 := by
    simpa [prefixWord, tailWord_5088670, baseEnd_5088670] using wordTrace_append hprefix tailTrace_5088670
  have hstable : (prefixWord ++ tailWord_5088670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088670).length < 2 ^ (prefixWord ++ tailWord_5088670).sum := by decide
  have hdescent : baseEnd_5088670 < baseStart_5088670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088700 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 6]
def baseStart_5088700 : Nat := 118140960795 + 5088700 * 2 ^ 59
def prefixEnd_5088700 : Nat := 4983230072969 + 3 ^ 40 * 5088700 * 2
def baseEnd_5088700 : Nat := 290327667392705074616389

theorem tailTrace_5088700 : CollatzResearch.WordTrace tailWord_5088700 prefixEnd_5088700 290327667392705074616389 := by
  unfold tailWord_5088700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92800068332258227807027777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123733424443010970409370369 92800068332258227807027777)
  ·
    refine ⟨69600051249193670855270833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92800068332258227807027777 69600051249193670855270833)
    ·
      refine ⟨52200038436895253141453125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69600051249193670855270833 52200038436895253141453125)
      ·
        refine ⟨9787507206917859964022461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52200038436895253141453125 9787507206917859964022461)
        ·
          refine ⟨3670315202594197486508423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9787507206917859964022461 3670315202594197486508423)
          ·
            refine ⟨5505472803891296229762635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670315202594197486508423 5505472803891296229762635)
            ·
              refine ⟨8258209205836944344643953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505472803891296229762635 8258209205836944344643953)
              ·
                refine ⟨6193656904377708258482965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8258209205836944344643953 6193656904377708258482965)
                ·
                  refine ⟨290327667392705074616389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6193656904377708258482965 290327667392705074616389)
                  ·
                    rfl

theorem cell23_5088700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_5088700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088700 prefixEnd_5088700 := by exact prefixLift 5088700
  have htrace : WordTrace (prefixWord ++ tailWord_5088700) baseStart_5088700 baseEnd_5088700 := by
    simpa [prefixWord, tailWord_5088700, baseEnd_5088700] using wordTrace_append hprefix tailTrace_5088700
  have hstable : (prefixWord ++ tailWord_5088700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088700).length < 2 ^ (prefixWord ++ tailWord_5088700).sum := by decide
  have hdescent : baseEnd_5088700 < baseStart_5088700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088719 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_5088719 : Nat := 118140960795 + 5088719 * 2 ^ 59
def prefixEnd_5088719 : Nat := 4983230072969 + 3 ^ 40 * 5088719 * 2
def baseEnd_5088719 : Nat := 2612958762666781097209913

theorem tailTrace_5088719 : CollatzResearch.WordTrace tailWord_5088719 prefixEnd_5088719 2612958762666781097209913 := by
  unfold tailWord_5088719
  simp only [CollatzResearch.WordTrace]
  refine ⟨185600829651447621858997211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123733886434298414572664807 185600829651447621858997211)
  ·
    refine ⟨278401244477171432788495817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185600829651447621858997211 278401244477171432788495817)
    ·
      refine ⟨208800933357878574591371863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278401244477171432788495817 208800933357878574591371863)
      ·
        refine ⟨313201400036817861887057795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208800933357878574591371863 313201400036817861887057795)
        ·
          refine ⟨469802100055226792830586693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313201400036817861887057795 469802100055226792830586693)
          ·
            refine ⟨88087893760355023655735005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 469802100055226792830586693 88087893760355023655735005)
            ·
              refine ⟨33032960160133133870900627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88087893760355023655735005 33032960160133133870900627)
              ·
                refine ⟨49549440240199700806350941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33032960160133133870900627 49549440240199700806350941)
                ·
                  refine ⟨18581040090074887802381603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49549440240199700806350941 18581040090074887802381603)
                  ·
                    refine ⟨27871560135112331703572405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18581040090074887802381603 27871560135112331703572405)
                    ·
                      refine ⟨2612958762666781097209913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27871560135112331703572405 2612958762666781097209913)
                      ·
                        rfl

theorem cell23_5088719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_5088719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088719 prefixEnd_5088719 := by exact prefixLift 5088719
  have htrace : WordTrace (prefixWord ++ tailWord_5088719) baseStart_5088719 baseEnd_5088719 := by
    simpa [prefixWord, tailWord_5088719, baseEnd_5088719] using wordTrace_append hprefix tailTrace_5088719
  have hstable : (prefixWord ++ tailWord_5088719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088719).length < 2 ^ (prefixWord ++ tailWord_5088719).sum := by decide
  have hdescent : baseEnd_5088719 < baseStart_5088719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088733 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_5088733 : Nat := 118140960795 + 5088733 * 2 ^ 59
def prefixEnd_5088733 : Nat := 4983230072969 + 3 ^ 40 * 5088733 * 2
def baseEnd_5088733 : Nat := 2612965951395944042434849

theorem tailTrace_5088733 : CollatzResearch.WordTrace tailWord_5088733 prefixEnd_5088733 2612965951395944042434849 := by
  unfold tailWord_5088733
  simp only [CollatzResearch.WordTrace]
  refine ⟨185601340273396902250006853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123734226848931268166671235 185601340273396902250006853)
  ·
    refine ⟨34800251301261919171876285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185601340273396902250006853 34800251301261919171876285)
    ·
      refine ⟨13050094237973219689453607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34800251301261919171876285 13050094237973219689453607)
      ·
        refine ⟨19575141356959829534180411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050094237973219689453607 19575141356959829534180411)
        ·
          refine ⟨29362712035439744301270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19575141356959829534180411 29362712035439744301270617)
          ·
            refine ⟨22022034026579808225952963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29362712035439744301270617 22022034026579808225952963)
            ·
              refine ⟨33033051039869712338929445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22022034026579808225952963 33033051039869712338929445)
              ·
                refine ⟨6193697069975571063549271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33033051039869712338929445 6193697069975571063549271)
                ·
                  refine ⟨9290545604963356595323907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193697069975571063549271 9290545604963356595323907)
                  ·
                    refine ⟨13935818407445034892985861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9290545604963356595323907 13935818407445034892985861)
                    ·
                      refine ⟨2612965951395944042434849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13935818407445034892985861 2612965951395944042434849)
                      ·
                        rfl

theorem cell23_5088733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_5088733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088733 prefixEnd_5088733 := by exact prefixLift 5088733
  have htrace : WordTrace (prefixWord ++ tailWord_5088733) baseStart_5088733 baseEnd_5088733 := by
    simpa [prefixWord, tailWord_5088733, baseEnd_5088733] using wordTrace_append hprefix tailTrace_5088733
  have hstable : (prefixWord ++ tailWord_5088733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088733).length < 2 ^ (prefixWord ++ tailWord_5088733).sum := by decide
  have hdescent : baseEnd_5088733 < baseStart_5088733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088753 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_5088753 : Nat := 118140960795 + 5088753 * 2 ^ 59
def prefixEnd_5088753 : Nat := 4983230072969 + 3 ^ 40 * 5088753 * 2
def baseEnd_5088753 : Nat := 2612976221009033964184757

theorem tailTrace_5088753 : CollatzResearch.WordTrace tailWord_5088753 prefixEnd_5088753 2612976221009033964184757 := by
  unfold tailWord_5088753
  simp only [CollatzResearch.WordTrace]
  refine ⟨185602069733324445665734913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123734713155549630443823275 185602069733324445665734913)
  ·
    refine ⟨139201552299993334249301185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185602069733324445665734913 139201552299993334249301185)
    ·
      refine ⟨104401164224995000686975889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139201552299993334249301185 104401164224995000686975889)
      ·
        refine ⟨78300873168746250515231917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104401164224995000686975889 78300873168746250515231917)
        ·
          refine ⟨29362827438279843943211969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78300873168746250515231917 29362827438279843943211969)
          ·
            refine ⟨22022120578709882957408977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29362827438279843943211969 22022120578709882957408977)
            ·
              refine ⟨16516590434032412218056733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22022120578709882957408977 16516590434032412218056733)
              ·
                refine ⟨6193721412762154581771275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16516590434032412218056733 6193721412762154581771275)
                ·
                  refine ⟨9290582119143231872656913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6193721412762154581771275 9290582119143231872656913)
                  ·
                    refine ⟨6967936589357423904492685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9290582119143231872656913 6967936589357423904492685)
                    ·
                      refine ⟨2612976221009033964184757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6967936589357423904492685 2612976221009033964184757)
                      ·
                        rfl

theorem cell23_5088753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_5088753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088753 prefixEnd_5088753 := by exact prefixLift 5088753
  have htrace : WordTrace (prefixWord ++ tailWord_5088753) baseStart_5088753 baseEnd_5088753 := by
    simpa [prefixWord, tailWord_5088753, baseEnd_5088753] using wordTrace_append hprefix tailTrace_5088753
  have hstable : (prefixWord ++ tailWord_5088753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088753).length < 2 ^ (prefixWord ++ tailWord_5088753).sum := by decide
  have hdescent : baseEnd_5088753 < baseStart_5088753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088826 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_5088826 : Nat := 118140960795 + 5088826 * 2 ^ 59
def prefixEnd_5088826 : Nat := 4983230072969 + 3 ^ 40 * 5088826 * 2
def baseEnd_5088826 : Nat := 2613013705096812178571921

theorem tailTrace_5088826 : CollatzResearch.WordTrace tailWord_5088826 prefixEnd_5088826 2613013705096812178571921 := by
  unfold tailWord_5088826
  simp only [CollatzResearch.WordTrace]
  refine ⟨46401183065514994783285583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123736488174706652755428221 46401183065514994783285583)
  ·
    refine ⟨69601774598272492174928375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46401183065514994783285583 69601774598272492174928375)
    ·
      refine ⟨104402661897408738262392563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69601774598272492174928375 104402661897408738262392563)
      ·
        refine ⟨156603992846113107393588845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104402661897408738262392563 156603992846113107393588845)
        ·
          refine ⟨58726497317292415272595817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156603992846113107393588845 58726497317292415272595817)
          ·
            refine ⟨44044872987969311454446863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58726497317292415272595817 44044872987969311454446863)
            ·
              refine ⟨66067309481953967181670295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44044872987969311454446863 66067309481953967181670295)
              ·
                refine ⟨99100964222930950772505443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66067309481953967181670295 99100964222930950772505443)
                ·
                  refine ⟨148651446334396426158758165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99100964222930950772505443 148651446334396426158758165)
                  ·
                    refine ⟨6968036546924832476191789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148651446334396426158758165 6968036546924832476191789)
                    ·
                      refine ⟨2613013705096812178571921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968036546924832476191789 2613013705096812178571921)
                      ·
                        rfl

theorem cell23_5088826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_5088826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088826 prefixEnd_5088826 := by exact prefixLift 5088826
  have htrace : WordTrace (prefixWord ++ tailWord_5088826) baseStart_5088826 baseEnd_5088826 := by
    simpa [prefixWord, tailWord_5088826, baseEnd_5088826] using wordTrace_append hprefix tailTrace_5088826
  have hstable : (prefixWord ++ tailWord_5088826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088826).length < 2 ^ (prefixWord ++ tailWord_5088826).sum := by decide
  have hdescent : baseEnd_5088826 < baseStart_5088826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088856 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_5088856 : Nat := 118140960795 + 5088856 * 2 ^ 59
def prefixEnd_5088856 : Nat := 4983230072969 + 3 ^ 40 * 5088856 * 2
def baseEnd_5088856 : Nat := 2613029109516447061196783

theorem tailTrace_5088856 : CollatzResearch.WordTrace tailWord_5088856 prefixEnd_5088856 2613029109516447061196783 := by
  unfold tailWord_5088856
  simp only [CollatzResearch.WordTrace]
  refine ⟨92802913225975647128367211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123737217634634196171156281 92802913225975647128367211)
  ·
    refine ⟨139204369838963470692550817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92802913225975647128367211 139204369838963470692550817)
    ·
      refine ⟨104403277379222603019413113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139204369838963470692550817 104403277379222603019413113)
      ·
        refine ⟨78302458034416952264559835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104403277379222603019413113 78302458034416952264559835)
        ·
          refine ⟨117453687051625428396839753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78302458034416952264559835 117453687051625428396839753)
          ·
            refine ⟨88090265288719071297629815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117453687051625428396839753 88090265288719071297629815)
            ·
              refine ⟨132135397933078606946444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88090265288719071297629815 132135397933078606946444723)
              ·
                refine ⟨198203096899617910419667085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132135397933078606946444723 198203096899617910419667085)
                ·
                  refine ⟨74326161337356716407375157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198203096899617910419667085 74326161337356716407375157)
                  ·
                    refine ⟨6968077625377192163191421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74326161337356716407375157 6968077625377192163191421)
                    ·
                      refine ⟨2613029109516447061196783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968077625377192163191421 2613029109516447061196783)
                      ·
                        rfl

theorem cell23_5088856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_5088856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088856 prefixEnd_5088856 := by exact prefixLift 5088856
  have htrace : WordTrace (prefixWord ++ tailWord_5088856) baseStart_5088856 baseEnd_5088856 := by
    simpa [prefixWord, tailWord_5088856, baseEnd_5088856] using wordTrace_append hprefix tailTrace_5088856
  have hstable : (prefixWord ++ tailWord_5088856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088856).length < 2 ^ (prefixWord ++ tailWord_5088856).sum := by decide
  have hdescent : baseEnd_5088856 < baseStart_5088856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088874 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5088874 : Nat := 118140960795 + 5088874 * 2 ^ 59
def prefixEnd_5088874 : Nat := 4983230072969 + 3 ^ 40 * 5088874 * 2
def baseEnd_5088874 : Nat := 2613038352168227990771701

theorem tailTrace_5088874 : CollatzResearch.WordTrace tailWord_5088874 prefixEnd_5088874 2613038352168227990771701 := by
  unfold tailWord_5088874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46401620741471520832722419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123737655310590722220593117 46401620741471520832722419)
  ·
    refine ⟨69602431112207281249083629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46401620741471520832722419 69602431112207281249083629)
    ·
      refine ⟨26100911667077730468406361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69602431112207281249083629 26100911667077730468406361)
      ·
        refine ⟨19575683750308297851304771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26100911667077730468406361 19575683750308297851304771)
        ·
          refine ⟨29363525625462446776957157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19575683750308297851304771 29363525625462446776957157)
          ·
            refine ⟨5505661054774208770679467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29363525625462446776957157 5505661054774208770679467)
            ·
              refine ⟨8258491582161313156019201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505661054774208770679467 8258491582161313156019201)
              ·
                refine ⟨6193868686620984867014401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8258491582161313156019201 6193868686620984867014401)
                ·
                  refine ⟨4645401514965738650260801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6193868686620984867014401 4645401514965738650260801)
                  ·
                    refine ⟨3484051136224303987695601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4645401514965738650260801 3484051136224303987695601)
                    ·
                      refine ⟨2613038352168227990771701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484051136224303987695601 2613038352168227990771701)
                      ·
                        rfl

theorem cell23_5088874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5088874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088874 prefixEnd_5088874 := by exact prefixLift 5088874
  have htrace : WordTrace (prefixWord ++ tailWord_5088874) baseStart_5088874 baseEnd_5088874 := by
    simpa [prefixWord, tailWord_5088874, baseEnd_5088874] using wordTrace_append hprefix tailTrace_5088874
  have hstable : (prefixWord ++ tailWord_5088874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088874).length < 2 ^ (prefixWord ++ tailWord_5088874).sum := by decide
  have hdescent : baseEnd_5088874 < baseStart_5088874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088876 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_5088876 : Nat := 118140960795 + 5088876 * 2 ^ 59
def prefixEnd_5088876 : Nat := 4983230072969 + 3 ^ 40 * 5088876 * 2
def baseEnd_5088876 : Nat := 871013126376512327648897

theorem tailTrace_5088876 : CollatzResearch.WordTrace tailWord_5088876 prefixEnd_5088876 871013126376512327648897 := by
  unfold tailWord_5088876
  simp only [CollatzResearch.WordTrace]
  refine ⟨92803277955939418836231241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123737703941252558448308321 92803277955939418836231241)
  ·
    refine ⟨69602458466954564127173431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92803277955939418836231241 69602458466954564127173431)
    ·
      refine ⟨104403687700431846190760147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69602458466954564127173431 104403687700431846190760147)
      ·
        refine ⟨156605531550647769286140221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104403687700431846190760147 156605531550647769286140221)
        ·
          refine ⟨58727074331492913482302583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156605531550647769286140221 58727074331492913482302583)
          ·
            refine ⟨88090611497239370223453875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58727074331492913482302583 88090611497239370223453875)
            ·
              refine ⟨132135917245859055335180813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88090611497239370223453875 132135917245859055335180813)
              ·
                refine ⟨49550968967197145750692805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132135917245859055335180813 49550968967197145750692805)
                ·
                  refine ⟨9290806681349464828254901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49550968967197145750692805 9290806681349464828254901)
                  ·
                    refine ⟨871013126376512327648897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9290806681349464828254901 871013126376512327648897)
                    ·
                      rfl

theorem cell23_5088876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_5088876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088876 prefixEnd_5088876 := by exact prefixLift 5088876
  have htrace : WordTrace (prefixWord ++ tailWord_5088876) baseStart_5088876 baseEnd_5088876 := by
    simpa [prefixWord, tailWord_5088876, baseEnd_5088876] using wordTrace_append hprefix tailTrace_5088876
  have hstable : (prefixWord ++ tailWord_5088876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088876).length < 2 ^ (prefixWord ++ tailWord_5088876).sum := by decide
  have hdescent : baseEnd_5088876 < baseStart_5088876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088896 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_5088896 : Nat := 118140960795 + 5088896 * 2 ^ 59
def prefixEnd_5088896 : Nat := 4983230072969 + 3 ^ 40 * 5088896 * 2
def baseEnd_5088896 : Nat := 2613049648742626904696599

theorem tailTrace_5088896 : CollatzResearch.WordTrace tailWord_5088896 prefixEnd_5088896 2613049648742626904696599 := by
  unfold tailWord_5088896
  simp only [CollatzResearch.WordTrace]
  refine ⟨92803642685903190544095271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123738190247870920725460361 92803642685903190544095271)
  ·
    refine ⟨139205464028854785816142907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92803642685903190544095271 139205464028854785816142907)
    ·
      refine ⟨208808196043282178724214361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139205464028854785816142907 208808196043282178724214361)
      ·
        refine ⟨156606147032461634043160771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208808196043282178724214361 156606147032461634043160771)
        ·
          refine ⟨234909220548692451064741157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156606147032461634043160771 234909220548692451064741157)
          ·
            refine ⟨44045478852879834574638967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234909220548692451064741157 44045478852879834574638967)
            ·
              refine ⟨66068218279319751861958451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44045478852879834574638967 66068218279319751861958451)
              ·
                refine ⟨99102327418979627792937677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66068218279319751861958451 99102327418979627792937677)
                ·
                  refine ⟨37163372782117360422351629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99102327418979627792937677 37163372782117360422351629)
                  ·
                    refine ⟨13936264793294010158381861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37163372782117360422351629 13936264793294010158381861)
                    ·
                      refine ⟨2613049648742626904696599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13936264793294010158381861 2613049648742626904696599)
                      ·
                        rfl

theorem cell23_5088896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_5088896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088896 prefixEnd_5088896 := by exact prefixLift 5088896
  have htrace : WordTrace (prefixWord ++ tailWord_5088896) baseStart_5088896 baseEnd_5088896 := by
    simpa [prefixWord, tailWord_5088896, baseEnd_5088896] using wordTrace_append hprefix tailTrace_5088896
  have hstable : (prefixWord ++ tailWord_5088896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088896).length < 2 ^ (prefixWord ++ tailWord_5088896).sum := by decide
  have hdescent : baseEnd_5088896 < baseStart_5088896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_5088913 : Nat := 118140960795 + 5088913 * 2 ^ 59
def prefixEnd_5088913 : Nat := 4983230072969 + 3 ^ 40 * 5088913 * 2
def baseEnd_5088913 : Nat := 2613058377913753338184021

theorem tailTrace_5088913 : CollatzResearch.WordTrace tailWord_5088913 prefixEnd_5088913 2613058377913753338184021 := by
  unfold tailWord_5088913
  simp only [CollatzResearch.WordTrace]
  refine ⟨185607905412744792991559393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123738603608496528661039595 185607905412744792991559393)
  ·
    refine ⟨139205929059558594743669545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185607905412744792991559393 139205929059558594743669545)
    ·
      refine ⟨104404446794668946057752159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139205929059558594743669545 104404446794668946057752159)
      ·
        refine ⟨156606670192003419086628239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104404446794668946057752159 156606670192003419086628239)
        ·
          refine ⟨234910005288005128629942359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156606670192003419086628239 234910005288005128629942359)
          ·
            refine ⟨352365007932007692944913539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234910005288005128629942359 352365007932007692944913539)
            ·
              refine ⟨528547511898011539417370309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352365007932007692944913539 528547511898011539417370309)
              ·
                refine ⟨99102658480877163640756933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528547511898011539417370309 99102658480877163640756933)
                ·
                  refine ⟨18581748465164468182641925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99102658480877163640756933 18581748465164468182641925)
                  ·
                    refine ⟨3484077837218337784245361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18581748465164468182641925 3484077837218337784245361)
                    ·
                      refine ⟨2613058377913753338184021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484077837218337784245361 2613058377913753338184021)
                      ·
                        rfl

theorem cell23_5088913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_5088913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088913 prefixEnd_5088913 := by exact prefixLift 5088913
  have htrace : WordTrace (prefixWord ++ tailWord_5088913) baseStart_5088913 baseEnd_5088913 := by
    simpa [prefixWord, tailWord_5088913, baseEnd_5088913] using wordTrace_append hprefix tailTrace_5088913
  have hstable : (prefixWord ++ tailWord_5088913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088913).length < 2 ^ (prefixWord ++ tailWord_5088913).sum := by decide
  have hdescent : baseEnd_5088913 < baseStart_5088913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088914 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_5088914 : Nat := 118140960795 + 5088914 * 2 ^ 59
def prefixEnd_5088914 : Nat := 4983230072969 + 3 ^ 40 * 5088914 * 2
def baseEnd_5088914 : Nat := 290339876821600870474613

theorem tailTrace_5088914 : CollatzResearch.WordTrace tailWord_5088914 prefixEnd_5088914 290339876821600870474613 := by
  unfold tailWord_5088914
  simp only [CollatzResearch.WordTrace]
  refine ⟨46401985471435292540586449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123738627923827446774897197 46401985471435292540586449)
  ·
    refine ⟨34801489103576469405439837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46401985471435292540586449 34801489103576469405439837)
    ·
      refine ⟨13050558413841176027039939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34801489103576469405439837 13050558413841176027039939)
      ·
        refine ⟨19575837620761764040559909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050558413841176027039939 19575837620761764040559909)
        ·
          refine ⟨3670469553892830757604983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19575837620761764040559909 3670469553892830757604983)
          ·
            refine ⟨5505704330839246136407475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670469553892830757604983 5505704330839246136407475)
            ·
              refine ⟨8258556496258869204611213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505704330839246136407475 8258556496258869204611213)
              ·
                refine ⟨3096958686097075951729205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8258556496258869204611213 3096958686097075951729205)
                ·
                  refine ⟨290339876821600870474613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096958686097075951729205 290339876821600870474613)
                  ·
                    rfl

theorem cell23_5088914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_5088914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088914 prefixEnd_5088914 := by exact prefixLift 5088914
  have htrace : WordTrace (prefixWord ++ tailWord_5088914) baseStart_5088914 baseEnd_5088914 := by
    simpa [prefixWord, tailWord_5088914, baseEnd_5088914] using wordTrace_append hprefix tailTrace_5088914
  have hstable : (prefixWord ++ tailWord_5088914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088914).length < 2 ^ (prefixWord ++ tailWord_5088914).sum := by decide
  have hdescent : baseEnd_5088914 < baseStart_5088914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088933 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_5088933 : Nat := 118140960795 + 5088933 * 2 ^ 59
def prefixEnd_5088933 : Nat := 4983230072969 + 3 ^ 40 * 5088933 * 2
def baseEnd_5088933 : Nat := 2613068647526843259933929

theorem tailTrace_5088933 : CollatzResearch.WordTrace tailWord_5088933 prefixEnd_5088933 2613068647526843259933929 := by
  unfold tailWord_5088933
  simp only [CollatzResearch.WordTrace]
  refine ⟨185608634872672336407287453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123739089915114890938191635 185608634872672336407287453)
  ·
    refine ⟨69603238077252126152732795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185608634872672336407287453 69603238077252126152732795)
    ·
      refine ⟨104404857115878189229099193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69603238077252126152732795 104404857115878189229099193)
      ·
        refine ⟨78303642836908641921824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104404857115878189229099193 78303642836908641921824395)
        ·
          refine ⟨117455464255362962882736593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78303642836908641921824395 117455464255362962882736593)
          ·
            refine ⟨88091598191522222162052445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117455464255362962882736593 88091598191522222162052445)
            ·
              refine ⟨33034349321820833310769667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88091598191522222162052445 33034349321820833310769667)
              ·
                refine ⟨49551523982731249966154501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33034349321820833310769667 49551523982731249966154501)
                ·
                  refine ⟨9290910746762109368653969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49551523982731249966154501 9290910746762109368653969)
                  ·
                    refine ⟨6968183060071582026490477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9290910746762109368653969 6968183060071582026490477)
                    ·
                      refine ⟨2613068647526843259933929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968183060071582026490477 2613068647526843259933929)
                      ·
                        rfl

theorem cell23_5088933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_5088933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088933 prefixEnd_5088933 := by exact prefixLift 5088933
  have htrace : WordTrace (prefixWord ++ tailWord_5088933) baseStart_5088933 baseEnd_5088933 := by
    simpa [prefixWord, tailWord_5088933, baseEnd_5088933] using wordTrace_append hprefix tailTrace_5088933
  have hstable : (prefixWord ++ tailWord_5088933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088933).length < 2 ^ (prefixWord ++ tailWord_5088933).sum := by decide
  have hdescent : baseEnd_5088933 < baseStart_5088933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5088976 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_5088976 : Nat := 118140960795 + 5088976 * 2 ^ 59
def prefixEnd_5088976 : Nat := 4983230072969 + 3 ^ 40 * 5088976 * 2
def baseEnd_5088976 : Nat := 2613090727194986591696231

theorem tailTrace_5088976 : CollatzResearch.WordTrace tailWord_5088976 prefixEnd_5088976 2613090727194986591696231 := by
  unfold tailWord_5088976
  simp only [CollatzResearch.WordTrace]
  refine ⟨92805101605758277375551391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123740135474344369834068521 92805101605758277375551391)
  ·
    refine ⟨139207652408637416063327087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92805101605758277375551391 139207652408637416063327087)
    ·
      refine ⟨208811478612956124094990631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139207652408637416063327087 208811478612956124094990631)
      ·
        refine ⟨313217217919434186142485947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208811478612956124094990631 313217217919434186142485947)
        ·
          refine ⟨469825826879151279213728921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313217217919434186142485947 469825826879151279213728921)
          ·
            refine ⟨352369370159363459410296691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469825826879151279213728921 352369370159363459410296691)
            ·
              refine ⟨528554055239045189115445037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352369370159363459410296691 528554055239045189115445037)
              ·
                refine ⟨198207770714641945918291889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528554055239045189115445037 198207770714641945918291889)
                ·
                  refine ⟨148655828035981459438718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198207770714641945918291889 148655828035981459438718917)
                  ·
                    refine ⟨27872967756746523644759797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148655828035981459438718917 27872967756746523644759797)
                    ·
                      refine ⟨2613090727194986591696231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27872967756746523644759797 2613090727194986591696231)
                      ·
                        rfl

theorem cell23_5088976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_5088976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5088976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5088976 prefixEnd_5088976 := by exact prefixLift 5088976
  have htrace : WordTrace (prefixWord ++ tailWord_5088976) baseStart_5088976 baseEnd_5088976 := by
    simpa [prefixWord, tailWord_5088976, baseEnd_5088976] using wordTrace_append hprefix tailTrace_5088976
  have hstable : (prefixWord ++ tailWord_5088976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5088976).length < 2 ^ (prefixWord ++ tailWord_5088976).sum := by decide
  have hdescent : baseEnd_5088976 < baseStart_5088976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5088976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089003 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4]
def baseStart_5089003 : Nat := 118140960795 + 5089003 * 2 ^ 59
def prefixEnd_5089003 : Nat := 4983230072969 + 3 ^ 40 * 5089003 * 2
def baseEnd_5089003 : Nat := 2613104591172657986058607

theorem tailTrace_5089003 : CollatzResearch.WordTrace tailWord_5089003 prefixEnd_5089003 2613104591172657986058607 := by
  unfold tailWord_5089003
  simp only [CollatzResearch.WordTrace]
  refine ⟨185611187982418738362335663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123740791988279158908223775 185611187982418738362335663)
  ·
    refine ⟨278416781973628107543503495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185611187982418738362335663 278416781973628107543503495)
    ·
      refine ⟨417625172960442161315255243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278416781973628107543503495 417625172960442161315255243)
      ·
        refine ⟨626437759440663241972882865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417625172960442161315255243 626437759440663241972882865)
        ·
          refine ⟨469828319580497431479662149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626437759440663241972882865 469828319580497431479662149)
          ·
            refine ⟨88092809921343268402436653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 469828319580497431479662149 88092809921343268402436653)
            ·
              refine ⟨33034803720503725650913745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88092809921343268402436653 33034803720503725650913745)
              ·
                refine ⟨24776102790377794238185309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33034803720503725650913745 24776102790377794238185309)
                ·
                  refine ⟨9291038546391672839319491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24776102790377794238185309 9291038546391672839319491)
                  ·
                    refine ⟨13936557819587509258979237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291038546391672839319491 13936557819587509258979237)
                    ·
                      refine ⟨2613104591172657986058607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13936557819587509258979237 2613104591172657986058607)
                      ·
                        rfl

theorem cell23_5089003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_5089003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089003 prefixEnd_5089003 := by exact prefixLift 5089003
  have htrace : WordTrace (prefixWord ++ tailWord_5089003) baseStart_5089003 baseEnd_5089003 := by
    simpa [prefixWord, tailWord_5089003, baseEnd_5089003] using wordTrace_append hprefix tailTrace_5089003
  have hstable : (prefixWord ++ tailWord_5089003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089003).length < 2 ^ (prefixWord ++ tailWord_5089003).sum := by decide
  have hdescent : baseEnd_5089003 < baseStart_5089003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089020 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_5089020 : Nat := 118140960795 + 5089020 * 2 ^ 59
def prefixEnd_5089020 : Nat := 4983230072969 + 3 ^ 40 * 5089020 * 2
def baseEnd_5089020 : Nat := 2613113320343784419546029

theorem tailTrace_5089020 : CollatzResearch.WordTrace tailWord_5089020 prefixEnd_5089020 2613113320343784419546029 := by
  unfold tailWord_5089020
  simp only [CollatzResearch.WordTrace]
  refine ⟨92805904011678575132852257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123741205348904766843803009 92805904011678575132852257)
  ·
    refine ⟨69604428008758931349639193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92805904011678575132852257 69604428008758931349639193)
    ·
      refine ⟨52203321006569198512229395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69604428008758931349639193 52203321006569198512229395)
      ·
        refine ⟨78304981509853797768344093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52203321006569198512229395 78304981509853797768344093)
        ·
          refine ⟨29364368066195174163129035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78304981509853797768344093 29364368066195174163129035)
          ·
            refine ⟨44046552099292761244693553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29364368066195174163129035 44046552099292761244693553)
            ·
              refine ⟨33034914074469570933520165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44046552099292761244693553 33034914074469570933520165)
              ·
                refine ⟨6194046388963044550035031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33034914074469570933520165 6194046388963044550035031)
                ·
                  refine ⟨9291069583444566825052547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194046388963044550035031 9291069583444566825052547)
                  ·
                    refine ⟨13936604375166850237578821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291069583444566825052547 13936604375166850237578821)
                    ·
                      refine ⟨2613113320343784419546029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13936604375166850237578821 2613113320343784419546029)
                      ·
                        rfl

theorem cell23_5089020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_5089020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089020 prefixEnd_5089020 := by exact prefixLift 5089020
  have htrace : WordTrace (prefixWord ++ tailWord_5089020) baseStart_5089020 baseEnd_5089020 := by
    simpa [prefixWord, tailWord_5089020, baseEnd_5089020] using wordTrace_append hprefix tailTrace_5089020
  have hstable : (prefixWord ++ tailWord_5089020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089020).length < 2 ^ (prefixWord ++ tailWord_5089020).sum := by decide
  have hdescent : baseEnd_5089020 < baseStart_5089020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089031 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5089031 : Nat := 118140960795 + 5089031 * 2 ^ 59
def prefixEnd_5089031 : Nat := 4983230072969 + 3 ^ 40 * 5089031 * 2
def baseEnd_5089031 : Nat := 2613118968630983876508479

theorem tailTrace_5089031 : CollatzResearch.WordTrace tailWord_5089031 prefixEnd_5089031 2613118968630983876508479 := by
  unfold tailWord_5089031
  simp only [CollatzResearch.WordTrace]
  refine ⟨185612209226317299144354947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123741472817544866096236631 185612209226317299144354947)
  ·
    refine ⟨278418313839475948716532421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185612209226317299144354947 278418313839475948716532421)
    ·
      refine ⟨52203433844901740384349829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278418313839475948716532421 52203433844901740384349829)
      ·
        refine ⟨9788143845919076322065593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52203433844901740384349829 9788143845919076322065593)
        ·
          refine ⟨7341107884439307241549195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788143845919076322065593 7341107884439307241549195)
          ·
            refine ⟨11011661826658960862323793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341107884439307241549195 11011661826658960862323793)
            ·
              refine ⟨8258746369994220646742845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11011661826658960862323793 8258746369994220646742845)
              ·
                refine ⟨3097029888747832742528567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8258746369994220646742845 3097029888747832742528567)
                ·
                  refine ⟨4645544833121749113792851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097029888747832742528567 4645544833121749113792851)
                  ·
                    refine ⟨6968317249682623670689277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645544833121749113792851 6968317249682623670689277)
                    ·
                      refine ⟨2613118968630983876508479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968317249682623670689277 2613118968630983876508479)
                      ·
                        rfl

theorem cell23_5089031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5089031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089031 prefixEnd_5089031 := by exact prefixLift 5089031
  have htrace : WordTrace (prefixWord ++ tailWord_5089031) baseStart_5089031 baseEnd_5089031 := by
    simpa [prefixWord, tailWord_5089031, baseEnd_5089031] using wordTrace_append hprefix tailTrace_5089031
  have hstable : (prefixWord ++ tailWord_5089031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089031).length < 2 ^ (prefixWord ++ tailWord_5089031).sum := by decide
  have hdescent : baseEnd_5089031 < baseStart_5089031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089047 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 2, 4]
def baseStart_5089047 : Nat := 118140960795 + 5089047 * 2 ^ 59
def prefixEnd_5089047 : Nat := 4983230072969 + 3 ^ 40 * 5089047 * 2
def baseEnd_5089047 : Nat := 871042394773818604636135

theorem tailTrace_5089047 : CollatzResearch.WordTrace tailWord_5089047 prefixEnd_5089047 871042394773818604636135 := by
  unfold tailWord_5089047
  simp only [CollatzResearch.WordTrace]
  refine ⟨185612792794259333876937395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123741861862839555917958263 185612792794259333876937395)
  ·
    refine ⟨278419189191389000815406093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185612792794259333876937395 278419189191389000815406093)
    ·
      refine ⟨104407195946770875305777285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278419189191389000815406093 104407195946770875305777285)
      ·
        refine ⟨19576349240019539119833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104407195946770875305777285 19576349240019539119833241)
        ·
          refine ⟨14682261930014654339874931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19576349240019539119833241 14682261930014654339874931)
          ·
            refine ⟨22023392895021981509812397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14682261930014654339874931 22023392895021981509812397)
            ·
              refine ⟨8258772335633243066179649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22023392895021981509812397 8258772335633243066179649)
              ·
                refine ⟨6194079251724932299634737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8258772335633243066179649 6194079251724932299634737)
                ·
                  refine ⟨4645559438793699224726053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6194079251724932299634737 4645559438793699224726053)
                  ·
                    refine ⟨871042394773818604636135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645559438793699224726053 871042394773818604636135)
                    ·
                      rfl

theorem cell23_5089047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_5089047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089047 prefixEnd_5089047 := by exact prefixLift 5089047
  have htrace : WordTrace (prefixWord ++ tailWord_5089047) baseStart_5089047 baseEnd_5089047 := by
    simpa [prefixWord, tailWord_5089047, baseEnd_5089047] using wordTrace_append hprefix tailTrace_5089047
  have hstable : (prefixWord ++ tailWord_5089047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089047).length < 2 ^ (prefixWord ++ tailWord_5089047).sum := by decide
  have hdescent : baseEnd_5089047 < baseStart_5089047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089064 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5089064 : Nat := 118140960795 + 5089064 * 2 ^ 59
def prefixEnd_5089064 : Nat := 4983230072969 + 3 ^ 40 * 5089064 * 2
def baseEnd_5089064 : Nat := 871045304497527415798609

theorem tailTrace_5089064 : CollatzResearch.WordTrace tailWord_5089064 prefixEnd_5089064 871045304497527415798609 := by
  unfold tailWord_5089064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92806706417598872890153123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123742275223465163853537497 92806706417598872890153123)
  ·
    refine ⟨139210059626398309335229685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92806706417598872890153123 139210059626398309335229685)
    ·
      refine ⟨13050943089974841500177783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139210059626398309335229685 13050943089974841500177783)
      ·
        refine ⟨19576414634962262250266675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050943089974841500177783 19576414634962262250266675)
        ·
          refine ⟨29364621952443393375400013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19576414634962262250266675 29364621952443393375400013)
          ·
            refine ⟨11011733232166272515775005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29364621952443393375400013 11011733232166272515775005)
            ·
              refine ⟨4129399962062352193415627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11011733232166272515775005 4129399962062352193415627)
              ·
                refine ⟨6194099943093528290123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129399962062352193415627 6194099943093528290123441)
                ·
                  refine ⟨4645574957320146217592581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6194099943093528290123441 4645574957320146217592581)
                  ·
                    refine ⟨871045304497527415798609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645574957320146217592581 871045304497527415798609)
                    ·
                      rfl

theorem cell23_5089064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5089064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089064 prefixEnd_5089064 := by exact prefixLift 5089064
  have htrace : WordTrace (prefixWord ++ tailWord_5089064) baseStart_5089064 baseEnd_5089064 := by
    simpa [prefixWord, tailWord_5089064, baseEnd_5089064] using wordTrace_append hprefix tailTrace_5089064
  have hstable : (prefixWord ++ tailWord_5089064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089064).length < 2 ^ (prefixWord ++ tailWord_5089064).sum := by decide
  have hdescent : baseEnd_5089064 < baseStart_5089064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089077 : List Nat := [1, 3, 3, 1, 4, 2, 2, 7]
def baseStart_5089077 : Nat := 118140960795 + 5089077 * 2 ^ 59
def prefixEnd_5089077 : Nat := 4983230072969 + 3 ^ 40 * 5089077 * 2
def baseEnd_5089077 : Nat := 96783058842262618390121

theorem tailTrace_5089077 : CollatzResearch.WordTrace tailWord_5089077 prefixEnd_5089077 96783058842262618390121 := by
  unfold tailWord_5089077
  simp only [CollatzResearch.WordTrace]
  refine ⟨185613886984150649000529485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123742591322767099333686323 185613886984150649000529485)
  ·
    refine ⟨69605207619056493375198557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185613886984150649000529485 69605207619056493375198557)
    ·
      refine ⟨26101952857146185015699459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69605207619056493375198557 26101952857146185015699459)
      ·
        refine ⟨39152929285719277523549189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26101952857146185015699459 39152929285719277523549189)
        ·
          refine ⟨7341174241072364535665473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39152929285719277523549189 7341174241072364535665473)
          ·
            refine ⟨5505880680804273401749105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7341174241072364535665473 5505880680804273401749105)
            ·
              refine ⟨4129410510603205051311829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5505880680804273401749105 4129410510603205051311829)
              ·
                refine ⟨96783058842262618390121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4129410510603205051311829 96783058842262618390121)
                ·
                  rfl

theorem cell23_5089077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 7].length) (baseStart_5089077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089077 prefixEnd_5089077 := by exact prefixLift 5089077
  have htrace : WordTrace (prefixWord ++ tailWord_5089077) baseStart_5089077 baseEnd_5089077 := by
    simpa [prefixWord, tailWord_5089077, baseEnd_5089077] using wordTrace_append hprefix tailTrace_5089077
  have hstable : (prefixWord ++ tailWord_5089077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089077).length < 2 ^ (prefixWord ++ tailWord_5089077).sum := by decide
  have hdescent : baseEnd_5089077 < baseStart_5089077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089097 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 1, 3, 2]
def baseStart_5089097 : Nat := 118140960795 + 5089097 * 2 ^ 59
def prefixEnd_5089097 : Nat := 4983230072969 + 3 ^ 40 * 5089097 * 2
def baseEnd_5089097 : Nat := 2613152858354180618283175

theorem tailTrace_5089097 : CollatzResearch.WordTrace tailWord_5089097 prefixEnd_5089097 2613152858354180618283175 := by
  unfold tailWord_5089097
  simp only [CollatzResearch.WordTrace]
  refine ⟨185614616444078192416257545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123743077629385461610838363 185614616444078192416257545)
  ·
    refine ⟨139210962333058644312193159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185614616444078192416257545 139210962333058644312193159)
    ·
      refine ⟨208816443499587966468289739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139210962333058644312193159 208816443499587966468289739)
      ·
        refine ⟨313224665249381949702434609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208816443499587966468289739 313224665249381949702434609)
        ·
          refine ⟨234918498937036462276825957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313224665249381949702434609 234918498937036462276825957)
          ·
            refine ⟨44047218550694336676904867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234918498937036462276825957 44047218550694336676904867)
            ·
              refine ⟨66070827826041505015357301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44047218550694336676904867 66070827826041505015357301)
              ·
                refine ⟨6194140108691391095189747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66070827826041505015357301 6194140108691391095189747)
                ·
                  refine ⟨9291210163037086642784621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194140108691391095189747 9291210163037086642784621)
                  ·
                    refine ⟨3484203811138907491044233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9291210163037086642784621 3484203811138907491044233)
                    ·
                      refine ⟨2613152858354180618283175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484203811138907491044233 2613152858354180618283175)
                      ·
                        rfl

theorem cell23_5089097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3, 2].length) (baseStart_5089097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089097 prefixEnd_5089097 := by exact prefixLift 5089097
  have htrace : WordTrace (prefixWord ++ tailWord_5089097) baseStart_5089097 baseEnd_5089097 := by
    simpa [prefixWord, tailWord_5089097, baseEnd_5089097] using wordTrace_append hprefix tailTrace_5089097
  have hstable : (prefixWord ++ tailWord_5089097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089097).length < 2 ^ (prefixWord ++ tailWord_5089097).sum := by decide
  have hdescent : baseEnd_5089097 < baseStart_5089097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089113 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_5089113 : Nat := 118140960795 + 5089113 * 2 ^ 59
def prefixEnd_5089113 : Nat := 4983230072969 + 3 ^ 40 * 5089113 * 2
def baseEnd_5089113 : Nat := 2613161074044652555683101

theorem tailTrace_5089113 : CollatzResearch.WordTrace tailWord_5089113 prefixEnd_5089113 2613161074044652555683101 := by
  unfold tailWord_5089113
  simp only [CollatzResearch.WordTrace]
  refine ⟨185615200012020227148839993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123743466674680151432559995 185615200012020227148839993)
  ·
    refine ⟨139211400009015170361629995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185615200012020227148839993 139211400009015170361629995)
    ·
      refine ⟨208817100013522755542444993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139211400009015170361629995 208817100013522755542444993)
      ·
        refine ⟨156612825010142066656833745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208817100013522755542444993 156612825010142066656833745)
        ·
          refine ⟨117459618757606549992625309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156612825010142066656833745 117459618757606549992625309)
          ·
            refine ⟨44047357034102456247234491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117459618757606549992625309 44047357034102456247234491)
            ·
              refine ⟨66071035551153684370851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44047357034102456247234491 66071035551153684370851737)
              ·
                refine ⟨49553276663365263278138803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66071035551153684370851737 49553276663365263278138803)
                ·
                  refine ⟨74329914995047894917208205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49553276663365263278138803 74329914995047894917208205)
                  ·
                    refine ⟨27873718123142960593953077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74329914995047894917208205 27873718123142960593953077)
                    ·
                      refine ⟨2613161074044652555683101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27873718123142960593953077 2613161074044652555683101)
                      ·
                        rfl

theorem cell23_5089113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_5089113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089113 prefixEnd_5089113 := by exact prefixLift 5089113
  have htrace : WordTrace (prefixWord ++ tailWord_5089113) baseStart_5089113 baseEnd_5089113 := by
    simpa [prefixWord, tailWord_5089113, baseEnd_5089113] using wordTrace_append hprefix tailTrace_5089113
  have hstable : (prefixWord ++ tailWord_5089113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089113).length < 2 ^ (prefixWord ++ tailWord_5089113).sum := by decide
  have hdescent : baseEnd_5089113 < baseStart_5089113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089127 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_5089127 : Nat := 118140960795 + 5089127 * 2 ^ 59
def prefixEnd_5089127 : Nat := 4983230072969 + 3 ^ 40 * 5089127 * 2
def baseEnd_5089127 : Nat := 2613168262773815500908037

theorem tailTrace_5089127 : CollatzResearch.WordTrace tailWord_5089127 prefixEnd_5089127 2613168262773815500908037 := by
  unfold tailWord_5089127
  simp only [CollatzResearch.WordTrace]
  refine ⟨185615710633969507539849635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123743807089313005026566423 185615710633969507539849635)
  ·
    refine ⟨278423565950954261309774453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185615710633969507539849635 278423565950954261309774453)
    ·
      refine ⟨26102209307901961997791355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278423565950954261309774453 26102209307901961997791355)
      ·
        refine ⟨39153313961852942996687033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26102209307901961997791355 39153313961852942996687033)
        ·
          refine ⟨29364985471389707247515275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39153313961852942996687033 29364985471389707247515275)
          ·
            refine ⟨44047478207084560871272913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29364985471389707247515275 44047478207084560871272913)
            ·
              refine ⟨33035608655313420653454685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44047478207084560871272913 33035608655313420653454685)
              ·
                refine ⟨12388353245742532745045507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33035608655313420653454685 12388353245742532745045507)
                ·
                  refine ⟨18582529868613799117568261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12388353245742532745045507 18582529868613799117568261)
                  ·
                    refine ⟨3484224350365087334544049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18582529868613799117568261 3484224350365087334544049)
                    ·
                      refine ⟨2613168262773815500908037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484224350365087334544049 2613168262773815500908037)
                      ·
                        rfl

theorem cell23_5089127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_5089127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089127 prefixEnd_5089127 := by exact prefixLift 5089127
  have htrace : WordTrace (prefixWord ++ tailWord_5089127) baseStart_5089127 baseEnd_5089127 := by
    simpa [prefixWord, tailWord_5089127, baseEnd_5089127] using wordTrace_append hprefix tailTrace_5089127
  have hstable : (prefixWord ++ tailWord_5089127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089127).length < 2 ^ (prefixWord ++ tailWord_5089127).sum := by decide
  have hdescent : baseEnd_5089127 < baseStart_5089127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089163 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 7]
def baseStart_5089163 : Nat := 118140960795 + 5089163 * 2 ^ 59
def prefixEnd_5089163 : Nat := 4983230072969 + 3 ^ 40 * 5089163 * 2
def baseEnd_5089163 : Nat := 871062249359125786685957

theorem tailTrace_5089163 : CollatzResearch.WordTrace tailWord_5089163 prefixEnd_5089163 871062249359125786685957 := by
  unfold tailWord_5089163
  simp only [CollatzResearch.WordTrace]
  refine ⟨185617023661839085688160143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123744682441226057125440095 185617023661839085688160143)
  ·
    refine ⟨278425535492758628532240215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185617023661839085688160143 278425535492758628532240215)
    ·
      refine ⟨417638303239137942798360323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278425535492758628532240215 417638303239137942798360323)
      ·
        refine ⟨626457454858706914197540485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417638303239137942798360323 626457454858706914197540485)
        ·
          refine ⟨117460772786007546412038841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 626457454858706914197540485 117460772786007546412038841)
          ·
            refine ⟨88095579589505659809029131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117460772786007546412038841 88095579589505659809029131)
            ·
              refine ⟨132143369384258489713543697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88095579589505659809029131 132143369384258489713543697)
              ·
                refine ⟨99107527038193867285157773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132143369384258489713543697 99107527038193867285157773)
                ·
                  refine ⟨37165322639322700231934165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99107527038193867285157773 37165322639322700231934165)
                  ·
                    refine ⟨871062249359125786685957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37165322639322700231934165 871062249359125786685957)
                    ·
                      rfl

theorem cell23_5089163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_5089163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089163 prefixEnd_5089163 := by exact prefixLift 5089163
  have htrace : WordTrace (prefixWord ++ tailWord_5089163) baseStart_5089163 baseEnd_5089163 := by
    simpa [prefixWord, tailWord_5089163, baseEnd_5089163] using wordTrace_append hprefix tailTrace_5089163
  have hstable : (prefixWord ++ tailWord_5089163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089163).length < 2 ^ (prefixWord ++ tailWord_5089163).sum := by decide
  have hdescent : baseEnd_5089163 < baseStart_5089163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089193 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_5089193 : Nat := 118140960795 + 5089193 * 2 ^ 59
def prefixEnd_5089193 : Nat := 4983230072969 + 3 ^ 40 * 5089193 * 2
def baseEnd_5089193 : Nat := 871067384165670747560911

theorem tailTrace_5089193 : CollatzResearch.WordTrace tailWord_5089193 prefixEnd_5089193 871067384165670747560911 := by
  unfold tailWord_5089193
  simp only [CollatzResearch.WordTrace]
  refine ⟨185618117851730400811752233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123745411901153600541168155 185618117851730400811752233)
  ·
    refine ⟨139213588388797800608814175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185618117851730400811752233 139213588388797800608814175)
    ·
      refine ⟨208820382583196700913221263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139213588388797800608814175 208820382583196700913221263)
      ·
        refine ⟨313230573874795051369831895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208820382583196700913221263 313230573874795051369831895)
        ·
          refine ⟨469845860812192577054747843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313230573874795051369831895 469845860812192577054747843)
          ·
            refine ⟨704768791218288865582121765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469845860812192577054747843 704768791218288865582121765)
            ·
              refine ⟨132144148353429162296647831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 704768791218288865582121765 132144148353429162296647831)
              ·
                refine ⟨198216222530143743444971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132144148353429162296647831 198216222530143743444971747)
                ·
                  refine ⟨297324333795215615167457621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198216222530143743444971747 297324333795215615167457621)
                  ·
                    refine ⟨871067384165670747560911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 297324333795215615167457621 871067384165670747560911)
                    ·
                      rfl

theorem cell23_5089193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_5089193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089193 prefixEnd_5089193 := by exact prefixLift 5089193
  have htrace : WordTrace (prefixWord ++ tailWord_5089193) baseStart_5089193 baseEnd_5089193 := by
    simpa [prefixWord, tailWord_5089193, baseEnd_5089193] using wordTrace_append hprefix tailTrace_5089193
  have hstable : (prefixWord ++ tailWord_5089193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089193).length < 2 ^ (prefixWord ++ tailWord_5089193).sum := by decide
  have hdescent : baseEnd_5089193 < baseStart_5089193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089227 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 3, 4]
def baseStart_5089227 : Nat := 118140960795 + 5089227 * 2 ^ 59
def prefixEnd_5089227 : Nat := 4983230072969 + 3 ^ 40 * 5089227 * 2
def baseEnd_5089227 : Nat := 871073203613088369885859

theorem tailTrace_5089227 : CollatzResearch.WordTrace tailWord_5089227 prefixEnd_5089227 871073203613088369885859 := by
  unfold tailWord_5089227
  simp only [CollatzResearch.WordTrace]
  refine ⟨185619357933607224618489935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123746238622404816412326623 185619357933607224618489935)
  ·
    refine ⟨278429036900410836927734903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185619357933607224618489935 278429036900410836927734903)
    ·
      refine ⟨417643555350616255391602355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278429036900410836927734903 417643555350616255391602355)
      ·
        refine ⟨626465333025924383087403533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417643555350616255391602355 626465333025924383087403533)
        ·
          refine ⟨234924499884721643657776325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 626465333025924383087403533 234924499884721643657776325)
          ·
            refine ⟨44048343728385308185833061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234924499884721643657776325 44048343728385308185833061)
            ·
              refine ⟨8259064449072245284843699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44048343728385308185833061 8259064449072245284843699)
              ·
                refine ⟨12388596673608367927265549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8259064449072245284843699 12388596673608367927265549)
                ·
                  refine ⟨4645723752603137972724581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12388596673608367927265549 4645723752603137972724581)
                  ·
                    refine ⟨871073203613088369885859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645723752603137972724581 871073203613088369885859)
                    ·
                      rfl

theorem cell23_5089227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 4].length) (baseStart_5089227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089227 prefixEnd_5089227 := by exact prefixLift 5089227
  have htrace : WordTrace (prefixWord ++ tailWord_5089227) baseStart_5089227 baseEnd_5089227 := by
    simpa [prefixWord, tailWord_5089227, baseEnd_5089227] using wordTrace_append hprefix tailTrace_5089227
  have hstable : (prefixWord ++ tailWord_5089227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089227).length < 2 ^ (prefixWord ++ tailWord_5089227).sum := by decide
  have hdescent : baseEnd_5089227 < baseStart_5089227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089230 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_5089230 : Nat := 118140960795 + 5089230 * 2 ^ 59
def prefixEnd_5089230 : Nat := 4983230072969 + 3 ^ 40 * 5089230 * 2
def baseEnd_5089230 : Nat := 2613221151281228597920063

theorem tailTrace_5089230 : CollatzResearch.WordTrace tailWord_5089230 prefixEnd_5089230 2613221151281228597920063 := by
  unfold tailWord_5089230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202433419074544516356143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123746311568397570753899429 23202433419074544516356143)
  ·
    refine ⟨34803650128611816774534215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23202433419074544516356143 34803650128611816774534215)
    ·
      refine ⟨52205475192917725161801323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34803650128611816774534215 52205475192917725161801323)
      ·
        refine ⟨78308212789376587742701985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52205475192917725161801323 78308212789376587742701985)
        ·
          refine ⟨58731159592032440807026489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78308212789376587742701985 58731159592032440807026489)
          ·
            refine ⟨44048369694024330605269867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58731159592032440807026489 44048369694024330605269867)
            ·
              refine ⟨66072554541036495907904801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44048369694024330605269867 66072554541036495907904801)
              ·
                refine ⟨49554415905777371930928601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66072554541036495907904801 49554415905777371930928601)
                ·
                  refine ⟨37165811929333028948196451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49554415905777371930928601 37165811929333028948196451)
                  ·
                    refine ⟨55748717893999543422294677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37165811929333028948196451 55748717893999543422294677)
                    ·
                      refine ⟨2613221151281228597920063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55748717893999543422294677 2613221151281228597920063)
                      ·
                        rfl

theorem cell23_5089230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_5089230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089230 prefixEnd_5089230 := by exact prefixLift 5089230
  have htrace : WordTrace (prefixWord ++ tailWord_5089230) baseStart_5089230 baseEnd_5089230 := by
    simpa [prefixWord, tailWord_5089230, baseEnd_5089230] using wordTrace_append hprefix tailTrace_5089230
  have hstable : (prefixWord ++ tailWord_5089230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089230).length < 2 ^ (prefixWord ++ tailWord_5089230).sum := by decide
  have hdescent : baseEnd_5089230 < baseStart_5089230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089237 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5089237 : Nat := 118140960795 + 5089237 * 2 ^ 59
def prefixEnd_5089237 : Nat := 4983230072969 + 3 ^ 40 * 5089237 * 2
def baseEnd_5089237 : Nat := 2613224745645810070532531

theorem tailTrace_5089237 : CollatzResearch.WordTrace tailWord_5089237 prefixEnd_5089237 2613224745645810070532531 := by
  unfold tailWord_5089237
  simp only [CollatzResearch.WordTrace]
  refine ⟨185619722663570996326353965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123746481775713997550902643 185619722663570996326353965)
  ·
    refine ⟨69607395998839123622382737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185619722663570996326353965 69607395998839123622382737)
    ·
      refine ⟨52205546999129342716787053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69607395998839123622382737 52205546999129342716787053)
      ·
        refine ⟨19577080124673503518795145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52205546999129342716787053 19577080124673503518795145)
        ·
          refine ⟨14682810093505127639096359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19577080124673503518795145 14682810093505127639096359)
          ·
            refine ⟨22024215140257691458644539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14682810093505127639096359 22024215140257691458644539)
            ·
              refine ⟨33036322710386537187966809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22024215140257691458644539 33036322710386537187966809)
              ·
                refine ⟨24777242032789902890975107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33036322710386537187966809 24777242032789902890975107)
                ·
                  refine ⟨37165863049184854336462661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24777242032789902890975107 37165863049184854336462661)
                  ·
                    refine ⟨6968599321722160188086749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37165863049184854336462661 6968599321722160188086749)
                    ·
                      refine ⟨2613224745645810070532531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968599321722160188086749 2613224745645810070532531)
                      ·
                        rfl

theorem cell23_5089237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5089237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089237 prefixEnd_5089237 := by exact prefixLift 5089237
  have htrace : WordTrace (prefixWord ++ tailWord_5089237) baseStart_5089237 baseEnd_5089237 := by
    simpa [prefixWord, tailWord_5089237, baseEnd_5089237] using wordTrace_append hprefix tailTrace_5089237
  have hstable : (prefixWord ++ tailWord_5089237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089237).length < 2 ^ (prefixWord ++ tailWord_5089237).sum := by decide
  have hdescent : baseEnd_5089237 < baseStart_5089237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089267 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 3]
def baseStart_5089267 : Nat := 118140960795 + 5089267 * 2 ^ 59
def prefixEnd_5089267 : Nat := 4983230072969 + 3 ^ 40 * 5089267 * 2
def baseEnd_5089267 : Nat := 2613240150065444953157393

theorem tailTrace_5089267 : CollatzResearch.WordTrace tailWord_5089267 prefixEnd_5089267 2613240150065444953157393 := by
  unfold tailWord_5089267
  simp only [CollatzResearch.WordTrace]
  refine ⟨185620816853462311449946055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123747211235641540966630703 185620816853462311449946055)
  ·
    refine ⟨278431225280193467174919083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185620816853462311449946055 278431225280193467174919083)
    ·
      refine ⟨417646837920290200762378625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278431225280193467174919083 417646837920290200762378625)
      ·
        refine ⟨313235128440217650571783969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417646837920290200762378625 313235128440217650571783969)
        ·
          refine ⟨234926346330163237928837977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313235128440217650571783969 234926346330163237928837977)
          ·
            refine ⟨176194759747622428446628483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234926346330163237928837977 176194759747622428446628483)
            ·
              refine ⟨264292139621433642669942725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176194759747622428446628483 264292139621433642669942725)
              ·
                refine ⟨49554776179018808000614261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264292139621433642669942725 49554776179018808000614261)
                ·
                  refine ⟨4645760266783013250057587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49554776179018808000614261 4645760266783013250057587)
                  ·
                    refine ⟨6968640400174519875086381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645760266783013250057587 6968640400174519875086381)
                    ·
                      refine ⟨2613240150065444953157393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6968640400174519875086381 2613240150065444953157393)
                      ·
                        rfl

theorem cell23_5089267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_5089267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089267 prefixEnd_5089267 := by exact prefixLift 5089267
  have htrace : WordTrace (prefixWord ++ tailWord_5089267) baseStart_5089267 baseEnd_5089267 := by
    simpa [prefixWord, tailWord_5089267, baseEnd_5089267] using wordTrace_append hprefix tailTrace_5089267
  have hstable : (prefixWord ++ tailWord_5089267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089267).length < 2 ^ (prefixWord ++ tailWord_5089267).sum := by decide
  have hdescent : baseEnd_5089267 < baseStart_5089267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089294 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5089294 : Nat := 118140960795 + 5089294 * 2 ^ 59
def prefixEnd_5089294 : Nat := 4983230072969 + 3 ^ 40 * 5089294 * 2
def baseEnd_5089294 : Nat := 2613254014043116347519769

theorem tailTrace_5089294 : CollatzResearch.WordTrace tailWord_5089294 prefixEnd_5089294 2613254014043116347519769 := by
  unfold tailWord_5089294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202725203045561882647367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123747867749576330040785957 23202725203045561882647367)
  ·
    refine ⟨34804087804568342823971051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23202725203045561882647367 34804087804568342823971051)
    ·
      refine ⟨52206131706852514235956577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34804087804568342823971051 52206131706852514235956577)
      ·
        refine ⟨39154598780139385676967433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52206131706852514235956577 39154598780139385676967433)
        ·
          refine ⟨29365949085104539257725575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39154598780139385676967433 29365949085104539257725575)
          ·
            refine ⟨44048923627656808886588363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29365949085104539257725575 44048923627656808886588363)
            ·
              refine ⟨66073385441485213329882545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44048923627656808886588363 66073385441485213329882545)
              ·
                refine ⟨49555039081113909997411909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66073385441485213329882545 49555039081113909997411909)
                ·
                  refine ⟨9291569827708858124514733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49555039081113909997411909 9291569827708858124514733)
                  ·
                    refine ⟨3484338685390821796693025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9291569827708858124514733 3484338685390821796693025)
                    ·
                      refine ⟨2613254014043116347519769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3484338685390821796693025 2613254014043116347519769)
                      ·
                        rfl

theorem cell23_5089294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5089294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089294 prefixEnd_5089294 := by exact prefixLift 5089294
  have htrace : WordTrace (prefixWord ++ tailWord_5089294) baseStart_5089294 baseEnd_5089294 := by
    simpa [prefixWord, tailWord_5089294, baseEnd_5089294] using wordTrace_append hprefix tailTrace_5089294
  have hstable : (prefixWord ++ tailWord_5089294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089294).length < 2 ^ (prefixWord ++ tailWord_5089294).sum := by decide
  have hdescent : baseEnd_5089294 < baseStart_5089294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 4]
def baseStart_5089307 : Nat := 118140960795 + 5089307 * 2 ^ 59
def prefixEnd_5089307 : Nat := 4983230072969 + 3 ^ 40 * 5089307 * 2
def baseEnd_5089307 : Nat := 2613260689291624796657209

theorem tailTrace_5089307 : CollatzResearch.WordTrace tailWord_5089307 prefixEnd_5089307 2613260689291624796657209 := by
  unfold tailWord_5089307
  simp only [CollatzResearch.WordTrace]
  refine ⟨185622275773317398281402175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123748183848878265520934783 185622275773317398281402175)
  ·
    refine ⟨278433413659976097422103263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185622275773317398281402175 278433413659976097422103263)
    ·
      refine ⟨417650120489964146133154895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278433413659976097422103263 417650120489964146133154895)
      ·
        refine ⟨626475180734946219199732343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417650120489964146133154895 626475180734946219199732343)
        ·
          refine ⟨939712771102419328799598515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626475180734946219199732343 939712771102419328799598515)
          ·
            refine ⟨1409569156653628993199397773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939712771102419328799598515 1409569156653628993199397773)
            ·
              refine ⟨528588433745110872449774165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409569156653628993199397773 528588433745110872449774165)
              ·
                refine ⟨6194395707950518036520791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 528588433745110872449774165 6194395707950518036520791)
                ·
                  refine ⟨9291593561925777054781187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194395707950518036520791 9291593561925777054781187)
                  ·
                    refine ⟨13937390342888665582171781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291593561925777054781187 13937390342888665582171781)
                    ·
                      refine ⟨2613260689291624796657209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13937390342888665582171781 2613260689291624796657209)
                      ·
                        rfl

theorem cell23_5089307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 4].length) (baseStart_5089307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089307 prefixEnd_5089307 := by exact prefixLift 5089307
  have htrace : WordTrace (prefixWord ++ tailWord_5089307) baseStart_5089307 baseEnd_5089307 := by
    simpa [prefixWord, tailWord_5089307, baseEnd_5089307] using wordTrace_append hprefix tailTrace_5089307
  have hstable : (prefixWord ++ tailWord_5089307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089307).length < 2 ^ (prefixWord ++ tailWord_5089307).sum := by decide
  have hdescent : baseEnd_5089307 < baseStart_5089307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5089317 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_5089317 : Nat := 118140960795 + 5089317 * 2 ^ 59
def prefixEnd_5089317 : Nat := 4983230072969 + 3 ^ 40 * 5089317 * 2
def baseEnd_5089317 : Nat := 871088608032723252510721

theorem tailTrace_5089317 : CollatzResearch.WordTrace tailWord_5089317 prefixEnd_5089317 871088608032723252510721 := by
  unfold tailWord_5089317
  simp only [CollatzResearch.WordTrace]
  refine ⟨185622640503281169989266205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123748427002187446659510803 185622640503281169989266205)
  ·
    refine ⟨69608490188730438745974827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185622640503281169989266205 69608490188730438745974827)
    ·
      refine ⟨104412735283095658118962241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69608490188730438745974827 104412735283095658118962241)
      ·
        refine ⟨78309551462321743589221681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104412735283095658118962241 78309551462321743589221681)
        ·
          refine ⟨58732163596741307691916261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78309551462321743589221681 58732163596741307691916261)
          ·
            refine ⟨11012280674388995192234299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58732163596741307691916261 11012280674388995192234299)
            ·
              refine ⟨16518421011583492788351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11012280674388995192234299 16518421011583492788351449)
              ·
                refine ⟨12388815758687619591263587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16518421011583492788351449 12388815758687619591263587)
                ·
                  refine ⟨18583223638031429386895381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12388815758687619591263587 18583223638031429386895381)
                  ·
                    refine ⟨871088608032723252510721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18583223638031429386895381 871088608032723252510721)
                    ·
                      rfl

theorem cell23_5089317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_5089317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5089317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5089317 prefixEnd_5089317 := by exact prefixLift 5089317
  have htrace : WordTrace (prefixWord ++ tailWord_5089317) baseStart_5089317 baseEnd_5089317 := by
    simpa [prefixWord, tailWord_5089317, baseEnd_5089317] using wordTrace_append hprefix tailTrace_5089317
  have hstable : (prefixWord ++ tailWord_5089317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5089317).length < 2 ^ (prefixWord ++ tailWord_5089317).sum := by decide
  have hdescent : baseEnd_5089317 < baseStart_5089317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5089317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
