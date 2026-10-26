import V185TrunkScan23Chunk0697

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4126538 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4126538 : Nat := 118140960795 + 4126538 * 2 ^ 59
def prefixEnd_4126538 : Nat := 4983230072969 + 3 ^ 40 * 4126538 * 2
def baseEnd_4126538 : Nat := 2118897433043081134797403

theorem tailTrace_4126538 : CollatzResearch.WordTrace tailWord_4126538 prefixEnd_4126538 2118897433043081134797403 := by
  unfold tailWord_4126538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37626801381066264356743067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100338137016176704951314845 37626801381066264356743067)
  ·
    refine ⟨56440202071599396535114601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37626801381066264356743067 56440202071599396535114601)
    ·
      refine ⟨42330151553699547401335951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56440202071599396535114601 42330151553699547401335951)
      ·
        refine ⟨63495227330549321102003927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42330151553699547401335951 63495227330549321102003927)
        ·
          refine ⟨95242840995823981653005891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63495227330549321102003927 95242840995823981653005891)
          ·
            refine ⟨142864261493735972479508837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95242840995823981653005891 142864261493735972479508837)
            ·
              refine ⟨26787049030075494839907907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142864261493735972479508837 26787049030075494839907907)
              ·
                refine ⟨40180573545113242259861861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26787049030075494839907907 40180573545113242259861861)
                ·
                  refine ⟨7533857539708732923724099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40180573545113242259861861 7533857539708732923724099)
                  ·
                    refine ⟨11300786309563099385586149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7533857539708732923724099 11300786309563099385586149)
                    ·
                      refine ⟨2118897433043081134797403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300786309563099385586149 2118897433043081134797403)
                      ·
                        rfl

theorem cell23_4126538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4126538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126538 prefixEnd_4126538 := by exact prefixLift 4126538
  have htrace : WordTrace (prefixWord ++ tailWord_4126538) baseStart_4126538 baseEnd_4126538 := by
    simpa [prefixWord, tailWord_4126538, baseEnd_4126538] using wordTrace_append hprefix tailTrace_4126538
  have hstable : (prefixWord ++ tailWord_4126538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126538).length < 2 ^ (prefixWord ++ tailWord_4126538).sum := by decide
  have hdescent : baseEnd_4126538 < baseStart_4126538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126568 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4126568 : Nat := 118140960795 + 4126568 * 2 ^ 59
def prefixEnd_4126568 : Nat := 4983230072969 + 3 ^ 40 * 4126568 * 2
def baseEnd_4126568 : Nat := 2118912837462716017422265

theorem tailTrace_4126568 : CollatzResearch.WordTrace tailWord_4126568 prefixEnd_4126568 2118912837462716017422265 := by
  unfold tailWord_4126568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75254149857078186275282179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100338866476104248367042905 75254149857078186275282179)
  ·
    refine ⟨112881224785617279412923269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75254149857078186275282179 112881224785617279412923269)
    ·
      refine ⟨21165229647303239889923113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112881224785617279412923269 21165229647303239889923113)
      ·
        refine ⟨15873922235477429917442335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21165229647303239889923113 15873922235477429917442335)
        ·
          refine ⟨23810883353216144876163503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873922235477429917442335 23810883353216144876163503)
          ·
            refine ⟨35716325029824217314245255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23810883353216144876163503 35716325029824217314245255)
            ·
              refine ⟨53574487544736325971367883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35716325029824217314245255 53574487544736325971367883)
              ·
                refine ⟨80361731317104488957051825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53574487544736325971367883 80361731317104488957051825)
                ·
                  refine ⟨60271298487828366717788869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80361731317104488957051825 60271298487828366717788869)
                  ·
                    refine ⟨11300868466467818759585413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60271298487828366717788869 11300868466467818759585413)
                    ·
                      refine ⟨2118912837462716017422265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11300868466467818759585413 2118912837462716017422265)
                      ·
                        rfl

theorem cell23_4126568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4126568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126568 prefixEnd_4126568 := by exact prefixLift 4126568
  have htrace : WordTrace (prefixWord ++ tailWord_4126568) baseStart_4126568 baseEnd_4126568 := by
    simpa [prefixWord, tailWord_4126568, baseEnd_4126568] using wordTrace_append hprefix tailTrace_4126568
  have hstable : (prefixWord ++ tailWord_4126568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126568).length < 2 ^ (prefixWord ++ tailWord_4126568).sum := by decide
  have hdescent : baseEnd_4126568 < baseStart_4126568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126599 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 3, 4]
def baseStart_4126599 : Nat := 118140960795 + 4126599 * 2 ^ 59
def prefixEnd_4126599 : Nat := 4983230072969 + 3 ^ 40 * 4126599 * 2
def baseEnd_4126599 : Nat := 706309585121001798711541

theorem tailTrace_4126599 : CollatzResearch.WordTrace tailWord_4126599 prefixEnd_4126599 706309585121001798711541 := by
  unfold tailWord_4126599
  simp only [CollatzResearch.WordTrace]
  refine ⟨150509430377044064844942851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100339620251362709896628567 150509430377044064844942851)
  ·
    refine ⟨225764145565566097267414277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150509430377044064844942851 225764145565566097267414277)
    ·
      refine ⟨42330777293543643237640177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225764145565566097267414277 42330777293543643237640177)
      ·
        refine ⟨31748082970157732428230133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42330777293543643237640177 31748082970157732428230133)
        ·
          refine ⟨2976382778452287415146575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31748082970157732428230133 2976382778452287415146575)
          ·
            refine ⟨4464574167678431122719863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976382778452287415146575 4464574167678431122719863)
            ·
              refine ⟨6696861251517646684079795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464574167678431122719863 6696861251517646684079795)
              ·
                refine ⟨10045291877276470026119693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696861251517646684079795 10045291877276470026119693)
                ·
                  refine ⟨3766984453978676259794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10045291877276470026119693 3766984453978676259794885)
                  ·
                    refine ⟨706309585121001798711541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766984453978676259794885 706309585121001798711541)
                    ·
                      rfl

theorem cell23_4126599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_4126599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126599 prefixEnd_4126599 := by exact prefixLift 4126599
  have htrace : WordTrace (prefixWord ++ tailWord_4126599) baseStart_4126599 baseEnd_4126599 := by
    simpa [prefixWord, tailWord_4126599, baseEnd_4126599] using wordTrace_append hprefix tailTrace_4126599
  have hstable : (prefixWord ++ tailWord_4126599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126599).length < 2 ^ (prefixWord ++ tailWord_4126599).sum := by decide
  have hdescent : baseEnd_4126599 < baseStart_4126599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126612 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 6]
def baseStart_4126612 : Nat := 118140960795 + 4126612 * 2 ^ 59
def prefixEnd_4126612 : Nat := 4983230072969 + 3 ^ 40 * 4126612 * 2
def baseEnd_4126612 : Nat := 235437270067945982808007

theorem tailTrace_4126612 : CollatzResearch.WordTrace tailWord_4126612 prefixEnd_4126612 235437270067945982808007 := by
  unfold tailWord_4126612
  simp only [CollatzResearch.WordTrace]
  refine ⟨75254952262998484032583045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100339936350664645376777393 75254952262998484032583045)
  ·
    refine ⟨14110303549312215756109321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75254952262998484032583045 14110303549312215756109321)
    ·
      refine ⟨10582727661984161817081991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14110303549312215756109321 10582727661984161817081991)
      ·
        refine ⟨15874091492976242725622987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582727661984161817081991 15874091492976242725622987)
        ·
          refine ⟨23811137239464364088434481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874091492976242725622987 23811137239464364088434481)
          ·
            refine ⟨17858352929598273066325861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23811137239464364088434481 17858352929598273066325861)
            ·
              refine ⟨3348441174299676199936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17858352929598273066325861 3348441174299676199936099)
              ·
                refine ⟨5022661761449514299904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348441174299676199936099 5022661761449514299904149)
                ·
                  refine ⟨235437270067945982808007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022661761449514299904149 235437270067945982808007)
                  ·
                    rfl

theorem cell23_4126612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_4126612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126612 prefixEnd_4126612 := by exact prefixLift 4126612
  have htrace : WordTrace (prefixWord ++ tailWord_4126612) baseStart_4126612 baseEnd_4126612 := by
    simpa [prefixWord, tailWord_4126612, baseEnd_4126612] using wordTrace_append hprefix tailTrace_4126612
  have hstable : (prefixWord ++ tailWord_4126612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126612).length < 2 ^ (prefixWord ++ tailWord_4126612).sum := by decide
  have hdescent : baseEnd_4126612 < baseStart_4126612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126755 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_4126755 : Nat := 118140960795 + 4126755 * 2 ^ 59
def prefixEnd_4126755 : Nat := 4983230072969 + 3 ^ 40 * 4126755 * 2
def baseEnd_4126755 : Nat := 2119008858345106785783905

theorem tailTrace_4126755 : CollatzResearch.WordTrace tailWord_4126755 prefixEnd_4126755 2119008858345106785783905 := by
  unfold tailWord_4126755
  simp only [CollatzResearch.WordTrace]
  refine ⟨150515120164478903487621719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100343413442985935658414479 150515120164478903487621719)
  ·
    refine ⟨225772680246718355231432579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150515120164478903487621719 225772680246718355231432579)
    ·
      refine ⟨338659020370077532847148869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225772680246718355231432579 338659020370077532847148869)
      ·
        refine ⟨63498566319389537408840413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338659020370077532847148869 63498566319389537408840413)
        ·
          refine ⟨23811962369771076528315155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63498566319389537408840413 23811962369771076528315155)
          ·
            refine ⟨35717943554656614792472733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23811962369771076528315155 35717943554656614792472733)
            ·
              refine ⟨13394228832996230547177275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35717943554656614792472733 13394228832996230547177275)
              ·
                refine ⟨20091343249494345820765913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394228832996230547177275 20091343249494345820765913)
                ·
                  refine ⟨15068507437120759365574435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20091343249494345820765913 15068507437120759365574435)
                  ·
                    refine ⟨22602761155681139048361653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15068507437120759365574435 22602761155681139048361653)
                    ·
                      refine ⟨2119008858345106785783905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22602761155681139048361653 2119008858345106785783905)
                      ·
                        rfl

theorem cell23_4126755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_4126755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126755 prefixEnd_4126755 := by exact prefixLift 4126755
  have htrace : WordTrace (prefixWord ++ tailWord_4126755) baseStart_4126755 baseEnd_4126755 := by
    simpa [prefixWord, tailWord_4126755, baseEnd_4126755] using wordTrace_append hprefix tailTrace_4126755
  have hstable : (prefixWord ++ tailWord_4126755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126755).length < 2 ^ (prefixWord ++ tailWord_4126755).sum := by decide
  have hdescent : baseEnd_4126755 < baseStart_4126755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126769 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4126769 : Nat := 118140960795 + 4126769 * 2 ^ 59
def prefixEnd_4126769 : Nat := 4983230072969 + 3 ^ 40 * 4126769 * 2
def baseEnd_4126769 : Nat := 2119016047074269731008841

theorem tailTrace_4126769 : CollatzResearch.WordTrace tailWord_4126769 prefixEnd_4126769 2119016047074269731008841 := by
  unfold tailWord_4126769
  simp only [CollatzResearch.WordTrace]
  refine ⟨150515630786428183878631361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100343753857618789252420907 150515630786428183878631361)
  ·
    refine ⟨112886723089821137908973521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150515630786428183878631361 112886723089821137908973521)
    ·
      refine ⟨84665042317365853431730141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112886723089821137908973521 84665042317365853431730141)
      ·
        refine ⟨31749390869012195036898803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84665042317365853431730141 31749390869012195036898803)
        ·
          refine ⟨47624086303518292555348205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31749390869012195036898803 47624086303518292555348205)
          ·
            refine ⟨17859032363819359708255577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47624086303518292555348205 17859032363819359708255577)
            ·
              refine ⟨13394274272864519781191683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17859032363819359708255577 13394274272864519781191683)
              ·
                refine ⟨20091411409296779671787525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394274272864519781191683 20091411409296779671787525)
                ·
                  refine ⟨3767139639243146188460161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20091411409296779671787525 3767139639243146188460161)
                  ·
                    refine ⟨2825354729432359641345121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3767139639243146188460161 2825354729432359641345121)
                    ·
                      refine ⟨2119016047074269731008841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825354729432359641345121 2119016047074269731008841)
                      ·
                        rfl

theorem cell23_4126769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4126769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126769 prefixEnd_4126769 := by exact prefixLift 4126769
  have htrace : WordTrace (prefixWord ++ tailWord_4126769) baseStart_4126769 baseEnd_4126769 := by
    simpa [prefixWord, tailWord_4126769, baseEnd_4126769] using wordTrace_append hprefix tailTrace_4126769
  have hstable : (prefixWord ++ tailWord_4126769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126769).length < 2 ^ (prefixWord ++ tailWord_4126769).sum := by decide
  have hdescent : baseEnd_4126769 < baseStart_4126769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126775 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 7]
def baseStart_4126775 : Nat := 118140960795 + 4126775 * 2 ^ 59
def prefixEnd_4126775 : Nat := 4983230072969 + 3 ^ 40 * 4126775 * 2
def baseEnd_4126775 : Nat := 235446569773132967503757

theorem tailTrace_4126775 : CollatzResearch.WordTrace tailWord_4126775 prefixEnd_4126775 235446569773132967503757 := by
  unfold tailWord_4126775
  simp only [CollatzResearch.WordTrace]
  refine ⟨150515849624406446903349779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100343899749604297935566519 150515849624406446903349779)
  ·
    refine ⟨225773774436609670355024669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150515849624406446903349779 225773774436609670355024669)
    ·
      refine ⟨84665165413728626383134251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225773774436609670355024669 84665165413728626383134251)
      ·
        refine ⟨126997748120592939574701377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84665165413728626383134251 126997748120592939574701377)
        ·
          refine ⟨95248311090444704681026033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126997748120592939574701377 95248311090444704681026033)
          ·
            refine ⟨71436233317833528510769525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95248311090444704681026033 71436233317833528510769525)
            ·
              refine ⟨6697146873546893297884643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71436233317833528510769525 6697146873546893297884643)
              ·
                refine ⟨10045720310320339946826965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697146873546893297884643 10045720310320339946826965)
                ·
                  refine ⟨235446569773132967503757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10045720310320339946826965 235446569773132967503757)
                  ·
                    rfl

theorem cell23_4126775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 7].length) (baseStart_4126775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126775 prefixEnd_4126775 := by exact prefixLift 4126775
  have htrace : WordTrace (prefixWord ++ tailWord_4126775) baseStart_4126775 baseEnd_4126775 := by
    simpa [prefixWord, tailWord_4126775, baseEnd_4126775] using wordTrace_append hprefix tailTrace_4126775
  have hstable : (prefixWord ++ tailWord_4126775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126775).length < 2 ^ (prefixWord ++ tailWord_4126775).sum := by decide
  have hdescent : baseEnd_4126775 < baseStart_4126775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126885 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4126885 : Nat := 118140960795 + 4126885 * 2 ^ 59
def prefixEnd_4126885 : Nat := 4983230072969 + 3 ^ 40 * 4126885 * 2
def baseEnd_4126885 : Nat := 2119075610830191277158307

theorem tailTrace_4126885 : CollatzResearch.WordTrace tailWord_4126885 prefixEnd_4126885 2119075610830191277158307 := by
  unfold tailWord_4126885
  simp only [CollatzResearch.WordTrace]
  refine ⟨150519861654007935689854109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100346574436005290459902739 150519861654007935689854109)
  ·
    refine ⟨56444948120252975883695291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150519861654007935689854109 56444948120252975883695291)
    ·
      refine ⟨84667422180379463825542937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56444948120252975883695291 84667422180379463825542937)
      ·
        refine ⟨63500566635284597869157203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84667422180379463825542937 63500566635284597869157203)
        ·
          refine ⟨95250849952926896803735805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63500566635284597869157203 95250849952926896803735805)
          ·
            refine ⟨35719068732347586301400927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95250849952926896803735805 35719068732347586301400927)
            ·
              refine ⟨53578603098521379452101391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35719068732347586301400927 53578603098521379452101391)
              ·
                refine ⟨80367904647782069178152087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53578603098521379452101391 80367904647782069178152087)
                ·
                  refine ⟨120551856971673103767228131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80367904647782069178152087 120551856971673103767228131)
                  ·
                    refine ⟨180827785457509655650842197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120551856971673103767228131 180827785457509655650842197)
                    ·
                      refine ⟨2119075610830191277158307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180827785457509655650842197 2119075610830191277158307)
                      ·
                        rfl

theorem cell23_4126885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4126885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126885 prefixEnd_4126885 := by exact prefixLift 4126885
  have htrace : WordTrace (prefixWord ++ tailWord_4126885) baseStart_4126885 baseEnd_4126885 := by
    simpa [prefixWord, tailWord_4126885, baseEnd_4126885] using wordTrace_append hprefix tailTrace_4126885
  have hstable : (prefixWord ++ tailWord_4126885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126885).length < 2 ^ (prefixWord ++ tailWord_4126885).sum := by decide
  have hdescent : baseEnd_4126885 < baseStart_4126885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126936 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_4126936 : Nat := 118140960795 + 4126936 * 2 ^ 59
def prefixEnd_4126936 : Nat := 4983230072969 + 3 ^ 40 * 4126936 * 2
def baseEnd_4126936 : Nat := 2119101798343570577620573

theorem tailTrace_4126936 : CollatzResearch.WordTrace tailWord_4126936 prefixEnd_4126936 2119101798343570577620573 := by
  unfold tailWord_4126936
  simp only [CollatzResearch.WordTrace]
  refine ⟨75260860888411585699980331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100347814517882114266640441 75260860888411585699980331)
  ·
    refine ⟨112891291332617378549970497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75260860888411585699980331 112891291332617378549970497)
    ·
      refine ⟨84668468499463033912477873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112891291332617378549970497 84668468499463033912477873)
      ·
        refine ⟨63501351374597275434358405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84668468499463033912477873 63501351374597275434358405)
        ·
          refine ⟨11906503382736989143942201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63501351374597275434358405 11906503382736989143942201)
          ·
            refine ⟨8929877537052741857956651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11906503382736989143942201 8929877537052741857956651)
            ·
              refine ⟨13394816305579112786934977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929877537052741857956651 13394816305579112786934977)
              ·
                refine ⟨10046112229184334590201233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13394816305579112786934977 10046112229184334590201233)
                ·
                  refine ⟨7534584171888250942650925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046112229184334590201233 7534584171888250942650925)
                  ·
                    refine ⟨2825469064458094103494097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7534584171888250942650925 2825469064458094103494097)
                    ·
                      refine ⟨2119101798343570577620573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825469064458094103494097 2119101798343570577620573)
                      ·
                        rfl

theorem cell23_4126936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_4126936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126936 prefixEnd_4126936 := by exact prefixLift 4126936
  have htrace : WordTrace (prefixWord ++ tailWord_4126936) baseStart_4126936 baseEnd_4126936 := by
    simpa [prefixWord, tailWord_4126936, baseEnd_4126936] using wordTrace_append hprefix tailTrace_4126936
  have hstable : (prefixWord ++ tailWord_4126936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126936).length < 2 ^ (prefixWord ++ tailWord_4126936).sum := by decide
  have hdescent : baseEnd_4126936 < baseStart_4126936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126966 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4126966 : Nat := 118140960795 + 4126966 * 2 ^ 59
def prefixEnd_4126966 : Nat := 4983230072969 + 3 ^ 40 * 4126966 * 2
def baseEnd_4126966 : Nat := 2119117202763205460245435

theorem tailTrace_4126966 : CollatzResearch.WordTrace tailWord_4126966 prefixEnd_4126966 2119117202763205460245435 := by
  unfold tailWord_4126966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407675997919655407722047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100348543977809657682368501 9407675997919655407722047)
  ·
    refine ⟨14111513996879483111583071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407675997919655407722047 14111513996879483111583071)
    ·
      refine ⟨21167270995319224667374607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111513996879483111583071 21167270995319224667374607)
      ·
        refine ⟨31750906492978837001061911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167270995319224667374607 31750906492978837001061911)
        ·
          refine ⟨47626359739468255501592867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31750906492978837001061911 47626359739468255501592867)
          ·
            refine ⟨71439539609202383252389301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47626359739468255501592867 71439539609202383252389301)
            ·
              refine ⟨6697456838362723429911497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71439539609202383252389301 6697456838362723429911497)
              ·
                refine ⟨5023092628772042572433623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697456838362723429911497 5023092628772042572433623)
                ·
                  refine ⟨7534638943158063858650435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023092628772042572433623 7534638943158063858650435)
                  ·
                    refine ⟨11301958414737095787975653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534638943158063858650435 11301958414737095787975653)
                    ·
                      refine ⟨2119117202763205460245435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11301958414737095787975653 2119117202763205460245435)
                      ·
                        rfl

theorem cell23_4126966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4126966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126966 prefixEnd_4126966 := by exact prefixLift 4126966
  have htrace : WordTrace (prefixWord ++ tailWord_4126966) baseStart_4126966 baseEnd_4126966 := by
    simpa [prefixWord, tailWord_4126966, baseEnd_4126966] using wordTrace_append hprefix tailTrace_4126966
  have hstable : (prefixWord ++ tailWord_4126966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126966).length < 2 ^ (prefixWord ++ tailWord_4126966).sum := by decide
  have hdescent : baseEnd_4126966 < baseStart_4126966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126969 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_4126969 : Nat := 118140960795 + 4126969 * 2 ^ 59
def prefixEnd_4126969 : Nat := 4983230072969 + 3 ^ 40 * 4126969 * 2
def baseEnd_4126969 : Nat := 2119118743205168948507921

theorem tailTrace_4126969 : CollatzResearch.WordTrace tailWord_4126969 prefixEnd_4126969 2119118743205168948507921 := by
  unfold tailWord_4126969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150522925385703618035911961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100348616923802412023941307 150522925385703618035911961)
  ·
    refine ⟨112892194039277713526933971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150522925385703618035911961 112892194039277713526933971)
    ·
      refine ⟨169338291058916570290400957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112892194039277713526933971 169338291058916570290400957)
      ·
        refine ⟨63501859147093713858900359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169338291058916570290400957 63501859147093713858900359)
        ·
          refine ⟨95252788720640570788350539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63501859147093713858900359 95252788720640570788350539)
          ·
            refine ⟨142879183080960856182525809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95252788720640570788350539 142879183080960856182525809)
            ·
              refine ⟨107159387310720642136894357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142879183080960856182525809 107159387310720642136894357)
              ·
                refine ⟨5023096280190030100166923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107159387310720642136894357 5023096280190030100166923)
                ·
                  refine ⟨7534644420285045150250385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023096280190030100166923 7534644420285045150250385)
                  ·
                    refine ⟨5650983315213783862687789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534644420285045150250385 5650983315213783862687789)
                    ·
                      refine ⟨2119118743205168948507921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5650983315213783862687789 2119118743205168948507921)
                      ·
                        rfl

theorem cell23_4126969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_4126969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126969 prefixEnd_4126969 := by exact prefixLift 4126969
  have htrace : WordTrace (prefixWord ++ tailWord_4126969) baseStart_4126969 baseEnd_4126969 := by
    simpa [prefixWord, tailWord_4126969, baseEnd_4126969] using wordTrace_append hprefix tailTrace_4126969
  have hstable : (prefixWord ++ tailWord_4126969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126969).length < 2 ^ (prefixWord ++ tailWord_4126969).sum := by decide
  have hdescent : baseEnd_4126969 < baseStart_4126969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4126972 : List Nat := [2, 2, 2, 1, 4, 1, 2, 9]
def baseStart_4126972 : Nat := 118140960795 + 4126972 * 2 ^ 59
def prefixEnd_4126972 : Nat := 4983230072969 + 3 ^ 40 * 4126972 * 2
def baseEnd_4126972 : Nat := 78485936431375275435941

theorem tailTrace_4126972 : CollatzResearch.WordTrace tailWord_4126972 prefixEnd_4126972 78485936431375275435941 := by
  unfold tailWord_4126972
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261517402346374774135585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100348689869795166365514113 75261517402346374774135585)
  ·
    refine ⟨56446138051759781080601689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75261517402346374774135585 56446138051759781080601689)
    ·
      refine ⟨42334603538819835810451267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56446138051759781080601689 42334603538819835810451267)
      ·
        refine ⟨63501905308229753715676901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42334603538819835810451267 63501905308229753715676901)
        ·
          refine ⟨11906607245293078821689419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63501905308229753715676901 11906607245293078821689419)
          ·
            refine ⟨17859910867939618232534129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906607245293078821689419 17859910867939618232534129)
            ·
              refine ⟨13394933150954713674400597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17859910867939618232534129 13394933150954713674400597)
              ·
                refine ⟨78485936431375275435941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13394933150954713674400597 78485936431375275435941)
                ·
                  rfl

theorem cell23_4126972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 9].length) (baseStart_4126972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4126972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4126972 prefixEnd_4126972 := by exact prefixLift 4126972
  have htrace : WordTrace (prefixWord ++ tailWord_4126972) baseStart_4126972 baseEnd_4126972 := by
    simpa [prefixWord, tailWord_4126972, baseEnd_4126972] using wordTrace_append hprefix tailTrace_4126972
  have hstable : (prefixWord ++ tailWord_4126972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4126972).length < 2 ^ (prefixWord ++ tailWord_4126972).sum := by decide
  have hdescent : baseEnd_4126972 < baseStart_4126972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4126972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127006 : List Nat := [4, 3, 2, 1, 1, 1, 3, 8]
def baseStart_4127006 : Nat := 118140960795 + 4127006 * 2 ^ 59
def prefixEnd_4127006 : Nat := 4983230072969 + 3 ^ 40 * 4127006 * 2
def baseEnd_4127006 : Nat := 78486583036643900138713

theorem tailTrace_4127006 : CollatzResearch.WordTrace tailWord_4127006 prefixEnd_4127006 78486583036643900138713 := by
  unfold tailWord_4127006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815534360821196669376109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100349516591046382236672581 18815534360821196669376109)
  ·
    refine ⟨7055825385307948751016041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18815534360821196669376109 7055825385307948751016041)
    ·
      refine ⟨5291869038980961563262031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055825385307948751016041 5291869038980961563262031)
      ·
        refine ⟨7937803558471442344893047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291869038980961563262031 7937803558471442344893047)
        ·
          refine ⟨11906705337707163517339571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937803558471442344893047 11906705337707163517339571)
          ·
            refine ⟨17860058006560745276009357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906705337707163517339571 17860058006560745276009357)
            ·
              refine ⟨6697521752460279478503509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17860058006560745276009357 6697521752460279478503509)
              ·
                refine ⟨78486583036643900138713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6697521752460279478503509 78486583036643900138713)
                ·
                  rfl

theorem cell23_4127006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_4127006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127006 prefixEnd_4127006 := by exact prefixLift 4127006
  have htrace : WordTrace (prefixWord ++ tailWord_4127006) baseStart_4127006 baseEnd_4127006 := by
    simpa [prefixWord, tailWord_4127006, baseEnd_4127006] using wordTrace_append hprefix tailTrace_4127006
  have hstable : (prefixWord ++ tailWord_4127006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127006).length < 2 ^ (prefixWord ++ tailWord_4127006).sum := by decide
  have hdescent : baseEnd_4127006 < baseStart_4127006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127043 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 1, 3, 2]
def baseStart_4127043 : Nat := 118140960795 + 4127043 * 2 ^ 59
def prefixEnd_4127043 : Nat := 4983230072969 + 3 ^ 40 * 4127043 * 2
def baseEnd_4127043 : Nat := 2119156740773601658982581

theorem tailTrace_4127043 : CollatzResearch.WordTrace tailWord_4127043 prefixEnd_4127043 2119156740773601658982581 := by
  unfold tailWord_4127043
  simp only [CollatzResearch.WordTrace]
  refine ⟨150525624387435528674105783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100350416258290352449403855 150525624387435528674105783)
  ·
    refine ⟨225788436581153293011158675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150525624387435528674105783 225788436581153293011158675)
    ·
      refine ⟨338682654871729939516738013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225788436581153293011158675 338682654871729939516738013)
      ·
        refine ⟨127005995576898727318776755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338682654871729939516738013 127005995576898727318776755)
        ·
          refine ⟨190508993365348090978165133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127005995576898727318776755 190508993365348090978165133)
          ·
            refine ⟨71440872512005534116811925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190508993365348090978165133 71440872512005534116811925)
            ·
              refine ⟨3348790899000259411725559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71440872512005534116811925 3348790899000259411725559)
              ·
                refine ⟨5023186348500389117588339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348790899000259411725559 5023186348500389117588339)
                ·
                  refine ⟨7534779522750583676382509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023186348500389117588339 7534779522750583676382509)
                  ·
                    refine ⟨2825542321031468878643441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7534779522750583676382509 2825542321031468878643441)
                    ·
                      refine ⟨2119156740773601658982581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825542321031468878643441 2119156740773601658982581)
                      ·
                        rfl

theorem cell23_4127043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_4127043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127043 prefixEnd_4127043 := by exact prefixLift 4127043
  have htrace : WordTrace (prefixWord ++ tailWord_4127043) baseStart_4127043 baseEnd_4127043 := by
    simpa [prefixWord, tailWord_4127043, baseEnd_4127043] using wordTrace_append hprefix tailTrace_4127043
  have hstable : (prefixWord ++ tailWord_4127043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127043).length < 2 ^ (prefixWord ++ tailWord_4127043).sum := by decide
  have hdescent : baseEnd_4127043 < baseStart_4127043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127079 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 7]
def baseStart_4127079 : Nat := 118140960795 + 4127079 * 2 ^ 59
def prefixEnd_4127079 : Nat := 4983230072969 + 3 ^ 40 * 4127079 * 2
def baseEnd_4127079 : Nat := 235463914008573724236935

theorem tailTrace_4127079 : CollatzResearch.WordTrace tailWord_4127079 prefixEnd_4127079 235463914008573724236935 := by
  unfold tailWord_4127079
  simp only [CollatzResearch.WordTrace]
  refine ⟨150526937415305106822416291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100351291610203404548277527 150526937415305106822416291)
  ·
    refine ⟨225790406122957660233624437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150526937415305106822416291 225790406122957660233624437)
    ·
      refine ⟨21167850574027280646902291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225790406122957660233624437 21167850574027280646902291)
      ·
        refine ⟨31751775861040920970353437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167850574027280646902291 31751775861040920970353437)
        ·
          refine ⟨11906915947890345363882539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31751775861040920970353437 11906915947890345363882539)
          ·
            refine ⟨17860373921835518045823809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906915947890345363882539 17860373921835518045823809)
            ·
              refine ⟨13395280441376638534367857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17860373921835518045823809 13395280441376638534367857)
              ·
                refine ⟨10046460331032478900775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395280441376638534367857 10046460331032478900775893)
                ·
                  refine ⟨235463914008573724236935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10046460331032478900775893 235463914008573724236935)
                  ·
                    rfl

theorem cell23_4127079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 7].length) (baseStart_4127079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127079 prefixEnd_4127079 := by exact prefixLift 4127079
  have htrace : WordTrace (prefixWord ++ tailWord_4127079) baseStart_4127079 baseEnd_4127079 := by
    simpa [prefixWord, tailWord_4127079, baseEnd_4127079] using wordTrace_append hprefix tailTrace_4127079
  have hstable : (prefixWord ++ tailWord_4127079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127079).length < 2 ^ (prefixWord ++ tailWord_4127079).sum := by decide
  have hdescent : baseEnd_4127079 < baseStart_4127079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127113 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 5]
def baseStart_4127113 : Nat := 118140960795 + 4127113 * 2 ^ 59
def prefixEnd_4127113 : Nat := 4983230072969 + 3 ^ 40 * 4127113 * 2
def baseEnd_4127113 : Nat := 235465853824379598345251

theorem tailTrace_4127113 : CollatzResearch.WordTrace tailWord_4127113 prefixEnd_4127113 235465853824379598345251 := by
  unfold tailWord_4127113
  simp only [CollatzResearch.WordTrace]
  refine ⟨150528177497181930629153993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100352118331454620419435995 150528177497181930629153993)
  ·
    refine ⟨112896133122886447971865495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150528177497181930629153993 112896133122886447971865495)
    ·
      refine ⟨169344199684329671957798243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112896133122886447971865495 169344199684329671957798243)
      ·
        refine ⟨254016299526494507936697365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169344199684329671957798243 254016299526494507936697365)
        ·
          refine ⟨11907014040304430059532689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254016299526494507936697365 11907014040304430059532689)
          ·
            refine ⟨8930260530228322544649517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11907014040304430059532689 8930260530228322544649517)
            ·
              refine ⟨3348847698835620954243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8930260530228322544649517 3348847698835620954243569)
              ·
                refine ⟨2511635774126715715682677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348847698835620954243569 2511635774126715715682677)
                ·
                  refine ⟨235465853824379598345251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511635774126715715682677 235465853824379598345251)
                  ·
                    rfl

theorem cell23_4127113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 5].length) (baseStart_4127113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127113 prefixEnd_4127113 := by exact prefixLift 4127113
  have htrace : WordTrace (prefixWord ++ tailWord_4127113) baseStart_4127113 baseEnd_4127113 := by
    simpa [prefixWord, tailWord_4127113, baseEnd_4127113] using wordTrace_append hprefix tailTrace_4127113
  have hstable : (prefixWord ++ tailWord_4127113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127113).length < 2 ^ (prefixWord ++ tailWord_4127113).sum := by decide
  have hdescent : baseEnd_4127113 < baseStart_4127113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127124 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4127124 : Nat := 118140960795 + 4127124 * 2 ^ 59
def prefixEnd_4127124 : Nat := 4983230072969 + 3 ^ 40 * 4127124 * 2
def baseEnd_4127124 : Nat := 2119198332706615842069709

theorem tailTrace_4127124 : CollatzResearch.WordTrace tailWord_4127124 prefixEnd_4127124 2119198332706615842069709 := by
  unfold tailWord_4127124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75264289350071039753902213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100352385800094719671869617 75264289350071039753902213)
  ·
    refine ⟨14112054253138319953856665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75264289350071039753902213 14112054253138319953856665)
    ·
      refine ⟨10584040689853739965392499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14112054253138319953856665 10584040689853739965392499)
      ·
        refine ⟨15876061034780609948088749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584040689853739965392499 15876061034780609948088749)
        ·
          refine ⟨5953522888042728730533281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15876061034780609948088749 5953522888042728730533281)
          ·
            refine ⟨4465142166032046547899961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953522888042728730533281 4465142166032046547899961)
            ·
              refine ⟨3348856624524034910924971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465142166032046547899961 3348856624524034910924971)
              ·
                refine ⟨5023284936786052366387457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348856624524034910924971 5023284936786052366387457)
                ·
                  refine ⟨3767463702589539274790593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5023284936786052366387457 3767463702589539274790593)
                  ·
                    refine ⟨2825597776942154456092945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3767463702589539274790593 2825597776942154456092945)
                    ·
                      refine ⟨2119198332706615842069709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825597776942154456092945 2119198332706615842069709)
                      ·
                        rfl

theorem cell23_4127124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4127124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127124 prefixEnd_4127124 := by exact prefixLift 4127124
  have htrace : WordTrace (prefixWord ++ tailWord_4127124) baseStart_4127124 baseEnd_4127124 := by
    simpa [prefixWord, tailWord_4127124, baseEnd_4127124] using wordTrace_append hprefix tailTrace_4127124
  have hstable : (prefixWord ++ tailWord_4127124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127124).length < 2 ^ (prefixWord ++ tailWord_4127124).sum := by decide
  have hdescent : baseEnd_4127124 < baseStart_4127124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127129 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_4127129 : Nat := 118140960795 + 4127129 * 2 ^ 59
def prefixEnd_4127129 : Nat := 4983230072969 + 3 ^ 40 * 4127129 * 2
def baseEnd_4127129 : Nat := 2119200900109888322507185

theorem tailTrace_4127129 : CollatzResearch.WordTrace tailWord_4127129 prefixEnd_4127129 2119200900109888322507185 := by
  unfold tailWord_4127129
  simp only [CollatzResearch.WordTrace]
  refine ⟨150528761065123965361736441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100352507376749310241157627 150528761065123965361736441)
  ·
    refine ⟨112896570798842974021302331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150528761065123965361736441 112896570798842974021302331)
    ·
      refine ⟨169344856198264461031953497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112896570798842974021302331 169344856198264461031953497)
      ·
        refine ⟨127008642148698345773965123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169344856198264461031953497 127008642148698345773965123)
        ·
          refine ⟨190512963223047518660947685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127008642148698345773965123 190512963223047518660947685)
          ·
            refine ⟨35721180604321409748927691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190512963223047518660947685 35721180604321409748927691)
            ·
              refine ⟨53581770906482114623391537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35721180604321409748927691 53581770906482114623391537)
              ·
                refine ⟨40186328179861585967543653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53581770906482114623391537 40186328179861585967543653)
                ·
                  refine ⟨7534936533724047368914435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40186328179861585967543653 7534936533724047368914435)
                  ·
                    refine ⟨11302404800586071053371653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534936533724047368914435 11302404800586071053371653)
                    ·
                      refine ⟨2119200900109888322507185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11302404800586071053371653 2119200900109888322507185)
                      ·
                        rfl

theorem cell23_4127129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_4127129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127129 prefixEnd_4127129 := by exact prefixLift 4127129
  have htrace : WordTrace (prefixWord ++ tailWord_4127129) baseStart_4127129 baseEnd_4127129 := by
    simpa [prefixWord, tailWord_4127129, baseEnd_4127129] using wordTrace_append hprefix tailTrace_4127129
  have hstable : (prefixWord ++ tailWord_4127129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127129).length < 2 ^ (prefixWord ++ tailWord_4127129).sum := by decide
  have hdescent : baseEnd_4127129 < baseStart_4127129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127179 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3]
def baseStart_4127179 : Nat := 118140960795 + 4127179 * 2 ^ 59
def prefixEnd_4127179 : Nat := 4983230072969 + 3 ^ 40 * 4127179 * 2
def baseEnd_4127179 : Nat := 2119226574142613126881955

theorem tailTrace_4127179 : CollatzResearch.WordTrace tailWord_4127179 prefixEnd_4127179 2119226574142613126881955 := by
  unfold tailWord_4127179
  simp only [CollatzResearch.WordTrace]
  refine ⟨150530584714942823901056591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100353723143295215934037727 150530584714942823901056591)
  ·
    refine ⟨225795877072414235851584887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150530584714942823901056591 225795877072414235851584887)
    ·
      refine ⟨338693815608621353777377331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225795877072414235851584887 338693815608621353777377331)
      ·
        refine ⟨508040723412932030666065997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338693815608621353777377331 508040723412932030666065997)
        ·
          refine ⟨190515271279849511499774749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508040723412932030666065997 190515271279849511499774749)
          ·
            refine ⟨71443226729943566812415531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190515271279849511499774749 71443226729943566812415531)
            ·
              refine ⟨107164840094915350218623297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71443226729943566812415531 107164840094915350218623297)
              ·
                refine ⟨80373630071186512663967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107164840094915350218623297 80373630071186512663967473)
                ·
                  refine ⟨60280222553389884497975605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80373630071186512663967473 60280222553389884497975605)
                  ·
                    refine ⟨5651270864380301671685213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60280222553389884497975605 5651270864380301671685213)
                    ·
                      refine ⟨2119226574142613126881955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5651270864380301671685213 2119226574142613126881955)
                      ·
                        rfl

theorem cell23_4127179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].length) (baseStart_4127179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127179 prefixEnd_4127179 := by exact prefixLift 4127179
  have htrace : WordTrace (prefixWord ++ tailWord_4127179) baseStart_4127179 baseEnd_4127179 := by
    simpa [prefixWord, tailWord_4127179, baseEnd_4127179] using wordTrace_append hprefix tailTrace_4127179
  have hstable : (prefixWord ++ tailWord_4127179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127179).length < 2 ^ (prefixWord ++ tailWord_4127179).sum := by decide
  have hdescent : baseEnd_4127179 < baseStart_4127179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127216 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_4127216 : Nat := 118140960795 + 4127216 * 2 ^ 59
def prefixEnd_4127216 : Nat := 4983230072969 + 3 ^ 40 * 4127216 * 2
def baseEnd_4127216 : Nat := 706415190975609827373095

theorem tailTrace_4127216 : CollatzResearch.WordTrace tailWord_4127216 prefixEnd_4127216 706415190975609827373095 := by
  unfold tailWord_4127216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75265967107904389610076751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100354622810539186146769001 75265967107904389610076751)
  ·
    refine ⟨112898950661856584415115127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75265967107904389610076751 112898950661856584415115127)
    ·
      refine ⟨169348425992784876622672691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112898950661856584415115127 169348425992784876622672691)
      ·
        refine ⟨254022638989177314934009037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169348425992784876622672691 254022638989177314934009037)
        ·
          refine ⟨95258489620941493100253389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254022638989177314934009037 95258489620941493100253389)
          ·
            refine ⟨35721933607853059912595021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95258489620941493100253389 35721933607853059912595021)
            ·
              refine ⟨13395725102944897467223133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35721933607853059912595021 13395725102944897467223133)
              ·
                refine ⟨5023396913604336550208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13395725102944897467223133 5023396913604336550208675)
                ·
                  refine ⟨7535095370406504825313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023396913604336550208675 7535095370406504825313013)
                  ·
                    refine ⟨706415190975609827373095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7535095370406504825313013 706415190975609827373095)
                    ·
                      rfl

theorem cell23_4127216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_4127216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127216 prefixEnd_4127216 := by exact prefixLift 4127216
  have htrace : WordTrace (prefixWord ++ tailWord_4127216) baseStart_4127216 baseEnd_4127216 := by
    simpa [prefixWord, tailWord_4127216, baseEnd_4127216] using wordTrace_append hprefix tailTrace_4127216
  have hstable : (prefixWord ++ tailWord_4127216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127216).length < 2 ^ (prefixWord ++ tailWord_4127216).sum := by decide
  have hdescent : baseEnd_4127216 < baseStart_4127216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127253 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_4127253 : Nat := 118140960795 + 4127253 * 2 ^ 59
def prefixEnd_4127253 : Nat := 4983230072969 + 3 ^ 40 * 4127253 * 2
def baseEnd_4127253 : Nat := 2119264571711045837356615

theorem tailTrace_4127253 : CollatzResearch.WordTrace tailWord_4127253 prefixEnd_4127253 2119264571711045837356615 := by
  unfold tailWord_4127253
  simp only [CollatzResearch.WordTrace]
  refine ⟨150533283716674734539250413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100355522477783156359500275 150533283716674734539250413)
  ·
    refine ⟨56449981393753025452218905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150533283716674734539250413 56449981393753025452218905)
    ·
      refine ⟨42337486045314769089164179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56449981393753025452218905 42337486045314769089164179)
      ·
        refine ⟨63506229067972153633746269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42337486045314769089164179 63506229067972153633746269)
        ·
          refine ⟨23814835900489557612654851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63506229067972153633746269 23814835900489557612654851)
          ·
            refine ⟨35722253850734336418982277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23814835900489557612654851 35722253850734336418982277)
            ·
              refine ⟨6697922597012688078559177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35722253850734336418982277 6697922597012688078559177)
              ·
                refine ⟨5023441947759516058919383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697922597012688078559177 5023441947759516058919383)
                ·
                  refine ⟨7535162921639274088379075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5023441947759516058919383 7535162921639274088379075)
                  ·
                    refine ⟨11302744382458911132568613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7535162921639274088379075 11302744382458911132568613)
                    ·
                      refine ⟨2119264571711045837356615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11302744382458911132568613 2119264571711045837356615)
                      ·
                        rfl

theorem cell23_4127253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_4127253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127253 prefixEnd_4127253 := by exact prefixLift 4127253
  have htrace : WordTrace (prefixWord ++ tailWord_4127253) baseStart_4127253 baseEnd_4127253 := by
    simpa [prefixWord, tailWord_4127253, baseEnd_4127253] using wordTrace_append hprefix tailTrace_4127253
  have hstable : (prefixWord ++ tailWord_4127253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127253).length < 2 ^ (prefixWord ++ tailWord_4127253).sum := by decide
  have hdescent : baseEnd_4127253 < baseStart_4127253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127264 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4127264 : Nat := 118140960795 + 4127264 * 2 ^ 59
def prefixEnd_4127264 : Nat := 4983230072969 + 3 ^ 40 * 4127264 * 2
def baseEnd_4127264 : Nat := 2119270219998245294319065

theorem tailTrace_4127264 : CollatzResearch.WordTrace tailWord_4127264 prefixEnd_4127264 2119270219998245294319065 := by
  unfold tailWord_4127264
  simp only [CollatzResearch.WordTrace]
  refine ⟨75266842459817441708950423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100355789946423255611933897 75266842459817441708950423)
  ·
    refine ⟨112900263689726162563425635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75266842459817441708950423 112900263689726162563425635)
    ·
      refine ⟨169350395534589243845138453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112900263689726162563425635 169350395534589243845138453)
      ·
        refine ⟨7938299790683870805240865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169350395534589243845138453 7938299790683870805240865)
        ·
          refine ⟨5953724843012903103930649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7938299790683870805240865 5953724843012903103930649)
          ·
            refine ⟨4465293632259677327947987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953724843012903103930649 4465293632259677327947987)
            ·
              refine ⟨6697940448389515991921981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465293632259677327947987 6697940448389515991921981)
              ·
                refine ⟨2511727668146068496970743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6697940448389515991921981 2511727668146068496970743)
                ·
                  refine ⟨3767591502219102745456115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511727668146068496970743 3767591502219102745456115)
                  ·
                    refine ⟨5651387253328654118184173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3767591502219102745456115 5651387253328654118184173)
                    ·
                      refine ⟨2119270219998245294319065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5651387253328654118184173 2119270219998245294319065)
                      ·
                        rfl

theorem cell23_4127264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4127264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127264 prefixEnd_4127264 := by exact prefixLift 4127264
  have htrace : WordTrace (prefixWord ++ tailWord_4127264) baseStart_4127264 baseEnd_4127264 := by
    simpa [prefixWord, tailWord_4127264, baseEnd_4127264] using wordTrace_append hprefix tailTrace_4127264
  have hstable : (prefixWord ++ tailWord_4127264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127264).length < 2 ^ (prefixWord ++ tailWord_4127264).sum := by decide
  have hdescent : baseEnd_4127264 < baseStart_4127264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127266 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4127266 : Nat := 118140960795 + 4127266 * 2 ^ 59
def prefixEnd_4127266 : Nat := 4983230072969 + 3 ^ 40 * 4127266 * 2
def baseEnd_4127266 : Nat := 2119271246959554286494055

theorem tailTrace_4127266 : CollatzResearch.WordTrace tailWord_4127266 prefixEnd_4127266 2119271246959554286494055 := by
  unfold tailWord_4127266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37633439466406909439868413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100355838577085091839649101 37633439466406909439868413)
  ·
    refine ⟨14112539799902591039950655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37633439466406909439868413 14112539799902591039950655)
    ·
      refine ⟨21168809699853886559925983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14112539799902591039950655 21168809699853886559925983)
      ·
        refine ⟨31753214549780829839888975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21168809699853886559925983 31753214549780829839888975)
        ·
          refine ⟨47629821824671244759833463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31753214549780829839888975 47629821824671244759833463)
          ·
            refine ⟨71444732737006867139750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47629821824671244759833463 71444732737006867139750195)
            ·
              refine ⟨107167099105510300709625293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71444732737006867139750195 107167099105510300709625293)
              ·
                refine ⟨40187662164566362766109485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107167099105510300709625293 40187662164566362766109485)
                ·
                  refine ⟨15070373311712386037291057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40187662164566362766109485 15070373311712386037291057)
                  ·
                    refine ⟨11302779983784289527968293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15070373311712386037291057 11302779983784289527968293)
                    ·
                      refine ⟨2119271246959554286494055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11302779983784289527968293 2119271246959554286494055)
                      ·
                        rfl

theorem cell23_4127266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4127266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127266 prefixEnd_4127266 := by exact prefixLift 4127266
  have htrace : WordTrace (prefixWord ++ tailWord_4127266) baseStart_4127266 baseEnd_4127266 := by
    simpa [prefixWord, tailWord_4127266, baseEnd_4127266] using wordTrace_append hprefix tailTrace_4127266
  have hstable : (prefixWord ++ tailWord_4127266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127266).length < 2 ^ (prefixWord ++ tailWord_4127266).sum := by decide
  have hdescent : baseEnd_4127266 < baseStart_4127266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127297 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4127297 : Nat := 118140960795 + 4127297 * 2 ^ 59
def prefixEnd_4127297 : Nat := 4983230072969 + 3 ^ 40 * 4127297 * 2
def baseEnd_4127297 : Nat := 706429054953281221735471

theorem tailTrace_4127297 : CollatzResearch.WordTrace tailWord_4127297 prefixEnd_4127297 706429054953281221735471 := by
  unfold tailWord_4127297
  simp only [CollatzResearch.WordTrace]
  refine ⟨150534888528515330053852145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100356592352343553369234763 150534888528515330053852145)
  ·
    refine ⟨112901166396386497540389109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150534888528515330053852145 112901166396386497540389109)
    ·
      refine ⟨10584484349661234144411479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112901166396386497540389109 10584484349661234144411479)
      ·
        refine ⟨15876726524491851216617219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584484349661234144411479 15876726524491851216617219)
        ·
          refine ⟨23815089786737776824925829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876726524491851216617219 23815089786737776824925829)
          ·
            refine ⟨4465329335013333154673593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23815089786737776824925829 4465329335013333154673593)
            ·
              refine ⟨3348997001259999866005195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465329335013333154673593 3348997001259999866005195)
              ·
                refine ⟨5023495501889999799007793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348997001259999866005195 5023495501889999799007793)
                ·
                  refine ⟨3767621626417499849255845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5023495501889999799007793 3767621626417499849255845)
                  ·
                    refine ⟨706429054953281221735471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767621626417499849255845 706429054953281221735471)
                    ·
                      rfl

theorem cell23_4127297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4127297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127297 prefixEnd_4127297 := by exact prefixLift 4127297
  have htrace : WordTrace (prefixWord ++ tailWord_4127297) baseStart_4127297 baseEnd_4127297 := by
    simpa [prefixWord, tailWord_4127297, baseEnd_4127297] using wordTrace_append hprefix tailTrace_4127297
  have hstable : (prefixWord ++ tailWord_4127297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127297).length < 2 ^ (prefixWord ++ tailWord_4127297).sum := by decide
  have hdescent : baseEnd_4127297 < baseStart_4127297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127356 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_4127356 : Nat := 118140960795 + 4127356 * 2 ^ 59
def prefixEnd_4127356 : Nat := 4983230072969 + 3 ^ 40 * 4127356 * 2
def baseEnd_4127356 : Nat := 2119317460218458934368641

theorem tailTrace_4127356 : CollatzResearch.WordTrace tailWord_4127356 prefixEnd_4127356 2119317460218458934368641 := by
  unfold tailWord_4127356
  simp only [CollatzResearch.WordTrace]
  refine ⟨75268520217650791565124961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100358026956867722086833281 75268520217650791565124961)
  ·
    refine ⟨56451390163238093673843721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75268520217650791565124961 56451390163238093673843721)
    ·
      refine ⟨42338542622428570255382791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56451390163238093673843721 42338542622428570255382791)
      ·
        refine ⟨63507813933642855383074187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42338542622428570255382791 63507813933642855383074187)
        ·
          refine ⟨95261720900464283074611281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63507813933642855383074187 95261720900464283074611281)
          ·
            refine ⟨71446290675348212305958461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95261720900464283074611281 71446290675348212305958461)
            ·
              refine ⟨26792359003255579614734423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71446290675348212305958461 26792359003255579614734423)
              ·
                refine ⟨40188538504883369422101635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26792359003255579614734423 40188538504883369422101635)
                ·
                  refine ⟨60282807757325054133152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40188538504883369422101635 60282807757325054133152453)
                  ·
                    refine ⟨11303026454498447649966085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60282807757325054133152453 11303026454498447649966085)
                    ·
                      refine ⟨2119317460218458934368641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11303026454498447649966085 2119317460218458934368641)
                      ·
                        rfl

theorem cell23_4127356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_4127356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127356 prefixEnd_4127356 := by exact prefixLift 4127356
  have htrace : WordTrace (prefixWord ++ tailWord_4127356) baseStart_4127356 baseEnd_4127356 := by
    simpa [prefixWord, tailWord_4127356, baseEnd_4127356] using wordTrace_append hprefix tailTrace_4127356
  have hstable : (prefixWord ++ tailWord_4127356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127356).length < 2 ^ (prefixWord ++ tailWord_4127356).sum := by decide
  have hdescent : baseEnd_4127356 < baseStart_4127356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127360 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2]
def baseStart_4127360 : Nat := 118140960795 + 4127360 * 2 ^ 59
def prefixEnd_4127360 : Nat := 4983230072969 + 3 ^ 40 * 4127360 * 2
def baseEnd_4127360 : Nat := 2119319514141076918718623

theorem tailTrace_4127360 : CollatzResearch.WordTrace tailWord_4127360 prefixEnd_4127360 2119319514141076918718623 := by
  unfold tailWord_4127360
  simp only [CollatzResearch.WordTrace]
  refine ⟨75268593163643545906697767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100358124218191394542263689 75268593163643545906697767)
  ·
    refine ⟨112902889745465318860046651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75268593163643545906697767 112902889745465318860046651)
    ·
      refine ⟨169354334618197978290069977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112902889745465318860046651 169354334618197978290069977)
      ·
        refine ⟨127015750963648483717552483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169354334618197978290069977 127015750963648483717552483)
        ·
          refine ⟨190523626445472725576328725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127015750963648483717552483 190523626445472725576328725)
          ·
            refine ⟨8930794989631534011390409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190523626445472725576328725 8930794989631534011390409)
            ·
              refine ⟨6698096242223650508542807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8930794989631534011390409 6698096242223650508542807)
              ·
                refine ⟨10047144363335475762814211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698096242223650508542807 10047144363335475762814211)
                ·
                  refine ⟨15070716545003213644221317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047144363335475762814211 15070716545003213644221317)
                  ·
                    refine ⟨2825759352188102558291497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15070716545003213644221317 2825759352188102558291497)
                    ·
                      refine ⟨2119319514141076918718623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2825759352188102558291497 2119319514141076918718623)
                      ·
                        rfl

theorem cell23_4127360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_4127360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127360 prefixEnd_4127360 := by exact prefixLift 4127360
  have htrace : WordTrace (prefixWord ++ tailWord_4127360) baseStart_4127360 baseEnd_4127360 := by
    simpa [prefixWord, tailWord_4127360, baseEnd_4127360] using wordTrace_append hprefix tailTrace_4127360
  have hstable : (prefixWord ++ tailWord_4127360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127360).length < 2 ^ (prefixWord ++ tailWord_4127360).sum := by decide
  have hdescent : baseEnd_4127360 < baseStart_4127360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127413 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4127413 : Nat := 118140960795 + 4127413 * 2 ^ 59
def prefixEnd_4127413 : Nat := 4983230072969 + 3 ^ 40 * 4127413 * 2
def baseEnd_4127413 : Nat := 706448909538588403785293

theorem tailTrace_4127413 : CollatzResearch.WordTrace tailWord_4127413 prefixEnd_4127413 706448909538588403785293 := by
  unfold tailWord_4127413
  simp only [CollatzResearch.WordTrace]
  refine ⟨150539119396095081865074893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100359412930730054576716595 150539119396095081865074893)
  ·
    refine ⟨56452169773535655699403085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150539119396095081865074893 56452169773535655699403085)
    ·
      refine ⟨21169563665075870887276157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56452169773535655699403085 21169563665075870887276157)
      ·
        refine ⟨7938586374403451582728559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21169563665075870887276157 7938586374403451582728559)
        ·
          refine ⟨11907879561605177374092839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938586374403451582728559 11907879561605177374092839)
          ·
            refine ⟨17861819342407766061139259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11907879561605177374092839 17861819342407766061139259)
            ·
              refine ⟨26792729013611649091708889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17861819342407766061139259 26792729013611649091708889)
              ·
                refine ⟨20094546760208736818781667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26792729013611649091708889 20094546760208736818781667)
                ·
                  refine ⟨30141820140313105228172501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20094546760208736818781667 30141820140313105228172501)
                  ·
                    refine ⟨706448909538588403785293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30141820140313105228172501 706448909538588403785293)
                    ·
                      rfl

theorem cell23_4127413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4127413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127413 prefixEnd_4127413 := by exact prefixLift 4127413
  have htrace : WordTrace (prefixWord ++ tailWord_4127413) baseStart_4127413 baseEnd_4127413 := by
    simpa [prefixWord, tailWord_4127413, baseEnd_4127413] using wordTrace_append hprefix tailTrace_4127413
  have hstable : (prefixWord ++ tailWord_4127413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127413).length < 2 ^ (prefixWord ++ tailWord_4127413).sum := by decide
  have hdescent : baseEnd_4127413 < baseStart_4127413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127460 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_4127460 : Nat := 118140960795 + 4127460 * 2 ^ 59
def prefixEnd_4127460 : Nat := 4983230072969 + 3 ^ 40 * 4127460 * 2
def baseEnd_4127460 : Nat := 706456954068842175822721

theorem tailTrace_4127460 : CollatzResearch.WordTrace tailWord_4127460 prefixEnd_4127460 706456954068842175822721 := by
  unfold tailWord_4127460
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270416813462404446017917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100360555751283205928023889 75270416813462404446017917)
  ·
    refine ⟨28226406305048401667256719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75270416813462404446017917 28226406305048401667256719)
    ·
      refine ⟨42339609457572602500885079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28226406305048401667256719 42339609457572602500885079)
      ·
        refine ⟨63509414186358903751327619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42339609457572602500885079 63509414186358903751327619)
        ·
          refine ⟨95264121279538355626991429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63509414186358903751327619 95264121279538355626991429)
          ·
            refine ⟨17862022739913441680060893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95264121279538355626991429 17862022739913441680060893)
            ·
              refine ⟨6698258527467540630022835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17862022739913441680060893 6698258527467540630022835)
              ·
                refine ⟨10047387791201310945034253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698258527467540630022835 10047387791201310945034253)
                ·
                  refine ⟨3767770421700491604387845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10047387791201310945034253 3767770421700491604387845)
                  ·
                    refine ⟨706456954068842175822721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767770421700491604387845 706456954068842175822721)
                    ·
                      rfl

theorem cell23_4127460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_4127460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127460 prefixEnd_4127460 := by exact prefixLift 4127460
  have htrace : WordTrace (prefixWord ++ tailWord_4127460) baseStart_4127460 baseEnd_4127460 := by
    simpa [prefixWord, tailWord_4127460, baseEnd_4127460] using wordTrace_append hprefix tailTrace_4127460
  have hstable : (prefixWord ++ tailWord_4127460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127460).length < 2 ^ (prefixWord ++ tailWord_4127460).sum := by decide
  have hdescent : baseEnd_4127460 < baseStart_4127460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127473 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 6]
def baseStart_4127473 : Nat := 118140960795 + 4127473 * 2 ^ 59
def prefixEnd_4127473 : Nat := 4983230072969 + 3 ^ 40 * 4127473 * 2
def baseEnd_4127473 : Nat := 235486393050559441845067

theorem tailTrace_4127473 : CollatzResearch.WordTrace tailWord_4127473 prefixEnd_4127473 235486393050559441845067 := by
  unfold tailWord_4127473
  simp only [CollatzResearch.WordTrace]
  refine ⟨150541307775877712112259073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100360871850585141408172715 150541307775877712112259073)
  ·
    refine ⟨112905980831908284084194305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150541307775877712112259073 112905980831908284084194305)
    ·
      refine ⟨84679485623931213063145729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112905980831908284084194305 84679485623931213063145729)
      ·
        refine ⟨63509614217948409797359297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84679485623931213063145729 63509614217948409797359297)
        ·
          refine ⟨47632210663461307348019473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63509614217948409797359297 47632210663461307348019473)
          ·
            refine ⟨35724157997595980511014605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47632210663461307348019473 35724157997595980511014605)
            ·
              refine ⟨13396559249098492691630477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35724157997595980511014605 13396559249098492691630477)
              ·
                refine ⟨5023709718411934759361429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13396559249098492691630477 5023709718411934759361429)
                ·
                  refine ⟨235486393050559441845067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5023709718411934759361429 235486393050559441845067)
                  ·
                    rfl

theorem cell23_4127473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_4127473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127473 prefixEnd_4127473 := by exact prefixLift 4127473
  have htrace : WordTrace (prefixWord ++ tailWord_4127473) baseStart_4127473 baseEnd_4127473 := by
    simpa [prefixWord, tailWord_4127473, baseEnd_4127473] using wordTrace_append hprefix tailTrace_4127473
  have hstable : (prefixWord ++ tailWord_4127473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127473).length < 2 ^ (prefixWord ++ tailWord_4127473).sum := by decide
  have hdescent : baseEnd_4127473 < baseStart_4127473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127511 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 1, 4]
def baseStart_4127511 : Nat := 118140960795 + 4127511 * 2 ^ 59
def prefixEnd_4127511 : Nat := 4983230072969 + 3 ^ 40 * 4127511 * 2
def baseEnd_4127511 : Nat := 706465683239968609310143

theorem tailTrace_4127511 : CollatzResearch.WordTrace tailWord_4127511 prefixEnd_4127511 706465683239968609310143 := by
  unfold tailWord_4127511
  simp only [CollatzResearch.WordTrace]
  refine ⟨150542693749740044602142387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100361795833160029734761591 150542693749740044602142387)
  ·
    refine ⟨225814040624610066903213581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150542693749740044602142387 225814040624610066903213581)
    ·
      refine ⟨84680265234228775088705093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225814040624610066903213581 84680265234228775088705093)
      ·
        refine ⟨15877549731417895329132205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84680265234228775088705093 15877549731417895329132205)
        ·
          refine ⟨5954081149281710748424577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15877549731417895329132205 5954081149281710748424577)
          ·
            refine ⟨4465560861961283061318433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5954081149281710748424577 4465560861961283061318433)
            ·
              refine ⟨3349170646470962295988825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465560861961283061318433 3349170646470962295988825)
              ·
                refine ⟨2511877984853221721991619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349170646470962295988825 2511877984853221721991619)
                ·
                  refine ⟨3767816977279832582987429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511877984853221721991619 3767816977279832582987429)
                  ·
                    refine ⟨706465683239968609310143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767816977279832582987429 706465683239968609310143)
                    ·
                      rfl

theorem cell23_4127511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_4127511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127511 prefixEnd_4127511 := by exact prefixLift 4127511
  have htrace : WordTrace (prefixWord ++ tailWord_4127511) baseStart_4127511 baseEnd_4127511 := by
    simpa [prefixWord, tailWord_4127511, baseEnd_4127511] using wordTrace_append hprefix tailTrace_4127511
  have hstable : (prefixWord ++ tailWord_4127511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127511).length < 2 ^ (prefixWord ++ tailWord_4127511).sum := by decide
  have hdescent : baseEnd_4127511 < baseStart_4127511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127534 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4127534 : Nat := 118140960795 + 4127534 * 2 ^ 59
def prefixEnd_4127534 : Nat := 4983230072969 + 3 ^ 40 * 4127534 * 2
def baseEnd_4127534 : Nat := 2119408859774959237942823

theorem tailTrace_4127534 : CollatzResearch.WordTrace tailWord_4127534 prefixEnd_4127534 2119408859774959237942823 := by
  unfold tailWord_4127534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817941578582089941278707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100362355085771146353486437 18817941578582089941278707)
  ·
    refine ⟨28226912367873134911918061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18817941578582089941278707 28226912367873134911918061)
    ·
      refine ⟨10585092137952425591969273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28226912367873134911918061 10585092137952425591969273)
      ·
        refine ⟨7938819103464319193976955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585092137952425591969273 7938819103464319193976955)
        ·
          refine ⟨11908228655196478790965433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938819103464319193976955 11908228655196478790965433)
          ·
            refine ⟨8931171491397359093224075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11908228655196478790965433 8931171491397359093224075)
            ·
              refine ⟨13396757237096038639836113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931171491397359093224075 13396757237096038639836113)
              ·
                refine ⟨10047567927822028979877085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13396757237096038639836113 10047567927822028979877085)
                ·
                  refine ⟨3767837972933260867453907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10047567927822028979877085 3767837972933260867453907)
                  ·
                    refine ⟨5651756959399891301180861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3767837972933260867453907 5651756959399891301180861)
                    ·
                      refine ⟨2119408859774959237942823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5651756959399891301180861 2119408859774959237942823)
                      ·
                        rfl

theorem cell23_4127534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4127534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127534 prefixEnd_4127534 := by exact prefixLift 4127534
  have htrace : WordTrace (prefixWord ++ tailWord_4127534) baseStart_4127534 baseEnd_4127534 := by
    simpa [prefixWord, tailWord_4127534, baseEnd_4127534] using wordTrace_append hprefix tailTrace_4127534
  have hstable : (prefixWord ++ tailWord_4127534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127534).length < 2 ^ (prefixWord ++ tailWord_4127534).sum := by decide
  have hdescent : baseEnd_4127534 < baseStart_4127534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127587 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 4]
def baseStart_4127587 : Nat := 118140960795 + 4127587 * 2 ^ 59
def prefixEnd_4127587 : Nat := 4983230072969 + 3 ^ 40 * 4127587 * 2
def baseEnd_4127587 : Nat := 2119436074249647530580079

theorem tailTrace_4127587 : CollatzResearch.WordTrace tailWord_4127587 prefixEnd_4127587 2119436074249647530580079 := by
  unfold tailWord_4127587
  simp only [CollatzResearch.WordTrace]
  refine ⟨150545465697464709581909015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100363643798309806387939343 150545465697464709581909015)
  ·
    refine ⟨225818198546197064372863523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150545465697464709581909015 225818198546197064372863523)
    ·
      refine ⟨338727297819295596559295285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225818198546197064372863523 338727297819295596559295285)
      ·
        refine ⟨31755684170558962177433933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338727297819295596559295285 31755684170558962177433933)
        ·
          refine ⟨11908381563959610816537725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31755684170558962177433933 11908381563959610816537725)
          ·
            refine ⟨4465643086484854056201647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11908381563959610816537725 4465643086484854056201647)
            ·
              refine ⟨6698464629727281084302471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465643086484854056201647 6698464629727281084302471)
              ·
                refine ⟨10047696944590921626453707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698464629727281084302471 10047696944590921626453707)
                ·
                  refine ⟨15071545416886382439680561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10047696944590921626453707 15071545416886382439680561)
                  ·
                    refine ⟨11303659062664786829760421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15071545416886382439680561 11303659062664786829760421)
                    ·
                      refine ⟨2119436074249647530580079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11303659062664786829760421 2119436074249647530580079)
                      ·
                        rfl

theorem cell23_4127587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_4127587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127587 prefixEnd_4127587 := by exact prefixLift 4127587
  have htrace : WordTrace (prefixWord ++ tailWord_4127587) baseStart_4127587 baseEnd_4127587 := by
    simpa [prefixWord, tailWord_4127587, baseEnd_4127587] using wordTrace_append hprefix tailTrace_4127587
  have hstable : (prefixWord ++ tailWord_4127587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127587).length < 2 ^ (prefixWord ++ tailWord_4127587).sum := by decide
  have hdescent : baseEnd_4127587 < baseStart_4127587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127603 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_4127603 : Nat := 118140960795 + 4127603 * 2 ^ 59
def prefixEnd_4127603 : Nat := 4983230072969 + 3 ^ 40 * 4127603 * 2
def baseEnd_4127603 : Nat := 2119444289940119467980005

theorem tailTrace_4127603 : CollatzResearch.WordTrace tailWord_4127603 prefixEnd_4127603 2119444289940119467980005 := by
  unfold tailWord_4127603
  simp only [CollatzResearch.WordTrace]
  refine ⟨150546049265406744314491463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100364032843604496209660975 150546049265406744314491463)
  ·
    refine ⟨225819073898110116471737195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150546049265406744314491463 225819073898110116471737195)
    ·
      refine ⟨338728610847165174707605793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225819073898110116471737195 338728610847165174707605793)
      ·
        refine ⟨254046458135373881030704345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338728610847165174707605793 254046458135373881030704345)
        ·
          refine ⟨190534843601530410773028259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254046458135373881030704345 190534843601530410773028259)
          ·
            refine ⟨285802265402295616159542389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190534843601530410773028259 285802265402295616159542389)
            ·
              refine ⟨26793962381465214014957099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285802265402295616159542389 26793962381465214014957099)
              ·
                refine ⟨40190943572197821022435649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26793962381465214014957099 40190943572197821022435649)
                ·
                  refine ⟨30143207679148365766826737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40190943572197821022435649 30143207679148365766826737)
                  ·
                    refine ⟨22607405759361274325120053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30143207679148365766826737 22607405759361274325120053)
                    ·
                      refine ⟨2119444289940119467980005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22607405759361274325120053 2119444289940119467980005)
                      ·
                        rfl

theorem cell23_4127603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_4127603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127603 prefixEnd_4127603 := by exact prefixLift 4127603
  have htrace : WordTrace (prefixWord ++ tailWord_4127603) baseStart_4127603 baseEnd_4127603 := by
    simpa [prefixWord, tailWord_4127603, baseEnd_4127603] using wordTrace_append hprefix tailTrace_4127603
  have hstable : (prefixWord ++ tailWord_4127603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127603).length < 2 ^ (prefixWord ++ tailWord_4127603).sum := by decide
  have hdescent : baseEnd_4127603 < baseStart_4127603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127614 : List Nat := [4, 2, 3, 1, 3, 1, 9]
def baseStart_4127614 : Nat := 118140960795 + 4127614 * 2 ^ 59
def prefixEnd_4127614 : Nat := 4983230072969 + 3 ^ 40 * 4127614 * 2
def baseEnd_4127614 : Nat := 26166048620090357098055

theorem tailTrace_4127614 : CollatzResearch.WordTrace tailWord_4127614 prefixEnd_4127614 26166048620090357098055 := by
  unfold tailWord_4127614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818306308545861649142737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100364300312244595462094597 18818306308545861649142737)
  ·
    refine ⟨14113729731409396236857053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18818306308545861649142737 14113729731409396236857053)
    ·
      refine ⟨5292648649278523588821395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14113729731409396236857053 5292648649278523588821395)
      ·
        refine ⟨7938972973917785383232093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292648649278523588821395 7938972973917785383232093)
        ·
          refine ⟨2977114865219169518712035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7938972973917785383232093 2977114865219169518712035)
          ·
            refine ⟨4465672297828754278068053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977114865219169518712035 4465672297828754278068053)
            ·
              refine ⟨26166048620090357098055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4465672297828754278068053 26166048620090357098055)
              ·
                rfl

theorem cell23_4127614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 9].length) (baseStart_4127614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127614 prefixEnd_4127614 := by exact prefixLift 4127614
  have htrace : WordTrace (prefixWord ++ tailWord_4127614) baseStart_4127614 baseEnd_4127614 := by
    simpa [prefixWord, tailWord_4127614, baseEnd_4127614] using wordTrace_append hprefix tailTrace_4127614
  have hstable : (prefixWord ++ tailWord_4127614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127614).length < 2 ^ (prefixWord ++ tailWord_4127614).sum := by decide
  have hdescent : baseEnd_4127614 < baseStart_4127614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127633 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_4127633 : Nat := 118140960795 + 4127633 * 2 ^ 59
def prefixEnd_4127633 : Nat := 4983230072969 + 3 ^ 40 * 4127633 * 2
def baseEnd_4127633 : Nat := 2119459694359754350604867

theorem tailTrace_4127633 : CollatzResearch.WordTrace tailWord_4127633 prefixEnd_4127633 2119459694359754350604867 := by
  unfold tailWord_4127633
  simp only [CollatzResearch.WordTrace]
  refine ⟨150547143455298059438083553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100364762303532039625389035 150547143455298059438083553)
  ·
    refine ⟨112910357591473544578562665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150547143455298059438083553 112910357591473544578562665)
    ·
      refine ⟨84682768193605158433921999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112910357591473544578562665 84682768193605158433921999)
      ·
        refine ⟨127024152290407737650882999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84682768193605158433921999 127024152290407737650882999)
        ·
          refine ⟨190536228435611606476324499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127024152290407737650882999 190536228435611606476324499)
          ·
            refine ⟨285804342653417409714486749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190536228435611606476324499 285804342653417409714486749)
            ·
              refine ⟨107176628495031528642932531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285804342653417409714486749 107176628495031528642932531)
              ·
                refine ⟨160764942742547292964398797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107176628495031528642932531 160764942742547292964398797)
                ·
                  refine ⟨60286853528455234861649549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160764942742547292964398797 60286853528455234861649549)
                  ·
                    refine ⟨22607570073170713073118581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60286853528455234861649549 22607570073170713073118581)
                    ·
                      refine ⟨2119459694359754350604867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22607570073170713073118581 2119459694359754350604867)
                      ·
                        rfl

theorem cell23_4127633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_4127633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127633 prefixEnd_4127633 := by exact prefixLift 4127633
  have htrace : WordTrace (prefixWord ++ tailWord_4127633) baseStart_4127633 baseEnd_4127633 := by
    simpa [prefixWord, tailWord_4127633, baseEnd_4127633] using wordTrace_append hprefix tailTrace_4127633
  have hstable : (prefixWord ++ tailWord_4127633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127633).length < 2 ^ (prefixWord ++ tailWord_4127633).sum := by decide
  have hdescent : baseEnd_4127633 < baseStart_4127633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_4127663 : Nat := 118140960795 + 4127663 * 2 ^ 59
def prefixEnd_4127663 : Nat := 4983230072969 + 3 ^ 40 * 4127663 * 2
def baseEnd_4127663 : Nat := 2119475098779389233229729

theorem tailTrace_4127663 : CollatzResearch.WordTrace tailWord_4127663 prefixEnd_4127663 2119475098779389233229729 := by
  unfold tailWord_4127663
  simp only [CollatzResearch.WordTrace]
  refine ⟨150548237645189374561675643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100365491763459583041117095 150548237645189374561675643)
  ·
    refine ⟨225822356467784061842513465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150548237645189374561675643 225822356467784061842513465)
    ·
      refine ⟨169366767350838046381885099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225822356467784061842513465 169366767350838046381885099)
      ·
        refine ⟨254050151026257069572827649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169366767350838046381885099 254050151026257069572827649)
        ·
          refine ⟨190537613269692802179620737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254050151026257069572827649 190537613269692802179620737)
          ·
            refine ⟨142903209952269601634715553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190537613269692802179620737 142903209952269601634715553)
            ·
              refine ⟨107177407464202201226036665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142903209952269601634715553 107177407464202201226036665)
              ·
                refine ⟨80383055598151650919527499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107177407464202201226036665 80383055598151650919527499)
                ·
                  refine ⟨120574583397227476379291249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80383055598151650919527499 120574583397227476379291249)
                  ·
                    refine ⟨90430937547920607284468437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120574583397227476379291249 90430937547920607284468437)
                    ·
                      refine ⟨2119475098779389233229729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90430937547920607284468437 2119475098779389233229729)
                      ·
                        rfl

theorem cell23_4127663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_4127663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127663 prefixEnd_4127663 := by exact prefixLift 4127663
  have htrace : WordTrace (prefixWord ++ tailWord_4127663) baseStart_4127663 baseEnd_4127663 := by
    simpa [prefixWord, tailWord_4127663, baseEnd_4127663] using wordTrace_append hprefix tailTrace_4127663
  have hstable : (prefixWord ++ tailWord_4127663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127663).length < 2 ^ (prefixWord ++ tailWord_4127663).sum := by decide
  have hdescent : baseEnd_4127663 < baseStart_4127663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127732 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4127732 : Nat := 118140960795 + 4127732 * 2 ^ 59
def prefixEnd_4127732 : Nat := 4983230072969 + 3 ^ 40 * 4127732 * 2
def baseEnd_4127732 : Nat := 2119510528944549463266913

theorem tailTrace_4127732 : CollatzResearch.WordTrace tailWord_4127732 prefixEnd_4127732 2119510528944549463266913 := by
  unfold tailWord_4127732
  simp only [CollatzResearch.WordTrace]
  refine ⟨75275377140969699672968725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100367169521292932897291633 75275377140969699672968725)
  ·
    refine ⟨3528533303482954672170409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75275377140969699672968725 3528533303482954672170409)
    ·
      refine ⟨2646399977612216004127807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528533303482954672170409 2646399977612216004127807)
      ·
        refine ⟨3969599966418324006191711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646399977612216004127807 3969599966418324006191711)
        ·
          refine ⟨5954399949627486009287567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969599966418324006191711 5954399949627486009287567)
          ·
            refine ⟨8931599924441229013931351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954399949627486009287567 8931599924441229013931351)
            ·
              refine ⟨13397399886661843520897027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931599924441229013931351 13397399886661843520897027)
              ·
                refine ⟨20096099829992765281345541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397399886661843520897027 20096099829992765281345541)
                ·
                  refine ⟨3768018718123643490252289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20096099829992765281345541 3768018718123643490252289)
                  ·
                    refine ⟨2826014038592732617689217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768018718123643490252289 2826014038592732617689217)
                    ·
                      refine ⟨2119510528944549463266913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826014038592732617689217 2119510528944549463266913)
                      ·
                        rfl

theorem cell23_4127732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4127732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127732 prefixEnd_4127732 := by exact prefixLift 4127732
  have htrace : WordTrace (prefixWord ++ tailWord_4127732) baseStart_4127732 baseEnd_4127732 := by
    simpa [prefixWord, tailWord_4127732, baseEnd_4127732] using wordTrace_append hprefix tailTrace_4127732
  have hstable : (prefixWord ++ tailWord_4127732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127732).length < 2 ^ (prefixWord ++ tailWord_4127732).sum := by decide
  have hdescent : baseEnd_4127732 < baseStart_4127732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127737 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 4, 2]
def baseStart_4127737 : Nat := 118140960795 + 4127737 * 2 ^ 59
def prefixEnd_4127737 : Nat := 4983230072969 + 3 ^ 40 * 4127737 * 2
def baseEnd_4127737 : Nat := 2119513096347821943704389

theorem tailTrace_4127737 : CollatzResearch.WordTrace tailWord_4127737 prefixEnd_4127737 2119513096347821943704389 := by
  unfold tailWord_4127737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150550936646921285199869465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100367291097947523466579643 150550936646921285199869465)
  ·
    refine ⟨112913202485190963899902099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150550936646921285199869465 112913202485190963899902099)
    ·
      refine ⟨169369803727786445849853149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112913202485190963899902099 169369803727786445849853149)
      ·
        refine ⟨63513676397919917193694931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169369803727786445849853149 63513676397919917193694931)
        ·
          refine ⟨95270514596879875790542397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63513676397919917193694931 95270514596879875790542397)
          ·
            refine ⟨35726442973829953421453399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95270514596879875790542397 35726442973829953421453399)
            ·
              refine ⟨53589664460744930132180099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35726442973829953421453399 53589664460744930132180099)
              ·
                refine ⟨80384496691117395198270149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53589664460744930132180099 80384496691117395198270149)
                ·
                  refine ⟨15072093129584511599675653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80384496691117395198270149 15072093129584511599675653)
                  ·
                    refine ⟨2826017461797095924939185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15072093129584511599675653 2826017461797095924939185)
                    ·
                      refine ⟨2119513096347821943704389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826017461797095924939185 2119513096347821943704389)
                      ·
                        rfl

theorem cell23_4127737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_4127737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127737 prefixEnd_4127737 := by exact prefixLift 4127737
  have htrace : WordTrace (prefixWord ++ tailWord_4127737) baseStart_4127737 baseEnd_4127737 := by
    simpa [prefixWord, tailWord_4127737, baseEnd_4127737] using wordTrace_append hprefix tailTrace_4127737
  have hstable : (prefixWord ++ tailWord_4127737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127737).length < 2 ^ (prefixWord ++ tailWord_4127737).sum := by decide
  have hdescent : baseEnd_4127737 < baseStart_4127737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127754 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_4127754 : Nat := 118140960795 + 4127754 * 2 ^ 59
def prefixEnd_4127754 : Nat := 4983230072969 + 3 ^ 40 * 4127754 * 2
def baseEnd_4127754 : Nat := 2119521825518948377191811

theorem tailTrace_4127754 : CollatzResearch.WordTrace tailWord_4127754 prefixEnd_4127754 2119521825518948377191811 := by
  unfold tailWord_4127754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637889171964924275809579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100367704458573131402158877 37637889171964924275809579)
  ·
    refine ⟨56456833757947386413714369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637889171964924275809579 56456833757947386413714369)
    ·
      refine ⟨42342625318460539810285777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56456833757947386413714369 42342625318460539810285777)
      ·
        refine ⟨31756968988845404857714333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42342625318460539810285777 31756968988845404857714333)
        ·
          refine ⟨11908863370817026821642875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31756968988845404857714333 11908863370817026821642875)
          ·
            refine ⟨17863295056225540232464313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11908863370817026821642875 17863295056225540232464313)
            ·
              refine ⟨13397471292169155174348235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17863295056225540232464313 13397471292169155174348235)
              ·
                refine ⟨20096206938253732761522353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397471292169155174348235 20096206938253732761522353)
                ·
                  refine ⟨15072155203690299571141765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20096206938253732761522353 15072155203690299571141765)
                  ·
                    refine ⟨2826029100691931169589081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15072155203690299571141765 2826029100691931169589081)
                    ·
                      refine ⟨2119521825518948377191811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826029100691931169589081 2119521825518948377191811)
                      ·
                        rfl

theorem cell23_4127754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_4127754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127754 prefixEnd_4127754 := by exact prefixLift 4127754
  have htrace : WordTrace (prefixWord ++ tailWord_4127754) baseStart_4127754 baseEnd_4127754 := by
    simpa [prefixWord, tailWord_4127754, baseEnd_4127754] using wordTrace_append hprefix tailTrace_4127754
  have hstable : (prefixWord ++ tailWord_4127754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127754).length < 2 ^ (prefixWord ++ tailWord_4127754).sum := by decide
  have hdescent : baseEnd_4127754 < baseStart_4127754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127827 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 8, 2]
def baseStart_4127827 : Nat := 118140960795 + 4127827 * 2 ^ 59
def prefixEnd_4127827 : Nat := 4983230072969 + 3 ^ 40 * 4127827 * 2
def baseEnd_4127827 : Nat := 2119559309606726591578975

theorem tailTrace_4127827 : CollatzResearch.WordTrace tailWord_4127827 prefixEnd_4127827 2119559309606726591578975 := by
  unfold tailWord_4127827
  simp only [CollatzResearch.WordTrace]
  refine ⟨150554219216595230570645735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100369479477730153713763823 150554219216595230570645735)
  ·
    refine ⟨225831328824892845855968603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150554219216595230570645735 225831328824892845855968603)
    ·
      refine ⟨338746993237339268783952905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225831328824892845855968603 338746993237339268783952905)
      ·
        refine ⟨254060244928004451587964679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338746993237339268783952905 254060244928004451587964679)
        ·
          refine ⟨381090367392006677381947019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254060244928004451587964679 381090367392006677381947019)
          ·
            refine ⟨571635551088010016072920529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381090367392006677381947019 571635551088010016072920529)
            ·
              refine ⟨428726663316007512054690397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571635551088010016072920529 428726663316007512054690397)
              ·
                refine ⟨160772498743502817020508899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428726663316007512054690397 160772498743502817020508899)
                ·
                  refine ⟨241158748115254225530763349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160772498743502817020508899 241158748115254225530763349)
                  ·
                    refine ⟨2826079079475635455438633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 241158748115254225530763349 2826079079475635455438633)
                    ·
                      refine ⟨2119559309606726591578975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826079079475635455438633 2119559309606726591578975)
                      ·
                        rfl

theorem cell23_4127827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8, 2].length) (baseStart_4127827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127827 prefixEnd_4127827 := by exact prefixLift 4127827
  have htrace : WordTrace (prefixWord ++ tailWord_4127827) baseStart_4127827 baseEnd_4127827 := by
    simpa [prefixWord, tailWord_4127827, baseEnd_4127827] using wordTrace_append hprefix tailTrace_4127827
  have hstable : (prefixWord ++ tailWord_4127827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127827).length < 2 ^ (prefixWord ++ tailWord_4127827).sum := by decide
  have hdescent : baseEnd_4127827 < baseStart_4127827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127895 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_4127895 : Nat := 118140960795 + 4127895 * 2 ^ 59
def prefixEnd_4127895 : Nat := 4983230072969 + 3 ^ 40 * 4127895 * 2
def baseEnd_4127895 : Nat := 2119594226291232325528663

theorem tailTrace_4127895 : CollatzResearch.WordTrace tailWord_4127895 prefixEnd_4127895 2119594226291232325528663 := by
  unfold tailWord_4127895
  simp only [CollatzResearch.WordTrace]
  refine ⟨150556699380348878184121139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100371132920232585456080759 150556699380348878184121139)
  ·
    refine ⟨225835049070523317276181709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150556699380348878184121139 225835049070523317276181709)
    ·
      refine ⟨84688143401446243978568141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225835049070523317276181709 84688143401446243978568141)
      ·
        refine ⟨31758053775542341491963053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84688143401446243978568141 31758053775542341491963053)
        ·
          refine ⟨11909270165828378059486145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31758053775542341491963053 11909270165828378059486145)
          ·
            refine ⟨8931952624371283544614609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11909270165828378059486145 8931952624371283544614609)
            ·
              refine ⟨6698964468278462658460957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8931952624371283544614609 6698964468278462658460957)
              ·
                refine ⟨2512111675604423496922859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698964468278462658460957 2512111675604423496922859)
                ·
                  refine ⟨3768167513406635245384289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512111675604423496922859 3768167513406635245384289)
                  ·
                    refine ⟨2826125635054976434038217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768167513406635245384289 2826125635054976434038217)
                    ·
                      refine ⟨2119594226291232325528663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826125635054976434038217 2119594226291232325528663)
                      ·
                        rfl

theorem cell23_4127895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_4127895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127895 prefixEnd_4127895 := by exact prefixLift 4127895
  have htrace : WordTrace (prefixWord ++ tailWord_4127895) baseStart_4127895 baseEnd_4127895 := by
    simpa [prefixWord, tailWord_4127895, baseEnd_4127895] using wordTrace_append hprefix tailTrace_4127895
  have hstable : (prefixWord ++ tailWord_4127895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127895).length < 2 ^ (prefixWord ++ tailWord_4127895).sum := by decide
  have hdescent : baseEnd_4127895 < baseStart_4127895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127898 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4127898 : Nat := 118140960795 + 4127898 * 2 ^ 59
def prefixEnd_4127898 : Nat := 4983230072969 + 3 ^ 40 * 4127898 * 2
def baseEnd_4127898 : Nat := 2119595766733195813791149

theorem tailTrace_4127898 : CollatzResearch.WordTrace tailWord_4127898 prefixEnd_4127898 2119595766733195813791149 := by
  unfold tailWord_4127898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37639202199834502424120087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100371205866225339797653565 37639202199834502424120087)
  ·
    refine ⟨56458803299751753636180131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37639202199834502424120087 56458803299751753636180131)
    ·
      refine ⟨84688204949627630454270197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56458803299751753636180131 84688204949627630454270197)
      ·
        refine ⟨7939519214027590355087831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84688204949627630454270197 7939519214027590355087831)
        ·
          refine ⟨11909278821041385532631747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939519214027590355087831 11909278821041385532631747)
          ·
            refine ⟨17863918231562078298947621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11909278821041385532631747 17863918231562078298947621)
            ·
              refine ⟨3349484668417889681052679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17863918231562078298947621 3349484668417889681052679)
              ·
                refine ⟨5024227002626834521579019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349484668417889681052679 5024227002626834521579019)
                ·
                  refine ⟨7536340503940251782368529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024227002626834521579019 7536340503940251782368529)
                  ·
                    refine ⟨5652255377955188836776397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536340503940251782368529 5652255377955188836776397)
                    ·
                      refine ⟨2119595766733195813791149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652255377955188836776397 2119595766733195813791149)
                      ·
                        rfl

theorem cell23_4127898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4127898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127898 prefixEnd_4127898 := by exact prefixLift 4127898
  have htrace : WordTrace (prefixWord ++ tailWord_4127898) baseStart_4127898 baseEnd_4127898 := by
    simpa [prefixWord, tailWord_4127898, baseEnd_4127898] using wordTrace_append hprefix tailTrace_4127898
  have hstable : (prefixWord ++ tailWord_4127898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127898).length < 2 ^ (prefixWord ++ tailWord_4127898).sum := by decide
  have hdescent : baseEnd_4127898 < baseStart_4127898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127927 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 6]
def baseStart_4127927 : Nat := 118140960795 + 4127927 * 2 ^ 59
def prefixEnd_4127927 : Nat := 4983230072969 + 3 ^ 40 * 4127927 * 2
def baseEnd_4127927 : Nat := 706536885890725400109505

theorem tailTrace_4127927 : CollatzResearch.WordTrace tailWord_4127927 prefixEnd_4127927 706536885890725400109505 := by
  unfold tailWord_4127927
  simp only [CollatzResearch.WordTrace]
  refine ⟨150557866516232947649286035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100371911010821965099524023 150557866516232947649286035)
  ·
    refine ⟨225836799774349421473929053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150557866516232947649286035 225836799774349421473929053)
    ·
      refine ⟨84688799915381033052723395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225836799774349421473929053 84688799915381033052723395)
      ·
        refine ⟨127033199873071549579085093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84688799915381033052723395 127033199873071549579085093)
        ·
          refine ⟨23818724976200915546078455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127033199873071549579085093 23818724976200915546078455)
          ·
            refine ⟨35728087464301373319117683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23818724976200915546078455 35728087464301373319117683)
            ·
              refine ⟨53592131196452059978676525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35728087464301373319117683 53592131196452059978676525)
              ·
                refine ⟨20097049198669522492003697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53592131196452059978676525 20097049198669522492003697)
                ·
                  refine ⟨15072786899002141869002773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20097049198669522492003697 15072786899002141869002773)
                  ·
                    refine ⟨706536885890725400109505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15072786899002141869002773 706536885890725400109505)
                    ·
                      rfl

theorem cell23_4127927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_4127927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127927 prefixEnd_4127927 := by exact prefixLift 4127927
  have htrace : WordTrace (prefixWord ++ tailWord_4127927) baseStart_4127927 baseEnd_4127927 := by
    simpa [prefixWord, tailWord_4127927, baseEnd_4127927] using wordTrace_append hprefix tailTrace_4127927
  have hstable : (prefixWord ++ tailWord_4127927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127927).length < 2 ^ (prefixWord ++ tailWord_4127927).sum := by decide
  have hdescent : baseEnd_4127927 < baseStart_4127927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127947 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_4127947 : Nat := 118140960795 + 4127947 * 2 ^ 59
def prefixEnd_4127947 : Nat := 4983230072969 + 3 ^ 40 * 4127947 * 2
def baseEnd_4127947 : Nat := 2119620927285266122078423

theorem tailTrace_4127947 : CollatzResearch.WordTrace tailWord_4127947 prefixEnd_4127947 2119620927285266122078423 := by
  unfold tailWord_4127947
  simp only [CollatzResearch.WordTrace]
  refine ⟨150558595976160491065014095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100372397317440327376676063 150558595976160491065014095)
  ·
    refine ⟨225837893964240736597521143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150558595976160491065014095 225837893964240736597521143)
    ·
      refine ⟨338756840946361104896281715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225837893964240736597521143 338756840946361104896281715)
      ·
        refine ⟨508135261419541657344422573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338756840946361104896281715 508135261419541657344422573)
        ·
          refine ⟨190550723032328121504158465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508135261419541657344422573 190550723032328121504158465)
          ·
            refine ⟨142913042274246091128118849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190550723032328121504158465 142913042274246091128118849)
            ·
              refine ⟨107184781705684568346089137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142913042274246091128118849 107184781705684568346089137)
              ·
                refine ⟨80388586279263426259566853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107184781705684568346089137 80388586279263426259566853)
                ·
                  refine ⟨15072859927361892423668785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80388586279263426259566853 15072859927361892423668785)
                  ·
                    refine ⟨11304644945521419317751589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15072859927361892423668785 11304644945521419317751589)
                    ·
                      refine ⟨2119620927285266122078423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11304644945521419317751589 2119620927285266122078423)
                      ·
                        rfl

theorem cell23_4127947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_4127947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127947 prefixEnd_4127947 := by exact prefixLift 4127947
  have htrace : WordTrace (prefixWord ++ tailWord_4127947) baseStart_4127947 baseEnd_4127947 := by
    simpa [prefixWord, tailWord_4127947, baseEnd_4127947] using wordTrace_append hprefix tailTrace_4127947
  have hstable : (prefixWord ++ tailWord_4127947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127947).length < 2 ^ (prefixWord ++ tailWord_4127947).sum := by decide
  have hdescent : baseEnd_4127947 < baseStart_4127947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4127954 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4127954 : Nat := 118140960795 + 4127954 * 2 ^ 59
def prefixEnd_4127954 : Nat := 4983230072969 + 3 ^ 40 * 4127954 * 2
def baseEnd_4127954 : Nat := 2119624521649847594690891

theorem tailTrace_4127954 : CollatzResearch.WordTrace tailWord_4127954 prefixEnd_4127954 2119624521649847594690891 := by
  unfold tailWord_4127954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37639712821783782815129729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100372567524756754173679277 37639712821783782815129729)
  ·
    refine ⟨28229784616337837111347297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37639712821783782815129729 28229784616337837111347297)
    ·
      refine ⟨21172338462253377833510473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28229784616337837111347297 21172338462253377833510473)
      ·
        refine ⟨15879253846690033375132855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21172338462253377833510473 15879253846690033375132855)
        ·
          refine ⟨23818880770035050062699283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879253846690033375132855 23818880770035050062699283)
          ·
            refine ⟨35728321155052575094048925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23818880770035050062699283 35728321155052575094048925)
            ·
              refine ⟨13398120433144715660268347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35728321155052575094048925 13398120433144715660268347)
              ·
                refine ⟨20097180649717073490402521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13398120433144715660268347 20097180649717073490402521)
                ·
                  refine ⟨15072885487287805117801891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20097180649717073490402521 15072885487287805117801891)
                  ·
                    refine ⟨22609328230931707676702837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15072885487287805117801891 22609328230931707676702837)
                    ·
                      refine ⟨2119624521649847594690891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22609328230931707676702837 2119624521649847594690891)
                      ·
                        rfl

theorem cell23_4127954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4127954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4127954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4127954 prefixEnd_4127954 := by exact prefixLift 4127954
  have htrace : WordTrace (prefixWord ++ tailWord_4127954) baseStart_4127954 baseEnd_4127954 := by
    simpa [prefixWord, tailWord_4127954, baseEnd_4127954] using wordTrace_append hprefix tailTrace_4127954
  have hstable : (prefixWord ++ tailWord_4127954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127954).length < 2 ^ (prefixWord ++ tailWord_4127954).sum := by decide
  have hdescent : baseEnd_4127954 < baseStart_4127954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128014 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4128014 : Nat := 118140960795 + 4128014 * 2 ^ 59
def prefixEnd_4128014 : Nat := 4983230072969 + 3 ^ 40 * 4128014 * 2
def baseEnd_4128014 : Nat := 2119655330489117359940615

theorem tailTrace_4128014 : CollatzResearch.WordTrace tailWord_4128014 prefixEnd_4128014 2119655330489117359940615 := by
  unfold tailWord_4128014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820129958364720188462887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100374026444611841005135397 18820129958364720188462887)
  ·
    refine ⟨28230194937547080282694331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18820129958364720188462887 28230194937547080282694331)
    ·
      refine ⟨42345292406320620424041497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230194937547080282694331 42345292406320620424041497)
      ·
        refine ⟨31758969304740465318031123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42345292406320620424041497 31758969304740465318031123)
        ·
          refine ⟨47638453957110697977046685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31758969304740465318031123 47638453957110697977046685)
          ·
            refine ⟨17864420233916511741392507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47638453957110697977046685 17864420233916511741392507)
            ·
              refine ⟨26796630350874767612088761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17864420233916511741392507 26796630350874767612088761)
              ·
                refine ⟨20097472763156075709066571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26796630350874767612088761 20097472763156075709066571)
                ·
                  refine ⟨30146209144734113563599857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20097472763156075709066571 30146209144734113563599857)
                  ·
                    refine ⟨22609656858550585172699893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30146209144734113563599857 22609656858550585172699893)
                    ·
                      refine ⟨2119655330489117359940615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22609656858550585172699893 2119655330489117359940615)
                      ·
                        rfl

theorem cell23_4128014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4128014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128014 prefixEnd_4128014 := by exact prefixLift 4128014
  have htrace : WordTrace (prefixWord ++ tailWord_4128014) baseStart_4128014 baseEnd_4128014 := by
    simpa [prefixWord, tailWord_4128014, baseEnd_4128014] using wordTrace_append hprefix tailTrace_4128014
  have hstable : (prefixWord ++ tailWord_4128014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128014).length < 2 ^ (prefixWord ++ tailWord_4128014).sum := by decide
  have hdescent : baseEnd_4128014 < baseStart_4128014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128027 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_4128027 : Nat := 118140960795 + 4128027 * 2 ^ 59
def prefixEnd_4128027 : Nat := 4983230072969 + 3 ^ 40 * 4128027 * 2
def baseEnd_4128027 : Nat := 2119662005737625809078055

theorem tailTrace_4128027 : CollatzResearch.WordTrace tailWord_4128027 prefixEnd_4128027 2119662005737625809078055 := by
  unfold tailWord_4128027
  simp only [CollatzResearch.WordTrace]
  refine ⟨150561513815870664727926335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100374342543913776485284223 150561513815870664727926335)
  ·
    refine ⟨225842270723805997091889503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150561513815870664727926335 225842270723805997091889503)
    ·
      refine ⟨338763406085708995637834255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225842270723805997091889503 338763406085708995637834255)
      ·
        refine ⟨508145109128563493456751383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338763406085708995637834255 508145109128563493456751383)
        ·
          refine ⟨762217663692845240185127075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508145109128563493456751383 762217663692845240185127075)
          ·
            refine ⟨1143326495539267860277690613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762217663692845240185127075 1143326495539267860277690613)
            ·
              refine ⟨107186858956806361901033495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1143326495539267860277690613 107186858956806361901033495)
              ·
                refine ⟨160780288435209542851550243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107186858956806361901033495 160780288435209542851550243)
                ·
                  refine ⟨241170432652814314277325365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160780288435209542851550243 241170432652814314277325365)
                  ·
                    refine ⟨22609728061201341963499253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241170432652814314277325365 22609728061201341963499253)
                    ·
                      refine ⟨2119662005737625809078055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22609728061201341963499253 2119662005737625809078055)
                      ·
                        rfl

theorem cell23_4128027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_4128027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128027 prefixEnd_4128027 := by exact prefixLift 4128027
  have htrace : WordTrace (prefixWord ++ tailWord_4128027) baseStart_4128027 baseEnd_4128027 := by
    simpa [prefixWord, tailWord_4128027, baseEnd_4128027] using wordTrace_append hprefix tailTrace_4128027
  have hstable : (prefixWord ++ tailWord_4128027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128027).length < 2 ^ (prefixWord ++ tailWord_4128027).sum := by decide
  have hdescent : baseEnd_4128027 < baseStart_4128027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128044 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_4128044 : Nat := 118140960795 + 4128044 * 2 ^ 59
def prefixEnd_4128044 : Nat := 4983230072969 + 3 ^ 40 * 4128044 * 2
def baseEnd_4128044 : Nat := 2119670734908752242565477

theorem tailTrace_4128044 : CollatzResearch.WordTrace tailWord_4128044 prefixEnd_4128044 2119670734908752242565477 := by
  unfold tailWord_4128044
  simp only [CollatzResearch.WordTrace]
  refine ⟨75281066928404538315647593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100374755904539384420863457 75281066928404538315647593)
  ·
    refine ⟨56460800196303403736735695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75281066928404538315647593 56460800196303403736735695)
    ·
      refine ⟨84691200294455105605103543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56460800196303403736735695 84691200294455105605103543)
      ·
        refine ⟨127036800441682658407655315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84691200294455105605103543 127036800441682658407655315)
        ·
          refine ⟨190555200662523987611482973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127036800441682658407655315 190555200662523987611482973)
          ·
            refine ⟨71458200248446495354306115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190555200662523987611482973 71458200248446495354306115)
            ·
              refine ⟨107187300372669743031459173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71458200248446495354306115 107187300372669743031459173)
              ·
                refine ⟨20097618819875576818398595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107187300372669743031459173 20097618819875576818398595)
                ·
                  refine ⟨30146428229813365227597893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20097618819875576818398595 30146428229813365227597893)
                  ·
                    refine ⟨5652455293090005980174605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30146428229813365227597893 5652455293090005980174605)
                    ·
                      refine ⟨2119670734908752242565477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652455293090005980174605 2119670734908752242565477)
                      ·
                        rfl

theorem cell23_4128044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_4128044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128044 prefixEnd_4128044 := by exact prefixLift 4128044
  have htrace : WordTrace (prefixWord ++ tailWord_4128044) baseStart_4128044 baseEnd_4128044 := by
    simpa [prefixWord, tailWord_4128044, baseEnd_4128044] using wordTrace_append hprefix tailTrace_4128044
  have hstable : (prefixWord ++ tailWord_4128044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128044).length < 2 ^ (prefixWord ++ tailWord_4128044).sum := by decide
  have hdescent : baseEnd_4128044 < baseStart_4128044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128047 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 10]
def baseStart_4128047 : Nat := 118140960795 + 4128047 * 2 ^ 59
def prefixEnd_4128047 : Nat := 4983230072969 + 3 ^ 40 * 4128047 * 2
def baseEnd_4128047 : Nat := 235519141705635081203107

theorem tailTrace_4128047 : CollatzResearch.WordTrace tailWord_4128047 prefixEnd_4128047 235519141705635081203107 := by
  unfold tailWord_4128047
  simp only [CollatzResearch.WordTrace]
  refine ⟨150562243275798208143654395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100374828850532138762436263 150562243275798208143654395)
  ·
    refine ⟨225843364913697312215481593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150562243275798208143654395 225843364913697312215481593)
    ·
      refine ⟨169382523685272984161611195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225843364913697312215481593 169382523685272984161611195)
      ·
        refine ⟨254073785527909476242416793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169382523685272984161611195 254073785527909476242416793)
        ·
          refine ⟨190555339145932107181812595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254073785527909476242416793 190555339145932107181812595)
          ·
            refine ⟨285833008718898160772718893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190555339145932107181812595 285833008718898160772718893)
            ·
              refine ⟨107187378269586810289769585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285833008718898160772718893 107187378269586810289769585)
              ·
                refine ⟨80390533702190107717327189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107187378269586810289769585 80390533702190107717327189)
                ·
                  refine ⟨235519141705635081203107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80390533702190107717327189 235519141705635081203107)
                  ·
                    rfl

theorem cell23_4128047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 10].length) (baseStart_4128047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128047 prefixEnd_4128047 := by exact prefixLift 4128047
  have htrace : WordTrace (prefixWord ++ tailWord_4128047) baseStart_4128047 baseEnd_4128047 := by
    simpa [prefixWord, tailWord_4128047, baseEnd_4128047] using wordTrace_append hprefix tailTrace_4128047
  have hstable : (prefixWord ++ tailWord_4128047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128047).length < 2 ^ (prefixWord ++ tailWord_4128047).sum := by decide
  have hdescent : baseEnd_4128047 < baseStart_4128047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128051 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 3, 4]
def baseStart_4128051 : Nat := 118140960795 + 4128051 * 2 ^ 59
def prefixEnd_4128051 : Nat := 4983230072969 + 3 ^ 40 * 4128051 * 2
def baseEnd_4128051 : Nat := 706558109757777905059315

theorem tailTrace_4128051 : CollatzResearch.WordTrace tailWord_4128051 prefixEnd_4128051 706558109757777905059315 := by
  unfold tailWord_4128051
  simp only [CollatzResearch.WordTrace]
  refine ⟨150562389167783716826800007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100374926111855811217866671 150562389167783716826800007)
  ·
    refine ⟨225843583751675575240200011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150562389167783716826800007 225843583751675575240200011)
    ·
      refine ⟨338765375627513362860300017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225843583751675575240200011 338765375627513362860300017)
      ·
        refine ⟨254074031720635022145225013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338765375627513362860300017 254074031720635022145225013)
        ·
          refine ⟨23819440473809533326114845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254074031720635022145225013 23819440473809533326114845)
          ·
            refine ⟨8932290177678574997293067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23819440473809533326114845 8932290177678574997293067)
            ·
              refine ⟨13398435266517862495939601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932290177678574997293067 13398435266517862495939601)
              ·
                refine ⟨10048826449888396871954701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13398435266517862495939601 10048826449888396871954701)
                ·
                  refine ⟨3768309918708148826983013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10048826449888396871954701 3768309918708148826983013)
                  ·
                    refine ⟨706558109757777905059315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3768309918708148826983013 706558109757777905059315)
                    ·
                      rfl

theorem cell23_4128051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 4].length) (baseStart_4128051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128051 prefixEnd_4128051 := by exact prefixLift 4128051
  have htrace : WordTrace (prefixWord ++ tailWord_4128051) baseStart_4128051 baseEnd_4128051 := by
    simpa [prefixWord, tailWord_4128051, baseEnd_4128051] using wordTrace_append hprefix tailTrace_4128051
  have hstable : (prefixWord ++ tailWord_4128051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128051).length < 2 ^ (prefixWord ++ tailWord_4128051).sum := by decide
  have hdescent : baseEnd_4128051 < baseStart_4128051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128074 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_4128074 : Nat := 118140960795 + 4128074 * 2 ^ 59
def prefixEnd_4128074 : Nat := 4983230072969 + 3 ^ 40 * 4128074 * 2
def baseEnd_4128074 : Nat := 2119686139328387125190339

theorem tailTrace_4128074 : CollatzResearch.WordTrace tailWord_4128074 prefixEnd_4128074 2119686139328387125190339 := by
  unfold tailWord_4128074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640807011675097938721819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100375485364466927836591517 37640807011675097938721819)
  ·
    refine ⟨56461210517512646908082729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37640807011675097938721819 56461210517512646908082729)
    ·
      refine ⟨42345907888134485181062047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56461210517512646908082729 42345907888134485181062047)
      ·
        refine ⟨63518861832201727771593071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42345907888134485181062047 63518861832201727771593071)
        ·
          refine ⟨95278292748302591657389607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63518861832201727771593071 95278292748302591657389607)
          ·
            refine ⟨142917439122453887486084411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95278292748302591657389607 142917439122453887486084411)
            ·
              refine ⟨214376158683680831229126617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142917439122453887486084411 214376158683680831229126617)
              ·
                refine ⟨160782119012760623421844963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214376158683680831229126617 160782119012760623421844963)
                ·
                  refine ⟨241173178519140935132767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160782119012760623421844963 241173178519140935132767445)
                  ·
                    refine ⟨5652496371542365667174237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241173178519140935132767445 5652496371542365667174237)
                    ·
                      refine ⟨2119686139328387125190339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652496371542365667174237 2119686139328387125190339)
                      ·
                        rfl

theorem cell23_4128074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_4128074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128074 prefixEnd_4128074 := by exact prefixLift 4128074
  have htrace : WordTrace (prefixWord ++ tailWord_4128074) baseStart_4128074 baseEnd_4128074 := by
    simpa [prefixWord, tailWord_4128074, baseEnd_4128074] using wordTrace_append hprefix tailTrace_4128074
  have hstable : (prefixWord ++ tailWord_4128074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128074).length < 2 ^ (prefixWord ++ tailWord_4128074).sum := by decide
  have hdescent : baseEnd_4128074 < baseStart_4128074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128084 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4128084 : Nat := 118140960795 + 4128084 * 2 ^ 59
def prefixEnd_4128084 : Nat := 4983230072969 + 3 ^ 40 * 4128084 * 2
def baseEnd_4128084 : Nat := 2119691274134932086065293

theorem tailTrace_4128084 : CollatzResearch.WordTrace tailWord_4128084 prefixEnd_4128084 2119691274134932086065293 := by
  unfold tailWord_4128084
  simp only [CollatzResearch.WordTrace]
  refine ⟨75281796388332081731375653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100375728517776108975167537 75281796388332081731375653)
  ·
    refine ⟨14115336822812265324632935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75281796388332081731375653 14115336822812265324632935)
    ·
      refine ⟨21173005234218397986949403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14115336822812265324632935 21173005234218397986949403)
      ·
        refine ⟨31759507851327596980424105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21173005234218397986949403 31759507851327596980424105)
        ·
          refine ⟨23819630888495697735318079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31759507851327596980424105 23819630888495697735318079)
          ·
            refine ⟨35729446332743546602977119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819630888495697735318079 35729446332743546602977119)
            ·
              refine ⟨53594169499115319904465679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35729446332743546602977119 53594169499115319904465679)
              ·
                refine ⟨80391254248672979856698519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53594169499115319904465679 80391254248672979856698519)
                ·
                  refine ⟨120586881373009469785047779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80391254248672979856698519 120586881373009469785047779)
                  ·
                    refine ⟨180880322059514204677571669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120586881373009469785047779 180880322059514204677571669)
                    ·
                      refine ⟨2119691274134932086065293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180880322059514204677571669 2119691274134932086065293)
                      ·
                        rfl

theorem cell23_4128084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4128084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128084 prefixEnd_4128084 := by exact prefixLift 4128084
  have htrace : WordTrace (prefixWord ++ tailWord_4128084) baseStart_4128084 baseEnd_4128084 := by
    simpa [prefixWord, tailWord_4128084, baseEnd_4128084] using wordTrace_append hprefix tailTrace_4128084
  have hstable : (prefixWord ++ tailWord_4128084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128084).length < 2 ^ (prefixWord ++ tailWord_4128084).sum := by decide
  have hdescent : baseEnd_4128084 < baseStart_4128084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128098 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_4128098 : Nat := 118140960795 + 4128098 * 2 ^ 59
def prefixEnd_4128098 : Nat := 4983230072969 + 3 ^ 40 * 4128098 * 2
def baseEnd_4128098 : Nat := 235522051429343892365581

theorem tailTrace_4128098 : CollatzResearch.WordTrace tailWord_4128098 prefixEnd_4128098 235522051429343892365581 := by
  unfold tailWord_4128098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641025849653360963440237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100376068932408962569173965 37641025849653360963440237)
  ·
    refine ⟨14115384693620010361290089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37641025849653360963440237 14115384693620010361290089)
    ·
      refine ⟨10586538520215007770967567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14115384693620010361290089 10586538520215007770967567)
      ·
        refine ⟨15879807780322511656451351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586538520215007770967567 15879807780322511656451351)
        ·
          refine ⟨23819711670483767484677027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879807780322511656451351 23819711670483767484677027)
          ·
            refine ⟨35729567505725651227015541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819711670483767484677027 35729567505725651227015541)
            ·
              refine ⟨3349646953661779802532707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35729567505725651227015541 3349646953661779802532707)
              ·
                refine ⟨5024470430492669703799061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349646953661779802532707 5024470430492669703799061)
                ·
                  refine ⟨235522051429343892365581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5024470430492669703799061 235522051429343892365581)
                  ·
                    rfl

theorem cell23_4128098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_4128098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128098 prefixEnd_4128098 := by exact prefixLift 4128098
  have htrace : WordTrace (prefixWord ++ tailWord_4128098) baseStart_4128098 baseEnd_4128098 := by
    simpa [prefixWord, tailWord_4128098, baseEnd_4128098] using wordTrace_append hprefix tailTrace_4128098
  have hstable : (prefixWord ++ tailWord_4128098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128098).length < 2 ^ (prefixWord ++ tailWord_4128098).sum := by decide
  have hdescent : baseEnd_4128098 < baseStart_4128098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128101 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_4128101 : Nat := 118140960795 + 4128101 * 2 ^ 59
def prefixEnd_4128101 : Nat := 4983230072969 + 3 ^ 40 * 4128101 * 2
def baseEnd_4128101 : Nat := 2119700003306058519552715

theorem tailTrace_4128101 : CollatzResearch.WordTrace tailWord_4128101 prefixEnd_4128101 2119700003306058519552715 := by
  unfold tailWord_4128101
  simp only [CollatzResearch.WordTrace]
  refine ⟨150564212817602575366120157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100376141878401716910746771 150564212817602575366120157)
  ·
    refine ⟨56461579806600965762295059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150564212817602575366120157 56461579806600965762295059)
    ·
      refine ⟨84692369709901448643442589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56461579806600965762295059 84692369709901448643442589)
      ·
        refine ⟨31759638641213043241290971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84692369709901448643442589 31759638641213043241290971)
        ·
          refine ⟨47639457961819564861936457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31759638641213043241290971 47639457961819564861936457)
          ·
            refine ⟨35729593471364673646452343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47639457961819564861936457 35729593471364673646452343)
            ·
              refine ⟨53594390207047010469678515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35729593471364673646452343 53594390207047010469678515)
              ·
                refine ⟨80391585310570515704517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53594390207047010469678515 80391585310570515704517773)
                ·
                  refine ⟨30146844491463943389194165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80391585310570515704517773 30146844491463943389194165)
                  ·
                    refine ⟨2826266671074744692736953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30146844491463943389194165 2826266671074744692736953)
                    ·
                      refine ⟨2119700003306058519552715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826266671074744692736953 2119700003306058519552715)
                      ·
                        rfl

theorem cell23_4128101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_4128101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128101 prefixEnd_4128101 := by exact prefixLift 4128101
  have htrace : WordTrace (prefixWord ++ tailWord_4128101) baseStart_4128101 baseEnd_4128101 := by
    simpa [prefixWord, tailWord_4128101, baseEnd_4128101] using wordTrace_append hprefix tailTrace_4128101
  have hstable : (prefixWord ++ tailWord_4128101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128101).length < 2 ^ (prefixWord ++ tailWord_4128101).sum := by decide
  have hdescent : baseEnd_4128101 < baseStart_4128101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128108 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_4128108 : Nat := 118140960795 + 4128108 * 2 ^ 59
def prefixEnd_4128108 : Nat := 4983230072969 + 3 ^ 40 * 4128108 * 2
def baseEnd_4128108 : Nat := 2119703597670639992165183

theorem tailTrace_4128108 : CollatzResearch.WordTrace tailWord_4128108 prefixEnd_4128108 2119703597670639992165183 := by
  unfold tailWord_4128108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75282234064288607780812489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100376312085718143707749985 75282234064288607780812489)
  ·
    refine ⟨56461675548216455835609367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75282234064288607780812489 56461675548216455835609367)
    ·
      refine ⟨84692513322324683753414051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56461675548216455835609367 84692513322324683753414051)
      ·
        refine ⟨127038769983487025630121077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84692513322324683753414051 127038769983487025630121077)
        ·
          refine ⟨11909884685951908652823851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127038769983487025630121077 11909884685951908652823851)
          ·
            refine ⟨17864827028927862979235777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11909884685951908652823851 17864827028927862979235777)
            ·
              refine ⟨13398620271695897234426833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17864827028927862979235777 13398620271695897234426833)
              ·
                refine ⟨10048965203771922925820125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13398620271695897234426833 10048965203771922925820125)
                ·
                  refine ⟨3768361951414471097182547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10048965203771922925820125 3768361951414471097182547)
                  ·
                    refine ⟨5652542927121706645773821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768361951414471097182547 5652542927121706645773821)
                    ·
                      refine ⟨2119703597670639992165183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652542927121706645773821 2119703597670639992165183)
                      ·
                        rfl

theorem cell23_4128108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_4128108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128108 prefixEnd_4128108 := by exact prefixLift 4128108
  have htrace : WordTrace (prefixWord ++ tailWord_4128108) baseStart_4128108 baseEnd_4128108 := by
    simpa [prefixWord, tailWord_4128108, baseEnd_4128108] using wordTrace_append hprefix tailTrace_4128108
  have hstable : (prefixWord ++ tailWord_4128108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128108).length < 2 ^ (prefixWord ++ tailWord_4128108).sum := by decide
  have hdescent : baseEnd_4128108 < baseStart_4128108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128111 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 1, 5]
def baseStart_4128111 : Nat := 118140960795 + 4128111 * 2 ^ 59
def prefixEnd_4128111 : Nat := 4983230072969 + 3 ^ 40 * 4128111 * 2
def baseEnd_4128111 : Nat := 706568379370867826809223

theorem tailTrace_4128111 : CollatzResearch.WordTrace tailWord_4128111 prefixEnd_4128111 706568379370867826809223 := by
  unfold tailWord_4128111
  simp only [CollatzResearch.WordTrace]
  refine ⟨150564577547566347073984187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100376385031710898049322791 150564577547566347073984187)
  ·
    refine ⟨225846866321349520610976281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150564577547566347073984187 225846866321349520610976281)
    ·
      refine ⟨169385149741012140458232211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225846866321349520610976281 169385149741012140458232211)
      ·
        refine ⟨254077724611518210687348317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169385149741012140458232211 254077724611518210687348317)
        ·
          refine ⟨95279146729319329007755619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254077724611518210687348317 95279146729319329007755619)
          ·
            refine ⟨142918720093978993511633429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95279146729319329007755619 142918720093978993511633429)
            ·
              refine ⟨6699315004405265320857817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142918720093978993511633429 6699315004405265320857817)
              ·
                refine ⟨5024486253303948990643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6699315004405265320857817 5024486253303948990643363)
                ·
                  refine ⟨7536729379955923485965045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024486253303948990643363 7536729379955923485965045)
                  ·
                    refine ⟨706568379370867826809223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7536729379955923485965045 706568379370867826809223)
                    ·
                      rfl

theorem cell23_4128111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_4128111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128111 prefixEnd_4128111 := by exact prefixLift 4128111
  have htrace : WordTrace (prefixWord ++ tailWord_4128111) baseStart_4128111 baseEnd_4128111 := by
    simpa [prefixWord, tailWord_4128111, baseEnd_4128111] using wordTrace_append hprefix tailTrace_4128111
  have hstable : (prefixWord ++ tailWord_4128111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128111).length < 2 ^ (prefixWord ++ tailWord_4128111).sum := by decide
  have hdescent : baseEnd_4128111 < baseStart_4128111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128124 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_4128124 : Nat := 118140960795 + 4128124 * 2 ^ 59
def prefixEnd_4128124 : Nat := 4983230072969 + 3 ^ 40 * 4128124 * 2
def baseEnd_4128124 : Nat := 706570604453703976521703

theorem tailTrace_4128124 : CollatzResearch.WordTrace tailWord_4128124 prefixEnd_4128124 706570604453703976521703 := by
  unfold tailWord_4128124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75282525848259625147103713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100376701131012833529471617 75282525848259625147103713)
  ·
    refine ⟨56461894386194718860327785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75282525848259625147103713 56461894386194718860327785)
    ·
      refine ⟨42346420789646039145245839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56461894386194718860327785 42346420789646039145245839)
      ·
        refine ⟨63519631184469058717868759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42346420789646039145245839 63519631184469058717868759)
        ·
          refine ⟨95279446776703588076803139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63519631184469058717868759 95279446776703588076803139)
          ·
            refine ⟨142919170165055382115204709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95279446776703588076803139 142919170165055382115204709)
            ·
              refine ⟨26797344405947884146600883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142919170165055382115204709 26797344405947884146600883)
              ·
                refine ⟨40196016608921826219901325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26797344405947884146600883 40196016608921826219901325)
                ·
                  refine ⟨15073506228345684832462997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40196016608921826219901325 15073506228345684832462997)
                  ·
                    refine ⟨706570604453703976521703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15073506228345684832462997 706570604453703976521703)
                    ·
                      rfl

theorem cell23_4128124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_4128124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128124 prefixEnd_4128124 := by exact prefixLift 4128124
  have htrace : WordTrace (prefixWord ++ tailWord_4128124) baseStart_4128124 baseEnd_4128124 := by
    simpa [prefixWord, tailWord_4128124, baseEnd_4128124] using wordTrace_append hprefix tailTrace_4128124
  have hstable : (prefixWord ++ tailWord_4128124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128124).length < 2 ^ (prefixWord ++ tailWord_4128124).sum := by decide
  have hdescent : baseEnd_4128124 < baseStart_4128124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128142 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4128142 : Nat := 118140960795 + 4128142 * 2 ^ 59
def prefixEnd_4128142 : Nat := 4983230072969 + 3 ^ 40 * 4128142 * 2
def baseEnd_4128142 : Nat := 2119721056012892859140027

theorem tailTrace_4128142 : CollatzResearch.WordTrace tailWord_4128142 prefixEnd_4128142 2119721056012892859140027 := by
  unfold tailWord_4128142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820713526306754921045335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100377138806969359578908453 18820713526306754921045335)
  ·
    refine ⟨28231070289460132381568003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18820713526306754921045335 28231070289460132381568003)
    ·
      refine ⟨42346605434190198572352005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28231070289460132381568003 42346605434190198572352005)
      ·
        refine ⟨7939988518910662232316001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42346605434190198572352005 7939988518910662232316001)
        ·
          refine ⟨5954991389182996674237001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939988518910662232316001 5954991389182996674237001)
          ·
            refine ⟨4466243541887247505677751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5954991389182996674237001 4466243541887247505677751)
            ·
              refine ⟨6699365312830871258516627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466243541887247505677751 6699365312830871258516627)
              ·
                refine ⟨10049047969246306887774941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699365312830871258516627 10049047969246306887774941)
                ·
                  refine ⟨3768392988467365082915603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10049047969246306887774941 3768392988467365082915603)
                  ·
                    refine ⟨5652589482701047624373405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768392988467365082915603 5652589482701047624373405)
                    ·
                      refine ⟨2119721056012892859140027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652589482701047624373405 2119721056012892859140027)
                      ·
                        rfl

theorem cell23_4128142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4128142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128142 prefixEnd_4128142 := by exact prefixLift 4128142
  have htrace : WordTrace (prefixWord ++ tailWord_4128142) baseStart_4128142 baseEnd_4128142 := by
    simpa [prefixWord, tailWord_4128142, baseEnd_4128142] using wordTrace_append hprefix tailTrace_4128142
  have hstable : (prefixWord ++ tailWord_4128142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128142).length < 2 ^ (prefixWord ++ tailWord_4128142).sum := by decide
  have hdescent : baseEnd_4128142 < baseStart_4128142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128151 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_4128151 : Nat := 118140960795 + 4128151 * 2 ^ 59
def prefixEnd_4128151 : Nat := 4983230072969 + 3 ^ 40 * 4128151 * 2
def baseEnd_4128151 : Nat := 2119725677338783323927485

theorem tailTrace_4128151 : CollatzResearch.WordTrace tailWord_4128151 prefixEnd_4128151 2119725677338783323927485 := by
  unfold tailWord_4128151
  simp only [CollatzResearch.WordTrace]
  refine ⟨150566036467421433905440307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100377357644947622603626871 150566036467421433905440307)
  ·
    refine ⟨225849054701132150858160461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150566036467421433905440307 225849054701132150858160461)
    ·
      refine ⟨84693395512924556571810173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225849054701132150858160461 84693395512924556571810173)
      ·
        refine ⟨31760023317346708714428815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84693395512924556571810173 31760023317346708714428815)
        ·
          refine ⟨47640034976020063071643223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31760023317346708714428815 47640034976020063071643223)
          ·
            refine ⟨71460052464030094607464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47640034976020063071643223 71460052464030094607464835)
            ·
              refine ⟨107190078696045141911197253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71460052464030094607464835 107190078696045141911197253)
              ·
                refine ⟨20098139755508464108349485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107190078696045141911197253 20098139755508464108349485)
                ·
                  refine ⟨7536802408315674040631057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20098139755508464108349485 7536802408315674040631057)
                  ·
                    refine ⟨5652601806236755530473293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536802408315674040631057 5652601806236755530473293)
                    ·
                      refine ⟨2119725677338783323927485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652601806236755530473293 2119725677338783323927485)
                      ·
                        rfl

theorem cell23_4128151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_4128151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128151 prefixEnd_4128151 := by exact prefixLift 4128151
  have htrace : WordTrace (prefixWord ++ tailWord_4128151) baseStart_4128151 baseEnd_4128151 := by
    simpa [prefixWord, tailWord_4128151, baseEnd_4128151] using wordTrace_append hprefix tailTrace_4128151
  have hstable : (prefixWord ++ tailWord_4128151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128151).length < 2 ^ (prefixWord ++ tailWord_4128151).sum := by decide
  have hdescent : baseEnd_4128151 < baseStart_4128151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128185 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4128185 : Nat := 118140960795 + 4128185 * 2 ^ 59
def prefixEnd_4128185 : Nat := 4983230072969 + 3 ^ 40 * 4128185 * 2
def baseEnd_4128185 : Nat := 2119743135681036190902329

theorem tailTrace_4128185 : CollatzResearch.WordTrace tailWord_4128185 prefixEnd_4128185 2119743135681036190902329 := by
  unfold tailWord_4128185
  simp only [CollatzResearch.WordTrace]
  refine ⟨150567276549298257712178009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100378184366198838474785339 150567276549298257712178009)
  ·
    refine ⟨112925457411973693284133507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150567276549298257712178009 112925457411973693284133507)
    ·
      refine ⟨169388186117960539926200261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112925457411973693284133507 169388186117960539926200261)
      ·
        refine ⟨31760284897117601236162549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169388186117960539926200261 31760284897117601236162549)
        ·
          refine ⟨2977526709104775115890239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31760284897117601236162549 2977526709104775115890239)
          ·
            refine ⟨4466290063657162673835359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977526709104775115890239 4466290063657162673835359)
            ·
              refine ⟨6699435095485744010753039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466290063657162673835359 6699435095485744010753039)
              ·
                refine ⟨10049152643228616016129559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699435095485744010753039 10049152643228616016129559)
                ·
                  refine ⟨15073728964842924024194339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049152643228616016129559 15073728964842924024194339)
                  ·
                    refine ⟨22610593447264386036291509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15073728964842924024194339 22610593447264386036291509)
                    ·
                      refine ⟨2119743135681036190902329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22610593447264386036291509 2119743135681036190902329)
                      ·
                        rfl

theorem cell23_4128185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4128185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128185 prefixEnd_4128185 := by exact prefixLift 4128185
  have htrace : WordTrace (prefixWord ++ tailWord_4128185) baseStart_4128185 baseEnd_4128185 := by
    simpa [prefixWord, tailWord_4128185, baseEnd_4128185] using wordTrace_append hprefix tailTrace_4128185
  have hstable : (prefixWord ++ tailWord_4128185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128185).length < 2 ^ (prefixWord ++ tailWord_4128185).sum := by decide
  have hdescent : baseEnd_4128185 < baseStart_4128185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128242 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4128242 : Nat := 118140960795 + 4128242 * 2 ^ 59
def prefixEnd_4128242 : Nat := 4983230072969 + 3 ^ 40 * 4128242 * 2
def baseEnd_4128242 : Nat := 2119772404078342467889567

theorem tailTrace_4128242 : CollatzResearch.WordTrace tailWord_4128242 prefixEnd_4128242 2119772404078342467889567 := by
  unfold tailWord_4128242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37642338877522939111750745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100379570340061170964668653 37642338877522939111750745)
  ·
    refine ⟨28231754158142204333813059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37642338877522939111750745 28231754158142204333813059)
    ·
      refine ⟨42347631237213306500719589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28231754158142204333813059 42347631237213306500719589)
      ·
        refine ⟨7940180856977494968884923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42347631237213306500719589 7940180856977494968884923)
        ·
          refine ⟨11910271285466242453327385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940180856977494968884923 11910271285466242453327385)
          ·
            refine ⟨8932703464099681839995539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11910271285466242453327385 8932703464099681839995539)
            ·
              refine ⟨13399055196149522759993309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932703464099681839995539 13399055196149522759993309)
              ·
                refine ⟨5024645698556071034997491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13399055196149522759993309 5024645698556071034997491)
                ·
                  refine ⟨7536968547834106552496237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024645698556071034997491 7536968547834106552496237)
                  ·
                    refine ⟨2826363205437789957186089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7536968547834106552496237 2826363205437789957186089)
                    ·
                      refine ⟨2119772404078342467889567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826363205437789957186089 2119772404078342467889567)
                      ·
                        rfl

theorem cell23_4128242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4128242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128242 prefixEnd_4128242 := by exact prefixLift 4128242
  have htrace : WordTrace (prefixWord ++ tailWord_4128242) baseStart_4128242 baseEnd_4128242 := by
    simpa [prefixWord, tailWord_4128242, baseEnd_4128242] using wordTrace_append hprefix tailTrace_4128242
  have hstable : (prefixWord ++ tailWord_4128242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128242).length < 2 ^ (prefixWord ++ tailWord_4128242).sum := by decide
  have hdescent : baseEnd_4128242 < baseStart_4128242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128255 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 2, 2, 2]
def baseStart_4128255 : Nat := 118140960795 + 4128255 * 2 ^ 59
def prefixEnd_4128255 : Nat := 4983230072969 + 3 ^ 40 * 4128255 * 2
def baseEnd_4128255 : Nat := 2119779079326850917027007

theorem tailTrace_4128255 : CollatzResearch.WordTrace tailWord_4128255 prefixEnd_4128255 2119779079326850917027007 := by
  unfold tailWord_4128255
  simp only [CollatzResearch.WordTrace]
  refine ⟨150569829659044659667226219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100379886439363106444817479 150569829659044659667226219)
  ·
    refine ⟨225854744488566989500839329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150569829659044659667226219 225854744488566989500839329)
    ·
      refine ⟨169391058366425242125629497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225854744488566989500839329 169391058366425242125629497)
      ·
        refine ⟨127043293774818931594222123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169391058366425242125629497 127043293774818931594222123)
        ·
          refine ⟨190564940662228397391333185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127043293774818931594222123 190564940662228397391333185)
          ·
            refine ⟨142923705496671298043499889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190564940662228397391333185 142923705496671298043499889)
            ·
              refine ⟨107192779122503473532624917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142923705496671298043499889 107192779122503473532624917)
              ·
                refine ⟨5024661521367350321841793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107192779122503473532624917 5024661521367350321841793)
                ·
                  refine ⟨3768496141025512741381345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5024661521367350321841793 3768496141025512741381345)
                  ·
                    refine ⟨2826372105769134556036009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768496141025512741381345 2826372105769134556036009)
                    ·
                      refine ⟨2119779079326850917027007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826372105769134556036009 2119779079326850917027007)
                      ·
                        rfl

theorem cell23_4128255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_4128255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128255 prefixEnd_4128255 := by exact prefixLift 4128255
  have htrace : WordTrace (prefixWord ++ tailWord_4128255) baseStart_4128255 baseEnd_4128255 := by
    simpa [prefixWord, tailWord_4128255, baseEnd_4128255] using wordTrace_append hprefix tailTrace_4128255
  have hstable : (prefixWord ++ tailWord_4128255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128255).length < 2 ^ (prefixWord ++ tailWord_4128255).sum := by decide
  have hdescent : baseEnd_4128255 < baseStart_4128255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128271 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_4128271 : Nat := 118140960795 + 4128271 * 2 ^ 59
def prefixEnd_4128271 : Nat := 4983230072969 + 3 ^ 40 * 4128271 * 2
def baseEnd_4128271 : Nat := 2119787295017322854426933

theorem tailTrace_4128271 : CollatzResearch.WordTrace tailWord_4128271 prefixEnd_4128271 2119787295017322854426933 := by
  unfold tailWord_4128271
  simp only [CollatzResearch.WordTrace]
  refine ⟨150570413226986694399808667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100380275484657796266539111 150570413226986694399808667)
  ·
    refine ⟨225855619840480041599713001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150570413226986694399808667 225855619840480041599713001)
    ·
      refine ⟨169391714880360031199784751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225855619840480041599713001 169391714880360031199784751)
      ·
        refine ⟨254087572320540046799677127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169391714880360031199784751 254087572320540046799677127)
        ·
          refine ⟨381131358480810070199515691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254087572320540046799677127 381131358480810070199515691)
          ·
            refine ⟨571697037721215105299273537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381131358480810070199515691 571697037721215105299273537)
            ·
              refine ⟨428772778290911328974455153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571697037721215105299273537 428772778290911328974455153)
              ·
                refine ⟨321579583718183496730841365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428772778290911328974455153 321579583718183496730841365)
                ·
                  refine ⟨15074042986789851409258189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 321579583718183496730841365 15074042986789851409258189)
                  ·
                    refine ⟨5652766120046194278471821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15074042986789851409258189 5652766120046194278471821)
                    ·
                      refine ⟨2119787295017322854426933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652766120046194278471821 2119787295017322854426933)
                      ·
                        rfl

theorem cell23_4128271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_4128271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128271 prefixEnd_4128271 := by exact prefixLift 4128271
  have htrace : WordTrace (prefixWord ++ tailWord_4128271) baseStart_4128271 baseEnd_4128271 := by
    simpa [prefixWord, tailWord_4128271, baseEnd_4128271] using wordTrace_append hprefix tailTrace_4128271
  have hstable : (prefixWord ++ tailWord_4128271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128271).length < 2 ^ (prefixWord ++ tailWord_4128271).sum := by decide
  have hdescent : baseEnd_4128271 < baseStart_4128271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128341 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4128341 : Nat := 118140960795 + 4128341 * 2 ^ 59
def prefixEnd_4128341 : Nat := 4983230072969 + 3 ^ 40 * 4128341 * 2
def baseEnd_4128341 : Nat := 2119823238663137580551611

theorem tailTrace_4128341 : CollatzResearch.WordTrace tailWord_4128341 prefixEnd_4128341 2119823238663137580551611 := by
  unfold tailWord_4128341
  simp only [CollatzResearch.WordTrace]
  refine ⟨150572966336733096354856877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100381977557822064236571251 150572966336733096354856877)
  ·
    refine ⟨56464862376274911133071329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150572966336733096354856877 56464862376274911133071329)
    ·
      refine ⟨42348646782206183349803497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56464862376274911133071329 42348646782206183349803497)
      ·
        refine ⟨31761485086654637512352623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42348646782206183349803497 31761485086654637512352623)
        ·
          refine ⟨47642227629981956268528935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31761485086654637512352623 47642227629981956268528935)
          ·
            refine ⟨71463341444972934402793403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47642227629981956268528935 71463341444972934402793403)
            ·
              refine ⟨107195012167459401604190105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71463341444972934402793403 107195012167459401604190105)
              ·
                refine ⟨80396259125594551203142579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107195012167459401604190105 80396259125594551203142579)
                ·
                  refine ⟨120594388688391826804713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80396259125594551203142579 120594388688391826804713869)
                  ·
                    refine ⟨45222895758146935051767701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120594388688391826804713869 45222895758146935051767701)
                    ·
                      refine ⟨2119823238663137580551611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45222895758146935051767701 2119823238663137580551611)
                      ·
                        rfl

theorem cell23_4128341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4128341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128341 prefixEnd_4128341 := by exact prefixLift 4128341
  have htrace : WordTrace (prefixWord ++ tailWord_4128341) baseStart_4128341 baseEnd_4128341 := by
    simpa [prefixWord, tailWord_4128341, baseEnd_4128341] using wordTrace_append hprefix tailTrace_4128341
  have hstable : (prefixWord ++ tailWord_4128341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128341).length < 2 ^ (prefixWord ++ tailWord_4128341).sum := by decide
  have hdescent : baseEnd_4128341 < baseStart_4128341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128368 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 6]
def baseStart_4128368 : Nat := 118140960795 + 4128368 * 2 ^ 59
def prefixEnd_4128368 : Nat := 4983230072969 + 3 ^ 40 * 4128368 * 2
def baseEnd_4128368 : Nat := 235537455848978774990443

theorem tailTrace_4128368 : CollatzResearch.WordTrace tailWord_4128368 prefixEnd_4128368 235537455848978774990443 := by
  unfold tailWord_4128368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75286975553817639983044879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100382634071756853310726505 75286975553817639983044879)
  ·
    refine ⟨112930463330726459974567319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75286975553817639983044879 112930463330726459974567319)
    ·
      refine ⟨169395694996089689961850979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112930463330726459974567319 169395694996089689961850979)
      ·
        refine ⟨254093542494134534942776469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169395694996089689961850979 254093542494134534942776469)
        ·
          refine ⟨11910634804412556325442647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254093542494134534942776469 11910634804412556325442647)
          ·
            refine ⟨17865952206618834488163971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910634804412556325442647 17865952206618834488163971)
            ·
              refine ⟨26798928309928251732245957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17865952206618834488163971 26798928309928251732245957)
              ·
                refine ⟨5024799058111547199796117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26798928309928251732245957 5024799058111547199796117)
                ·
                  refine ⟨235537455848978774990443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5024799058111547199796117 235537455848978774990443)
                  ·
                    rfl

theorem cell23_4128368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_4128368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128368 prefixEnd_4128368 := by exact prefixLift 4128368
  have htrace : WordTrace (prefixWord ++ tailWord_4128368) baseStart_4128368 baseEnd_4128368 := by
    simpa [prefixWord, tailWord_4128368, baseEnd_4128368] using wordTrace_append hprefix tailTrace_4128368
  have hstable : (prefixWord ++ tailWord_4128368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128368).length < 2 ^ (prefixWord ++ tailWord_4128368).sum := by decide
  have hdescent : baseEnd_4128368 < baseStart_4128368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128395 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 3]
def baseStart_4128395 : Nat := 118140960795 + 4128395 * 2 ^ 59
def prefixEnd_4128395 : Nat := 4983230072969 + 3 ^ 40 * 4128395 * 2
def baseEnd_4128395 : Nat := 2119850966618480369276363

theorem tailTrace_4128395 : CollatzResearch.WordTrace tailWord_4128395 prefixEnd_4128395 2119850966618480369276363 := by
  unfold tailWord_4128395
  simp only [CollatzResearch.WordTrace]
  refine ⟨150574935878537463577322639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100383290585691642384881759 150574935878537463577322639)
  ·
    refine ⟨225862403817806195365983959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150574935878537463577322639 225862403817806195365983959)
    ·
      refine ⟨338793605726709293048975939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225862403817806195365983959 338793605726709293048975939)
      ·
        refine ⟨508190408590063939573463909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338793605726709293048975939 508190408590063939573463909)
        ·
          refine ⟨95285701610636988670024483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508190408590063939573463909 95285701610636988670024483)
          ·
            refine ⟨142928552415955483005036725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95285701610636988670024483 142928552415955483005036725)
            ·
              refine ⟨13399551788995826531722193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142928552415955483005036725 13399551788995826531722193)
              ·
                refine ⟨10049663841746869898791645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13399551788995826531722193 10049663841746869898791645)
                ·
                  refine ⟨3768623940655076212046867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10049663841746869898791645 3768623940655076212046867)
                  ·
                    refine ⟨5652935910982614318070301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768623940655076212046867 5652935910982614318070301)
                    ·
                      refine ⟨2119850966618480369276363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652935910982614318070301 2119850966618480369276363)
                      ·
                        rfl

theorem cell23_4128395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 3].length) (baseStart_4128395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128395 prefixEnd_4128395 := by exact prefixLift 4128395
  have htrace : WordTrace (prefixWord ++ tailWord_4128395) baseStart_4128395 baseEnd_4128395 := by
    simpa [prefixWord, tailWord_4128395, baseEnd_4128395] using wordTrace_append hprefix tailTrace_4128395
  have hstable : (prefixWord ++ tailWord_4128395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128395).length < 2 ^ (prefixWord ++ tailWord_4128395).sum := by decide
  have hdescent : baseEnd_4128395 < baseStart_4128395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128429 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4128429 : Nat := 118140960795 + 4128429 * 2 ^ 59
def prefixEnd_4128429 : Nat := 4983230072969 + 3 ^ 40 * 4128429 * 2
def baseEnd_4128429 : Nat := 2119868424960733236251207

theorem tailTrace_4128429 : CollatzResearch.WordTrace tailWord_4128429 prefixEnd_4128429 2119868424960733236251207 := by
  unfold tailWord_4128429
  simp only [CollatzResearch.WordTrace]
  refine ⟨150576175960414287384060341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100384117306942858256040227 150576175960414287384060341)
  ·
    refine ⟨14116516496288839442255657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150576175960414287384060341 14116516496288839442255657)
    ·
      refine ⟨10587387372216629581691743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14116516496288839442255657 10587387372216629581691743)
      ·
        refine ⟨15881081058324944372537615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10587387372216629581691743 15881081058324944372537615)
        ·
          refine ⟨23821621587487416558806423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15881081058324944372537615 23821621587487416558806423)
          ·
            refine ⟨35732432381231124838209635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821621587487416558806423 35732432381231124838209635)
            ·
              refine ⟨53598648571846687257314453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35732432381231124838209635 53598648571846687257314453)
              ·
                refine ⟨2512436651805313465186615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53598648571846687257314453 2512436651805313465186615)
                ·
                  refine ⟨3768654977707970197779923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512436651805313465186615 3768654977707970197779923)
                  ·
                    refine ⟨5652982466561955296669885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768654977707970197779923 5652982466561955296669885)
                    ·
                      refine ⟨2119868424960733236251207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5652982466561955296669885 2119868424960733236251207)
                      ·
                        rfl

theorem cell23_4128429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4128429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128429 prefixEnd_4128429 := by exact prefixLift 4128429
  have htrace : WordTrace (prefixWord ++ tailWord_4128429) baseStart_4128429 baseEnd_4128429 := by
    simpa [prefixWord, tailWord_4128429, baseEnd_4128429] using wordTrace_append hprefix tailTrace_4128429
  have hstable : (prefixWord ++ tailWord_4128429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128429).length < 2 ^ (prefixWord ++ tailWord_4128429).sum := by decide
  have hdescent : baseEnd_4128429 < baseStart_4128429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128448 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_4128448 : Nat := 118140960795 + 4128448 * 2 ^ 59
def prefixEnd_4128448 : Nat := 4983230072969 + 3 ^ 40 * 4128448 * 2
def baseEnd_4128448 : Nat := 2119878181093168661913619

theorem tailTrace_4128448 : CollatzResearch.WordTrace tailWord_4128448 prefixEnd_4128448 2119878181093168661913619 := by
  unfold tailWord_4128448
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288434473672726814500999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100384579298230302419334665 75288434473672726814500999)
  ·
    refine ⟨112932651710509090221751499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75288434473672726814500999 112932651710509090221751499)
    ·
      refine ⟨169398977565763635332627249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112932651710509090221751499 169398977565763635332627249)
      ·
        refine ⟨127049233174322726499470437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169398977565763635332627249 127049233174322726499470437)
        ·
          refine ⟨23821731220185511218650707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127049233174322726499470437 23821731220185511218650707)
          ·
            refine ⟨35732596830278266827976061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821731220185511218650707 35732596830278266827976061)
            ·
              refine ⟨13399723811354350060491023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35732596830278266827976061 13399723811354350060491023)
              ·
                refine ⟨20099585717031525090736535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13399723811354350060491023 20099585717031525090736535)
                ·
                  refine ⟨30149378575547287636104803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20099585717031525090736535 30149378575547287636104803)
                  ·
                    refine ⟨45224067863320931454157205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30149378575547287636104803 45224067863320931454157205)
                    ·
                      refine ⟨2119878181093168661913619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45224067863320931454157205 2119878181093168661913619)
                      ·
                        rfl

theorem cell23_4128448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_4128448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128448 prefixEnd_4128448 := by exact prefixLift 4128448
  have htrace : WordTrace (prefixWord ++ tailWord_4128448) baseStart_4128448 baseEnd_4128448 := by
    simpa [prefixWord, tailWord_4128448, baseEnd_4128448] using wordTrace_append hprefix tailTrace_4128448
  have hstable : (prefixWord ++ tailWord_4128448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128448).length < 2 ^ (prefixWord ++ tailWord_4128448).sum := by decide
  have hdescent : baseEnd_4128448 < baseStart_4128448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128452 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4128452 : Nat := 118140960795 + 4128452 * 2 ^ 59
def prefixEnd_4128452 : Nat := 4983230072969 + 3 ^ 40 * 4128452 * 2
def baseEnd_4128452 : Nat := 2119880235015786646263601

theorem tailTrace_4128452 : CollatzResearch.WordTrace tailWord_4128452 prefixEnd_4128452 2119880235015786646263601 := by
  unfold tailWord_4128452
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288507419665481156073805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100384676559553974874765073 75288507419665481156073805)
  ·
    refine ⟨28233190282374555433527677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75288507419665481156073805 28233190282374555433527677)
    ·
      refine ⟨10587446355890458287572879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28233190282374555433527677 10587446355890458287572879)
      ·
        refine ⟨15881169533835687431359319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10587446355890458287572879 15881169533835687431359319)
        ·
          refine ⟨23821754300753531147038979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15881169533835687431359319 23821754300753531147038979)
          ·
            refine ⟨35732631451130296720558469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821754300753531147038979 35732631451130296720558469)
            ·
              refine ⟨6699868397086930635104713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35732631451130296720558469 6699868397086930635104713)
              ·
                refine ⟨5024901297815197976328535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6699868397086930635104713 5024901297815197976328535)
                ·
                  refine ⟨7537351946722796964492803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024901297815197976328535 7537351946722796964492803)
                  ·
                    refine ⟨11306027920084195446739205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7537351946722796964492803 11306027920084195446739205)
                    ·
                      refine ⟨2119880235015786646263601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11306027920084195446739205 2119880235015786646263601)
                      ·
                        rfl

theorem cell23_4128452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4128452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128452 prefixEnd_4128452 := by exact prefixLift 4128452
  have htrace : WordTrace (prefixWord ++ tailWord_4128452) baseStart_4128452 baseEnd_4128452 := by
    simpa [prefixWord, tailWord_4128452, baseEnd_4128452] using wordTrace_append hprefix tailTrace_4128452
  have hstable : (prefixWord ++ tailWord_4128452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128452).length < 2 ^ (prefixWord ++ tailWord_4128452).sum := by decide
  have hdescent : baseEnd_4128452 < baseStart_4128452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128545 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4128545 : Nat := 118140960795 + 4128545 * 2 ^ 59
def prefixEnd_4128545 : Nat := 4983230072969 + 3 ^ 40 * 4128545 * 2
def baseEnd_4128545 : Nat := 2119927988716654782400673

theorem tailTrace_4128545 : CollatzResearch.WordTrace tailWord_4128545 prefixEnd_4128545 2119927988716654782400673 := by
  unfold tailWord_4128545
  simp only [CollatzResearch.WordTrace]
  refine ⟨150580406827994039195283089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100386937885329359463522059 150580406827994039195283089)
  ·
    refine ⟨112935305120995529396462317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150580406827994039195283089 112935305120995529396462317)
    ·
      refine ⟨42350739420373323523673369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112935305120995529396462317 42350739420373323523673369)
      ·
        refine ⟨31763054565279992642755027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42350739420373323523673369 31763054565279992642755027)
        ·
          refine ⟨47644581847919988964132541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763054565279992642755027 47644581847919988964132541)
          ·
            refine ⟨17866718192969995861549703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47644581847919988964132541 17866718192969995861549703)
            ·
              refine ⟨26800077289454993792324555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17866718192969995861549703 26800077289454993792324555)
              ·
                refine ⟨40200115934182490688486833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26800077289454993792324555 40200115934182490688486833)
                ·
                  refine ⟨30150086950636868016365125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40200115934182490688486833 30150086950636868016365125)
                  ·
                    refine ⟨5653141303244412753068461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30150086950636868016365125 5653141303244412753068461)
                    ·
                      refine ⟨2119927988716654782400673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5653141303244412753068461 2119927988716654782400673)
                      ·
                        rfl

theorem cell23_4128545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4128545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128545 prefixEnd_4128545 := by exact prefixLift 4128545
  have htrace : WordTrace (prefixWord ++ tailWord_4128545) baseStart_4128545 baseEnd_4128545 := by
    simpa [prefixWord, tailWord_4128545, baseEnd_4128545] using wordTrace_append hprefix tailTrace_4128545
  have hstable : (prefixWord ++ tailWord_4128545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128545).length < 2 ^ (prefixWord ++ tailWord_4128545).sum := by decide
  have hdescent : baseEnd_4128545 < baseStart_4128545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128615 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4128615 : Nat := 118140960795 + 4128615 * 2 ^ 59
def prefixEnd_4128615 : Nat := 4983230072969 + 3 ^ 40 * 4128615 * 2
def baseEnd_4128615 : Nat := 2119963932362469508525351

theorem tailTrace_4128615 : CollatzResearch.WordTrace tailWord_4128615 prefixEnd_4128615 2119963932362469508525351 := by
  unfold tailWord_4128615
  simp only [CollatzResearch.WordTrace]
  refine ⟨150582959937740441150331299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100388639958493627433554199 150582959937740441150331299)
  ·
    refine ⟨225874439906610661725496949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150582959937740441150331299 225874439906610661725496949)
    ·
      refine ⟨21175728741244749536765339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225874439906610661725496949 21175728741244749536765339)
      ·
        refine ⟨31763593111867124305148009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175728741244749536765339 31763593111867124305148009)
        ·
          refine ⟨23822694833900343228861007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31763593111867124305148009 23822694833900343228861007)
          ·
            refine ⟨35734042250850514843291511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23822694833900343228861007 35734042250850514843291511)
            ·
              refine ⟨53601063376275772264937267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35734042250850514843291511 53601063376275772264937267)
              ·
                refine ⟨80401595064413658397405901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53601063376275772264937267 80401595064413658397405901)
                ·
                  refine ⟨30150598149155121899027213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80401595064413658397405901 30150598149155121899027213)
                  ·
                    refine ⟨11306474305933170712135205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30150598149155121899027213 11306474305933170712135205)
                    ·
                      refine ⟨2119963932362469508525351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11306474305933170712135205 2119963932362469508525351)
                      ·
                        rfl

theorem cell23_4128615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4128615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128615 prefixEnd_4128615 := by exact prefixLift 4128615
  have htrace : WordTrace (prefixWord ++ tailWord_4128615) baseStart_4128615 baseEnd_4128615 := by
    simpa [prefixWord, tailWord_4128615, baseEnd_4128615] using wordTrace_append hprefix tailTrace_4128615
  have hstable : (prefixWord ++ tailWord_4128615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128615).length < 2 ^ (prefixWord ++ tailWord_4128615).sum := by decide
  have hdescent : baseEnd_4128615 < baseStart_4128615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128715 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 6]
def baseStart_4128715 : Nat := 118140960795 + 4128715 * 2 ^ 59
def prefixEnd_4128715 : Nat := 4983230072969 + 3 ^ 40 * 4128715 * 2
def baseEnd_4128715 : Nat := 706671760142639705758297

theorem tailTrace_4128715 : CollatzResearch.WordTrace tailWord_4128715 prefixEnd_4128715 706671760142639705758297 := by
  unfold tailWord_4128715
  simp only [CollatzResearch.WordTrace]
  refine ⟨150586607237378158228971599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100391071491585438819314399 150586607237378158228971599)
  ·
    refine ⟨225879910856067237343457399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150586607237378158228971599 225879910856067237343457399)
    ·
      refine ⟨338819866284100856015186099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225879910856067237343457399 338819866284100856015186099)
      ·
        refine ⟨508229799426151284022779149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338819866284100856015186099 508229799426151284022779149)
        ·
          refine ⟨190586174784806731508542181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508229799426151284022779149 190586174784806731508542181)
          ·
            refine ⟨35734907772151262157851659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190586174784806731508542181 35734907772151262157851659)
            ·
              refine ⟨53602361658226893236777489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35734907772151262157851659 53602361658226893236777489)
              ·
                refine ⟨40201771243670169927583117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53602361658226893236777489 40201771243670169927583117)
                ·
                  refine ⟨15075664216376313722843669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40201771243670169927583117 15075664216376313722843669)
                  ·
                    refine ⟨706671760142639705758297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15075664216376313722843669 706671760142639705758297)
                    ·
                      rfl

theorem cell23_4128715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_4128715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128715 prefixEnd_4128715 := by exact prefixLift 4128715
  have htrace : WordTrace (prefixWord ++ tailWord_4128715) baseStart_4128715 baseEnd_4128715 := by
    simpa [prefixWord, tailWord_4128715, baseEnd_4128715] using wordTrace_append hprefix tailTrace_4128715
  have hstable : (prefixWord ++ tailWord_4128715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128715).length < 2 ^ (prefixWord ++ tailWord_4128715).sum := by decide
  have hdescent : baseEnd_4128715 < baseStart_4128715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128743 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4128743 : Nat := 118140960795 + 4128743 * 2 ^ 59
def prefixEnd_4128743 : Nat := 4983230072969 + 3 ^ 40 * 4128743 * 2
def baseEnd_4128743 : Nat := 2120029657886245007724763

theorem tailTrace_4128743 : CollatzResearch.WordTrace tailWord_4128743 prefixEnd_4128743 2120029657886245007724763 := by
  unfold tailWord_4128743
  simp only [CollatzResearch.WordTrace]
  refine ⟨150587628481276719010990883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100391752320851146007327255 150587628481276719010990883)
  ·
    refine ⟨225881442721915078516486325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150587628481276719010990883 225881442721915078516486325)
    ·
      refine ⟨21176385255179538610920593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225881442721915078516486325 21176385255179538610920593)
      ·
        refine ⟨15882288941384653958190445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21176385255179538610920593 15882288941384653958190445)
        ·
          refine ⟨5955858353019245234321417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15882288941384653958190445 5955858353019245234321417)
          ·
            refine ⟨4466893764764433925741063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5955858353019245234321417 4466893764764433925741063)
            ·
              refine ⟨6700340647146650888611595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466893764764433925741063 6700340647146650888611595)
              ·
                refine ⟨10050510970719976332917393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700340647146650888611595 10050510970719976332917393)
                ·
                  refine ⟨7537883228039982249688045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050510970719976332917393 7537883228039982249688045)
                  ·
                    refine ⟨2826706210514993343633017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7537883228039982249688045 2826706210514993343633017)
                    ·
                      refine ⟨2120029657886245007724763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826706210514993343633017 2120029657886245007724763)
                      ·
                        rfl

theorem cell23_4128743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4128743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128743 prefixEnd_4128743 := by exact prefixLift 4128743
  have htrace : WordTrace (prefixWord ++ tailWord_4128743) baseStart_4128743 baseEnd_4128743 := by
    simpa [prefixWord, tailWord_4128743, baseEnd_4128743] using wordTrace_append hprefix tailTrace_4128743
  have hstable : (prefixWord ++ tailWord_4128743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128743).length < 2 ^ (prefixWord ++ tailWord_4128743).sum := by decide
  have hdescent : baseEnd_4128743 < baseStart_4128743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128752 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_4128752 : Nat := 118140960795 + 4128752 * 2 ^ 59
def prefixEnd_4128752 : Nat := 4983230072969 + 3 ^ 40 * 4128752 * 2
def baseEnd_4128752 : Nat := 2120034279212135472512221

theorem tailTrace_4128752 : CollatzResearch.WordTrace tailWord_4128752 prefixEnd_4128752 2120034279212135472512221 := by
  unfold tailWord_4128752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75293978369122056774034255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100391971158829409032045673 75293978369122056774034255)
  ·
    refine ⟨112940967553683085161051383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75293978369122056774034255 112940967553683085161051383)
    ·
      refine ⟨169411451330524627741577075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112940967553683085161051383 169411451330524627741577075)
      ·
        refine ⟨254117176995786941612365613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169411451330524627741577075 254117176995786941612365613)
        ·
          refine ⟨95293941373420103104637105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254117176995786941612365613 95293941373420103104637105)
          ·
            refine ⟨71470456030065077328477829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95293941373420103104637105 71470456030065077328477829)
            ·
              refine ⟨13400710505637201999089593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71470456030065077328477829 13400710505637201999089593)
              ·
                refine ⟨10050532879227901499317195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13400710505637201999089593 10050532879227901499317195)
                ·
                  refine ⟨15075799318841852248975793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050532879227901499317195 15075799318841852248975793)
                  ·
                    refine ⟨11306849489131389186731845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15075799318841852248975793 11306849489131389186731845)
                    ·
                      refine ⟨2120034279212135472512221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11306849489131389186731845 2120034279212135472512221)
                      ·
                        rfl

theorem cell23_4128752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_4128752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128752 prefixEnd_4128752 := by exact prefixLift 4128752
  have htrace : WordTrace (prefixWord ++ tailWord_4128752) baseStart_4128752 baseEnd_4128752 := by
    simpa [prefixWord, tailWord_4128752, baseEnd_4128752] using wordTrace_append hprefix tailTrace_4128752
  have hstable : (prefixWord ++ tailWord_4128752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128752).length < 2 ^ (prefixWord ++ tailWord_4128752).sum := by decide
  have hdescent : baseEnd_4128752 < baseStart_4128752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128753 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_4128753 : Nat := 118140960795 + 4128753 * 2 ^ 59
def prefixEnd_4128753 : Nat := 4983230072969 + 3 ^ 40 * 4128753 * 2
def baseEnd_4128753 : Nat := 706678264230929989533239

theorem tailTrace_4128753 : CollatzResearch.WordTrace tailWord_4128753 prefixEnd_4128753 706678264230929989533239 := by
  unfold tailWord_4128753
  simp only [CollatzResearch.WordTrace]
  refine ⟨150587993211240490718854913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100391995474160327145903275 150587993211240490718854913)
  ·
    refine ⟨112940994908430368039141185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150587993211240490718854913 112940994908430368039141185)
    ·
      refine ⟨84705746181322776029355889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112940994908430368039141185 84705746181322776029355889)
      ·
        refine ⟨63529309635992082022016917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84705746181322776029355889 63529309635992082022016917)
        ·
          refine ⟨2977936389187128844782043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63529309635992082022016917 2977936389187128844782043)
          ·
            refine ⟨4466904583780693267173065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977936389187128844782043 4466904583780693267173065)
            ·
              refine ⟨3350178437835519950379799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466904583780693267173065 3350178437835519950379799)
              ·
                refine ⟨5025267656753279925569699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350178437835519950379799 5025267656753279925569699)
                ·
                  refine ⟨7537901485129919888354549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025267656753279925569699 7537901485129919888354549)
                  ·
                    refine ⟨706678264230929989533239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7537901485129919888354549 706678264230929989533239)
                    ·
                      rfl

theorem cell23_4128753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_4128753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128753 prefixEnd_4128753 := by exact prefixLift 4128753
  have htrace : WordTrace (prefixWord ++ tailWord_4128753) baseStart_4128753 baseEnd_4128753 := by
    simpa [prefixWord, tailWord_4128753, baseEnd_4128753] using wordTrace_append hprefix tailTrace_4128753
  have hstable : (prefixWord ++ tailWord_4128753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128753).length < 2 ^ (prefixWord ++ tailWord_4128753).sum := by decide
  have hdescent : baseEnd_4128753 < baseStart_4128753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128766 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4128766 : Nat := 118140960795 + 4128766 * 2 ^ 59
def prefixEnd_4128766 : Nat := 4983230072969 + 3 ^ 40 * 4128766 * 2
def baseEnd_4128766 : Nat := 706680489313766139245719

theorem tailTrace_4128766 : CollatzResearch.WordTrace tailWord_4128766 prefixEnd_4128766 706680489313766139245719 := by
  unfold tailWord_4128766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823558420024174242384769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100392311573462262626052101 18823558420024174242384769)
  ·
    refine ⟨14117668815018130681788577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18823558420024174242384769 14117668815018130681788577)
    ·
      refine ⟨10588251611263598011341433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14117668815018130681788577 10588251611263598011341433)
      ·
        refine ⟨7941188708447698508506075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10588251611263598011341433 7941188708447698508506075)
        ·
          refine ⟨11911783062671547762759113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941188708447698508506075 11911783062671547762759113)
          ·
            refine ⟨8933837297003660822069335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11911783062671547762759113 8933837297003660822069335)
            ·
              refine ⟨13400755945505491233104003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8933837297003660822069335 13400755945505491233104003)
              ·
                refine ⟨20101133918258236849656005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13400755945505491233104003 20101133918258236849656005)
                ·
                  refine ⟨3768962609673419409310501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20101133918258236849656005 3768962609673419409310501)
                  ·
                    refine ⟨706680489313766139245719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3768962609673419409310501 706680489313766139245719)
                    ·
                      rfl

theorem cell23_4128766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4128766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128766 prefixEnd_4128766 := by exact prefixLift 4128766
  have htrace : WordTrace (prefixWord ++ tailWord_4128766) baseStart_4128766 baseEnd_4128766 := by
    simpa [prefixWord, tailWord_4128766, baseEnd_4128766] using wordTrace_append hprefix tailTrace_4128766
  have hstable : (prefixWord ++ tailWord_4128766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128766).length < 2 ^ (prefixWord ++ tailWord_4128766).sum := by decide
  have hdescent : baseEnd_4128766 < baseStart_4128766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128773 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_4128773 : Nat := 118140960795 + 4128773 * 2 ^ 59
def prefixEnd_4128773 : Nat := 4983230072969 + 3 ^ 40 * 4128773 * 2
def baseEnd_4128773 : Nat := 2120045062305879890349625

theorem tailTrace_4128773 : CollatzResearch.WordTrace tailWord_4128773 prefixEnd_4128773 2120045062305879890349625 := by
  unfold tailWord_4128773
  simp only [CollatzResearch.WordTrace]
  refine ⟨150588722671168034134582973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100392481780778689423055315 150588722671168034134582973)
  ·
    refine ⟨56470771001688012800468615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150588722671168034134582973 56470771001688012800468615)
    ·
      refine ⟨84706156502532019200702923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56470771001688012800468615 84706156502532019200702923)
      ·
        refine ⟨127059234753798028801054385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84706156502532019200702923 127059234753798028801054385)
        ·
          refine ⟨95294426065348521600790789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127059234753798028801054385 95294426065348521600790789)
          ·
            refine ⟨17867704887252847800148273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95294426065348521600790789 17867704887252847800148273)
            ·
              refine ⟨13400778665439635850111205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17867704887252847800148273 13400778665439635850111205)
              ·
                refine ⟨2512645999769931721895851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13400778665439635850111205 2512645999769931721895851)
                ·
                  refine ⟨3768968999654897582843777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512645999769931721895851 3768968999654897582843777)
                  ·
                    refine ⟨2826726749741173187132833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768968999654897582843777 2826726749741173187132833)
                    ·
                      refine ⟨2120045062305879890349625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826726749741173187132833 2120045062305879890349625)
                      ·
                        rfl

theorem cell23_4128773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_4128773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128773 prefixEnd_4128773 := by exact prefixLift 4128773
  have htrace : WordTrace (prefixWord ++ tailWord_4128773) baseStart_4128773 baseEnd_4128773 := by
    simpa [prefixWord, tailWord_4128773, baseEnd_4128773] using wordTrace_append hprefix tailTrace_4128773
  have hstable : (prefixWord ++ tailWord_4128773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128773).length < 2 ^ (prefixWord ++ tailWord_4128773).sum := by decide
  have hdescent : baseEnd_4128773 < baseStart_4128773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128795 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_4128795 : Nat := 118140960795 + 4128795 * 2 ^ 59
def prefixEnd_4128795 : Nat := 4983230072969 + 3 ^ 40 * 4128795 * 2
def baseEnd_4128795 : Nat := 2120056358880278804274523

theorem tailTrace_4128795 : CollatzResearch.WordTrace tailWord_4128795 prefixEnd_4128795 2120056358880278804274523 := by
  unfold tailWord_4128795
  simp only [CollatzResearch.WordTrace]
  refine ⟨150589525077088331891883839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100393016718058887927922559 150589525077088331891883839)
  ·
    refine ⟨225884287615632497837825759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150589525077088331891883839 225884287615632497837825759)
    ·
      refine ⟨338826431423448746756738639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225884287615632497837825759 338826431423448746756738639)
      ·
        refine ⟨508239647135173120135107959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338826431423448746756738639 508239647135173120135107959)
        ·
          refine ⟨762359470702759680202661939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508239647135173120135107959 762359470702759680202661939)
          ·
            refine ⟨1143539206054139520303992909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762359470702759680202661939 1143539206054139520303992909)
            ·
              refine ⟨428827202270302320113997341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143539206054139520303992909 428827202270302320113997341)
              ·
                refine ⟨160810200851363370042749003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428827202270302320113997341 160810200851363370042749003)
                ·
                  refine ⟨241215301277045055064123505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160810200851363370042749003 241215301277045055064123505)
                  ·
                    refine ⟨180911475957783791298092629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241215301277045055064123505 180911475957783791298092629)
                    ·
                      refine ⟨2120056358880278804274523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180911475957783791298092629 2120056358880278804274523)
                      ·
                        rfl

theorem cell23_4128795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_4128795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128795 prefixEnd_4128795 := by exact prefixLift 4128795
  have htrace : WordTrace (prefixWord ++ tailWord_4128795) baseStart_4128795 baseEnd_4128795 := by
    simpa [prefixWord, tailWord_4128795, baseEnd_4128795] using wordTrace_append hprefix tailTrace_4128795
  have hstable : (prefixWord ++ tailWord_4128795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128795).length < 2 ^ (prefixWord ++ tailWord_4128795).sum := by decide
  have hdescent : baseEnd_4128795 < baseStart_4128795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128802 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4128802 : Nat := 118140960795 + 4128802 * 2 ^ 59
def prefixEnd_4128802 : Nat := 4983230072969 + 3 ^ 40 * 4128802 * 2
def baseEnd_4128802 : Nat := 2120059953244860276886991

theorem tailTrace_4128802 : CollatzResearch.WordTrace tailWord_4128802 prefixEnd_4128802 2120059953244860276886991 := by
  unfold tailWord_4128802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647445097015743021847165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100393186925375314724925773 37647445097015743021847165)
  ·
    refine ⟨14117791911380903633192687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37647445097015743021847165 14117791911380903633192687)
    ·
      refine ⟨21176687867071355449789031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14117791911380903633192687 21176687867071355449789031)
      ·
        refine ⟨31765031800607033174683547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176687867071355449789031 31765031800607033174683547)
        ·
          refine ⟨47647547700910549762025321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31765031800607033174683547 47647547700910549762025321)
          ·
            refine ⟨35735660775682912321518991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47647547700910549762025321 35735660775682912321518991)
            ·
              refine ⟨53603491163524368482278487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35735660775682912321518991 53603491163524368482278487)
              ·
                refine ⟨80405236745286552723417731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53603491163524368482278487 80405236745286552723417731)
                ·
                  refine ⟨120607855117929829085126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80405236745286552723417731 120607855117929829085126597)
                  ·
                    refine ⟨22613972834611842953461237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120607855117929829085126597 22613972834611842953461237)
                    ·
                      refine ⟨2120059953244860276886991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22613972834611842953461237 2120059953244860276886991)
                      ·
                        rfl

theorem cell23_4128802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4128802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128802 prefixEnd_4128802 := by exact prefixLift 4128802
  have htrace : WordTrace (prefixWord ++ tailWord_4128802) baseStart_4128802 baseEnd_4128802 := by
    simpa [prefixWord, tailWord_4128802, baseEnd_4128802] using wordTrace_append hprefix tailTrace_4128802
  have hstable : (prefixWord ++ tailWord_4128802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128802).length < 2 ^ (prefixWord ++ tailWord_4128802).sum := by decide
  have hdescent : baseEnd_4128802 < baseStart_4128802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128816 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2]
def baseStart_4128816 : Nat := 118140960795 + 4128816 * 2 ^ 59
def prefixEnd_4128816 : Nat := 4983230072969 + 3 ^ 40 * 4128816 * 2
def baseEnd_4128816 : Nat := 2120067141974023222111927

theorem tailTrace_4128816 : CollatzResearch.WordTrace tailWord_4128816 prefixEnd_4128816 2120067141974023222111927 := by
  unfold tailWord_4128816
  simp only [CollatzResearch.WordTrace]
  refine ⟨75295145505006126239199151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100393527340008168318932201 75295145505006126239199151)
  ·
    refine ⟨112942718257509189358798727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75295145505006126239199151 112942718257509189358798727)
    ·
      refine ⟨169414077386263784038198091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112942718257509189358798727 169414077386263784038198091)
      ·
        refine ⟨254121116079395676057297137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169414077386263784038198091 254121116079395676057297137)
        ·
          refine ⟨190590837059546757042972853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254121116079395676057297137 190590837059546757042972853)
          ·
            refine ⟨17867890974332508472778705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190590837059546757042972853 17867890974332508472778705)
            ·
              refine ⟨13400918230749381354584029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17867890974332508472778705 13400918230749381354584029)
              ·
                refine ⟨5025344336531018007969011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13400918230749381354584029 5025344336531018007969011)
                ·
                  refine ⟨7538016504796527011953517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025344336531018007969011 7538016504796527011953517)
                  ·
                    refine ⟨2826756189298697629482569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7538016504796527011953517 2826756189298697629482569)
                    ·
                      refine ⟨2120067141974023222111927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826756189298697629482569 2120067141974023222111927)
                      ·
                        rfl

theorem cell23_4128816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2].length) (baseStart_4128816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128816 prefixEnd_4128816 := by exact prefixLift 4128816
  have htrace : WordTrace (prefixWord ++ tailWord_4128816) baseStart_4128816 baseEnd_4128816 := by
    simpa [prefixWord, tailWord_4128816, baseEnd_4128816] using wordTrace_append hprefix tailTrace_4128816
  have hstable : (prefixWord ++ tailWord_4128816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128816).length < 2 ^ (prefixWord ++ tailWord_4128816).sum := by decide
  have hdescent : baseEnd_4128816 < baseStart_4128816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128842 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4128842 : Nat := 118140960795 + 4128842 * 2 ^ 59
def prefixEnd_4128842 : Nat := 4983230072969 + 3 ^ 40 * 4128842 * 2
def baseEnd_4128842 : Nat := 2120080492471040120386807

theorem tailTrace_4128842 : CollatzResearch.WordTrace tailWord_4128842 prefixEnd_4128842 2120080492471040120386807 := by
  unfold tailWord_4128842
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647809826979514729711195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100394159538612039279229853 37647809826979514729711195)
  ·
    refine ⟨56471714740469272094566793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37647809826979514729711195 56471714740469272094566793)
    ·
      refine ⟨42353786055351954070925095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56471714740469272094566793 42353786055351954070925095)
      ·
        refine ⟨63530679083027931106387643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42353786055351954070925095 63530679083027931106387643)
        ·
          refine ⟨95296018624541896659581465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63530679083027931106387643 95296018624541896659581465)
          ·
            refine ⟨71472013968406422494686099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95296018624541896659581465 71472013968406422494686099)
            ·
              refine ⟨107208020952609633742029149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71472013968406422494686099 107208020952609633742029149)
              ·
                refine ⟨40203007857228612653260931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107208020952609633742029149 40203007857228612653260931)
                ·
                  refine ⟨60304511785842918979891397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40203007857228612653260931 60304511785842918979891397)
                  ·
                    refine ⟨11307095959845547308729637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60304511785842918979891397 11307095959845547308729637)
                    ·
                      refine ⟨2120080492471040120386807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11307095959845547308729637 2120080492471040120386807)
                      ·
                        rfl

theorem cell23_4128842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4128842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128842 prefixEnd_4128842 := by exact prefixLift 4128842
  have htrace : WordTrace (prefixWord ++ tailWord_4128842) baseStart_4128842 baseEnd_4128842 := by
    simpa [prefixWord, tailWord_4128842, baseEnd_4128842] using wordTrace_append hprefix tailTrace_4128842
  have hstable : (prefixWord ++ tailWord_4128842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128842).length < 2 ^ (prefixWord ++ tailWord_4128842).sum := by decide
  have hdescent : baseEnd_4128842 < baseStart_4128842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128850 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_4128850 : Nat := 118140960795 + 4128850 * 2 ^ 59
def prefixEnd_4128850 : Nat := 4983230072969 + 3 ^ 40 * 4128850 * 2
def baseEnd_4128850 : Nat := 2120084600316276089086771

theorem tailTrace_4128850 : CollatzResearch.WordTrace tailWord_4128850 prefixEnd_4128850 2120084600316276089086771 := by
  unfold tailWord_4128850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647882772972269071284001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100394354061259384190090669 37647882772972269071284001)
  ·
    refine ⟨28235912079729201803463001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37647882772972269071284001 28235912079729201803463001)
    ·
      refine ⟨21176934059796901352597251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28235912079729201803463001 21176934059796901352597251)
      ·
        refine ⟨31765401089695352028895877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176934059796901352597251 31765401089695352028895877)
        ·
          refine ⟨5956012704317878505417977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31765401089695352028895877 5956012704317878505417977)
          ·
            refine ⟨4467009528238408879063483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956012704317878505417977 4467009528238408879063483)
            ·
              refine ⟨6700514292357613318595225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467009528238408879063483 6700514292357613318595225)
              ·
                refine ⟨5025385719268209988946419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700514292357613318595225 5025385719268209988946419)
                ·
                  refine ⟨7538078578902314983419629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025385719268209988946419 7538078578902314983419629)
                  ·
                    refine ⟨2826779467088368118782361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7538078578902314983419629 2826779467088368118782361)
                    ·
                      refine ⟨2120084600316276089086771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826779467088368118782361 2120084600316276089086771)
                      ·
                        rfl

theorem cell23_4128850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_4128850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128850 prefixEnd_4128850 := by exact prefixLift 4128850
  have htrace : WordTrace (prefixWord ++ tailWord_4128850) baseStart_4128850 baseEnd_4128850 := by
    simpa [prefixWord, tailWord_4128850, baseEnd_4128850] using wordTrace_append hprefix tailTrace_4128850
  have hstable : (prefixWord ++ tailWord_4128850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128850).length < 2 ^ (prefixWord ++ tailWord_4128850).sum := by decide
  have hdescent : baseEnd_4128850 < baseStart_4128850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128852 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 9]
def baseStart_4128852 : Nat := 118140960795 + 4128852 * 2 ^ 59
def prefixEnd_4128852 : Nat := 4983230072969 + 3 ^ 40 * 4128852 * 2
def baseEnd_4128852 : Nat := 235565069697509453473529

theorem tailTrace_4128852 : CollatzResearch.WordTrace tailWord_4128852 prefixEnd_4128852 235565069697509453473529 := by
  unfold tailWord_4128852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75295802018940915313354405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100394402691921220417805873 75295802018940915313354405)
  ·
    refine ⟨14117962878551421621253951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75295802018940915313354405 14117962878551421621253951)
    ·
      refine ⟨21176944317827132431880927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14117962878551421621253951 21176944317827132431880927)
      ·
        refine ⟨31765416476740698647821391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176944317827132431880927 31765416476740698647821391)
        ·
          refine ⟨47648124715111047971732087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31765416476740698647821391 47648124715111047971732087)
          ·
            refine ⟨71472187072666571957598131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47648124715111047971732087 71472187072666571957598131)
            ·
              refine ⟨107208280608999857936397197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71472187072666571957598131 107208280608999857936397197)
              ·
                refine ⟨40203105228374946726148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107208280608999857936397197 40203105228374946726148949)
                ·
                  refine ⟨235565069697509453473529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40203105228374946726148949 235565069697509453473529)
                  ·
                    rfl

theorem cell23_4128852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_4128852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128852 prefixEnd_4128852 := by exact prefixLift 4128852
  have htrace : WordTrace (prefixWord ++ tailWord_4128852) baseStart_4128852 baseEnd_4128852 := by
    simpa [prefixWord, tailWord_4128852, baseEnd_4128852] using wordTrace_append hprefix tailTrace_4128852
  have hstable : (prefixWord ++ tailWord_4128852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128852).length < 2 ^ (prefixWord ++ tailWord_4128852).sum := by decide
  have hdescent : baseEnd_4128852 < baseStart_4128852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128918 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4128918 : Nat := 118140960795 + 4128918 * 2 ^ 59
def prefixEnd_4128918 : Nat := 4983230072969 + 3 ^ 40 * 4128918 * 2
def baseEnd_4128918 : Nat := 2120119517000781823036459

theorem tailTrace_4128918 : CollatzResearch.WordTrace tailWord_4128918 prefixEnd_4128918 2120119517000781823036459 := by
  unfold tailWord_4128918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412125703477670243663213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100396007503761815932407605 9412125703477670243663213)
  ·
    refine ⟨3529547138804126341373705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9412125703477670243663213 3529547138804126341373705)
    ·
      refine ⟨2647160354103094756030279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3529547138804126341373705 2647160354103094756030279)
      ·
        refine ⟨3970740531154642134045419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647160354103094756030279 3970740531154642134045419)
        ·
          refine ⟨5956110796731963201068129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970740531154642134045419 5956110796731963201068129)
          ·
            refine ⟨4467083097548972400801097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956110796731963201068129 4467083097548972400801097)
            ·
              refine ⟨3350312323161729300600823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467083097548972400801097 3350312323161729300600823)
              ·
                refine ⟨5025468484742593950901235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350312323161729300600823 5025468484742593950901235)
                ·
                  refine ⟨7538202727113890926351853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025468484742593950901235 7538202727113890926351853)
                  ·
                    refine ⟨2826826022667709097381945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7538202727113890926351853 2826826022667709097381945)
                    ·
                      refine ⟨2120119517000781823036459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2826826022667709097381945 2120119517000781823036459)
                      ·
                        rfl

theorem cell23_4128918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4128918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128918 prefixEnd_4128918 := by exact prefixLift 4128918
  have htrace : WordTrace (prefixWord ++ tailWord_4128918) baseStart_4128918 baseEnd_4128918 := by
    simpa [prefixWord, tailWord_4128918, baseEnd_4128918] using wordTrace_append hprefix tailTrace_4128918
  have hstable : (prefixWord ++ tailWord_4128918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128918).length < 2 ^ (prefixWord ++ tailWord_4128918).sum := by decide
  have hdescent : baseEnd_4128918 < baseStart_4128918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128946 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_4128946 : Nat := 118140960795 + 4128946 * 2 ^ 59
def prefixEnd_4128946 : Nat := 4983230072969 + 3 ^ 40 * 4128946 * 2
def baseEnd_4128946 : Nat := 706711298153035904495443

theorem tailTrace_4128946 : CollatzResearch.WordTrace tailWord_4128946 prefixEnd_4128946 706711298153035904495443 := by
  unfold tailWord_4128946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37648758124885321170157673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100396688333027523120420461 37648758124885321170157673)
  ·
    refine ⟨28236568593663990877618255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37648758124885321170157673 28236568593663990877618255)
    ·
      refine ⟨42354852890495986316427383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28236568593663990877618255 42354852890495986316427383)
      ·
        refine ⟨63532279335743979474641075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42354852890495986316427383 63532279335743979474641075)
        ·
          refine ⟨95298419003615969211961613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63532279335743979474641075 95298419003615969211961613)
          ·
            refine ⟨35736907126355988454485605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95298419003615969211961613 35736907126355988454485605)
            ·
              refine ⟨6700670086191747835216051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35736907126355988454485605 6700670086191747835216051)
              ·
                refine ⟨10051005129287621752824077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700670086191747835216051 10051005129287621752824077)
                ·
                  refine ⟨3769126923482858157309029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10051005129287621752824077 3769126923482858157309029)
                  ·
                    refine ⟨706711298153035904495443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3769126923482858157309029 706711298153035904495443)
                    ·
                      rfl

theorem cell23_4128946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_4128946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128946 prefixEnd_4128946 := by exact prefixLift 4128946
  have htrace : WordTrace (prefixWord ++ tailWord_4128946) baseStart_4128946 baseEnd_4128946 := by
    simpa [prefixWord, tailWord_4128946, baseEnd_4128946] using wordTrace_append hprefix tailTrace_4128946
  have hstable : (prefixWord ++ tailWord_4128946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128946).length < 2 ^ (prefixWord ++ tailWord_4128946).sum := by decide
  have hdescent : baseEnd_4128946 < baseStart_4128946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128986 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_4128986 : Nat := 118140960795 + 4128986 * 2 ^ 59
def prefixEnd_4128986 : Nat := 4983230072969 + 3 ^ 40 * 4128986 * 2
def baseEnd_4128986 : Nat := 2120154433685287556986145

theorem tailTrace_4128986 : CollatzResearch.WordTrace tailWord_4128986 prefixEnd_4128986 2120154433685287556986145 := by
  unfold tailWord_4128986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37649122854849092878021703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100397660946264247674724541 37649122854849092878021703)
  ·
    refine ⟨56473684282273639317032555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37649122854849092878021703 56473684282273639317032555)
    ·
      refine ⟨84710526423410458975548833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56473684282273639317032555 84710526423410458975548833)
      ·
        refine ⟨63532894817557844231661625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84710526423410458975548833 63532894817557844231661625)
        ·
          refine ⟨47649671113168383173746219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63532894817557844231661625 47649671113168383173746219)
          ·
            refine ⟨71474506669752574760619329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47649671113168383173746219 71474506669752574760619329)
            ·
              refine ⟨53605880002314431070464497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71474506669752574760619329 53605880002314431070464497)
              ·
                refine ⟨40204410001735823302848373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53605880002314431070464497 40204410001735823302848373)
                ·
                  refine ⟨3769163437662733434642035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40204410001735823302848373 3769163437662733434642035)
                  ·
                    refine ⟨5653745156494100151963053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769163437662733434642035 5653745156494100151963053)
                    ·
                      refine ⟨2120154433685287556986145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5653745156494100151963053 2120154433685287556986145)
                      ·
                        rfl

theorem cell23_4128986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_4128986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4128986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4128986 prefixEnd_4128986 := by exact prefixLift 4128986
  have htrace : WordTrace (prefixWord ++ tailWord_4128986) baseStart_4128986 baseEnd_4128986 := by
    simpa [prefixWord, tailWord_4128986, baseEnd_4128986] using wordTrace_append hprefix tailTrace_4128986
  have hstable : (prefixWord ++ tailWord_4128986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128986).length < 2 ^ (prefixWord ++ tailWord_4128986).sum := by decide
  have hdescent : baseEnd_4128986 < baseStart_4128986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129054 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4129054 : Nat := 118140960795 + 4129054 * 2 ^ 59
def prefixEnd_4129054 : Nat := 4983230072969 + 3 ^ 40 * 4129054 * 2
def baseEnd_4129054 : Nat := 2120189350369793290935833

theorem tailTrace_4129054 : CollatzResearch.WordTrace tailWord_4129054 prefixEnd_4129054 2120189350369793290935833 := by
  unfold tailWord_4129054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824871447893752390695277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100399314388766679417041477 18824871447893752390695277)
  ·
    refine ⟨7059326792960157146510729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18824871447893752390695277 7059326792960157146510729)
    ·
      refine ⟨5294495094720117859883047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7059326792960157146510729 5294495094720117859883047)
      ·
        refine ⟨7941742642080176789824571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294495094720117859883047 7941742642080176789824571)
        ·
          refine ⟨11912613963120265184736857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941742642080176789824571 11912613963120265184736857)
          ·
            refine ⟨8934460472340198888552643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11912613963120265184736857 8934460472340198888552643)
            ·
              refine ⟨13401690708510298332828965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934460472340198888552643 13401690708510298332828965)
              ·
                refine ⟨2512817007845680937405431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13401690708510298332828965 2512817007845680937405431)
                ·
                  refine ⟨3769225511768521406108147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512817007845680937405431 3769225511768521406108147)
                  ·
                    refine ⟨5653838267652782109162221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769225511768521406108147 5653838267652782109162221)
                    ·
                      refine ⟨2120189350369793290935833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5653838267652782109162221 2120189350369793290935833)
                      ·
                        rfl

theorem cell23_4129054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4129054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129054 prefixEnd_4129054 := by exact prefixLift 4129054
  have htrace : WordTrace (prefixWord ++ tailWord_4129054) baseStart_4129054 baseEnd_4129054 := by
    simpa [prefixWord, tailWord_4129054, baseEnd_4129054] using wordTrace_append hprefix tailTrace_4129054
  have hstable : (prefixWord ++ tailWord_4129054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129054).length < 2 ^ (prefixWord ++ tailWord_4129054).sum := by decide
  have hdescent : baseEnd_4129054 < baseStart_4129054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129070 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4129070 : Nat := 118140960795 + 4129070 * 2 ^ 59
def prefixEnd_4129070 : Nat := 4983230072969 + 3 ^ 40 * 4129070 * 2
def baseEnd_4129070 : Nat := 706732522020088409445253

theorem tailTrace_4129070 : CollatzResearch.WordTrace tailWord_4129070 prefixEnd_4129070 706732522020088409445253 := by
  unfold tailWord_4129070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824944393886506732268083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100399703434061369238763109 18824944393886506732268083)
  ·
    refine ⟨28237416590829760098402125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18824944393886506732268083 28237416590829760098402125)
    ·
      refine ⟨10589031221561160036900797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28237416590829760098402125 10589031221561160036900797)
      ·
        refine ⟨3970886708085435013837799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10589031221561160036900797 3970886708085435013837799)
        ·
          refine ⟨5956330062128152520756699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970886708085435013837799 5956330062128152520756699)
          ·
            refine ⟨8934495093192228781135049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956330062128152520756699 8934495093192228781135049)
            ·
              refine ⟨6700871319894171585851287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8934495093192228781135049 6700871319894171585851287)
              ·
                refine ⟨10051306979841257378776931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700871319894171585851287 10051306979841257378776931)
                ·
                  refine ⟨15076960469761886068165397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051306979841257378776931 15076960469761886068165397)
                  ·
                    refine ⟨706732522020088409445253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15076960469761886068165397 706732522020088409445253)
                    ·
                      rfl

theorem cell23_4129070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4129070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129070 prefixEnd_4129070 := by exact prefixLift 4129070
  have htrace : WordTrace (prefixWord ++ tailWord_4129070) baseStart_4129070 baseEnd_4129070 := by
    simpa [prefixWord, tailWord_4129070, baseEnd_4129070] using wordTrace_append hprefix tailTrace_4129070
  have hstable : (prefixWord ++ tailWord_4129070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129070).length < 2 ^ (prefixWord ++ tailWord_4129070).sum := by decide
  have hdescent : baseEnd_4129070 < baseStart_4129070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129073 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4129073 : Nat := 118140960795 + 4129073 * 2 ^ 59
def prefixEnd_4129073 : Nat := 4983230072969 + 3 ^ 40 * 4129073 * 2
def baseEnd_4129073 : Nat := 2120199106502228716598245

theorem tailTrace_4129073 : CollatzResearch.WordTrace tailWord_4129073 prefixEnd_4129073 2120199106502228716598245 := by
  unfold tailWord_4129073
  simp only [CollatzResearch.WordTrace]
  refine ⟨150599664570081185370503873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100399776380054123580335915 150599664570081185370503873)
  ·
    refine ⟨112949748427560889027877905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150599664570081185370503873 112949748427560889027877905)
    ·
      refine ⟨84712311320670666770908429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112949748427560889027877905 84712311320670666770908429)
      ·
        refine ⟨31767116745251500039090661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84712311320670666770908429 31767116745251500039090661)
        ·
          refine ⟨5956334389734656257329499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31767116745251500039090661 5956334389734656257329499)
          ·
            refine ⟨8934501584601984385994249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956334389734656257329499 8934501584601984385994249)
            ·
              refine ⟨6700876188451488289495687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8934501584601984385994249 6700876188451488289495687)
              ·
                refine ⟨10051314282677232434243531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700876188451488289495687 10051314282677232434243531)
                ·
                  refine ⟨15076971424015848651365297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051314282677232434243531 15076971424015848651365297)
                  ·
                    refine ⟨11307728568011886488523973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076971424015848651365297 11307728568011886488523973)
                    ·
                      refine ⟨2120199106502228716598245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11307728568011886488523973 2120199106502228716598245)
                      ·
                        rfl

theorem cell23_4129073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4129073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129073 prefixEnd_4129073 := by exact prefixLift 4129073
  have htrace : WordTrace (prefixWord ++ tailWord_4129073) baseStart_4129073 baseEnd_4129073 := by
    simpa [prefixWord, tailWord_4129073, baseEnd_4129073] using wordTrace_append hprefix tailTrace_4129073
  have hstable : (prefixWord ++ tailWord_4129073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129073).length < 2 ^ (prefixWord ++ tailWord_4129073).sum := by decide
  have hdescent : baseEnd_4129073 < baseStart_4129073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129099 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_4129099 : Nat := 118140960795 + 4129099 * 2 ^ 59
def prefixEnd_4129099 : Nat := 4983230072969 + 3 ^ 40 * 4129099 * 2
def baseEnd_4129099 : Nat := 2120212456999245614873125

theorem tailTrace_4129099 : CollatzResearch.WordTrace tailWord_4129099 prefixEnd_4129099 2120212456999245614873125 := by
  unfold tailWord_4129099
  simp only [CollatzResearch.WordTrace]
  refine ⟨150600612867986991810950351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100400408578657994540633567 150600612867986991810950351)
  ·
    refine ⟨225900919301980487716425527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150600612867986991810950351 225900919301980487716425527)
    ·
      refine ⟨338851378952970731574638291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225900919301980487716425527 338851378952970731574638291)
      ·
        refine ⟨508277068429456097361957437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338851378952970731574638291 508277068429456097361957437)
        ·
          refine ⟨190603900661046036510734039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508277068429456097361957437 190603900661046036510734039)
          ·
            refine ⟨285905850991569054766101059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190603900661046036510734039 285905850991569054766101059)
            ·
              refine ⟨428858776487353582149151589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285905850991569054766101059 428858776487353582149151589)
              ·
                refine ⟨80411020591378796652965923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428858776487353582149151589 80411020591378796652965923)
                ·
                  refine ⟨120616530887068194979448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80411020591378796652965923 120616530887068194979448885)
                  ·
                    refine ⟨11307799770662643279323333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120616530887068194979448885 11307799770662643279323333)
                    ·
                      refine ⟨2120212456999245614873125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11307799770662643279323333 2120212456999245614873125)
                      ·
                        rfl

theorem cell23_4129099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_4129099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129099 prefixEnd_4129099 := by exact prefixLift 4129099
  have htrace : WordTrace (prefixWord ++ tailWord_4129099) baseStart_4129099 baseEnd_4129099 := by
    simpa [prefixWord, tailWord_4129099, baseEnd_4129099] using wordTrace_append hprefix tailTrace_4129099
  have hstable : (prefixWord ++ tailWord_4129099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129099).length < 2 ^ (prefixWord ++ tailWord_4129099).sum := by decide
  have hdescent : baseEnd_4129099 < baseStart_4129099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129127 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_4129127 : Nat := 118140960795 + 4129127 * 2 ^ 59
def prefixEnd_4129127 : Nat := 4983230072969 + 3 ^ 40 * 4129127 * 2
def baseEnd_4129127 : Nat := 2120226834457571505322997

theorem tailTrace_4129127 : CollatzResearch.WordTrace tailWord_4129127 prefixEnd_4129127 2120226834457571505322997 := by
  unfold tailWord_4129127
  simp only [CollatzResearch.WordTrace]
  refine ⟨150601634111885552592969635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100401089407923701728646423 150601634111885552592969635)
  ·
    refine ⟨225902451167828328889454453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150601634111885552592969635 225902451167828328889454453)
    ·
      refine ⟨21178354796983905833386355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225902451167828328889454453 21178354796983905833386355)
      ·
        refine ⟨31767532195475858750079533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178354796983905833386355 31767532195475858750079533)
        ·
          refine ⟨11912824573303447031279825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31767532195475858750079533 11912824573303447031279825)
          ·
            refine ⟨8934618429977585273459869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11912824573303447031279825 8934618429977585273459869)
            ·
              refine ⟨3350481911241594477547451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8934618429977585273459869 3350481911241594477547451)
              ·
                refine ⟨5025722866862391716321177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350481911241594477547451 5025722866862391716321177)
                ·
                  refine ⟨3769292150146793787240883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025722866862391716321177 3769292150146793787240883)
                  ·
                    refine ⟨5653938225220190680861325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769292150146793787240883 5653938225220190680861325)
                    ·
                      refine ⟨2120226834457571505322997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5653938225220190680861325 2120226834457571505322997)
                      ·
                        rfl

theorem cell23_4129127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_4129127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129127 prefixEnd_4129127 := by exact prefixLift 4129127
  have htrace : WordTrace (prefixWord ++ tailWord_4129127) baseStart_4129127 baseEnd_4129127 := by
    simpa [prefixWord, tailWord_4129127, baseEnd_4129127] using wordTrace_append hprefix tailTrace_4129127
  have hstable : (prefixWord ++ tailWord_4129127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129127).length < 2 ^ (prefixWord ++ tailWord_4129127).sum := by decide
  have hdescent : baseEnd_4129127 < baseStart_4129127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129153 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4129153 : Nat := 118140960795 + 4129153 * 2 ^ 59
def prefixEnd_4129153 : Nat := 4983230072969 + 3 ^ 40 * 4129153 * 2
def baseEnd_4129153 : Nat := 2120240184954588403597877

theorem tailTrace_4129153 : CollatzResearch.WordTrace tailWord_4129153 prefixEnd_4129153 2120240184954588403597877 := by
  unfold tailWord_4129153
  simp only [CollatzResearch.WordTrace]
  refine ⟨150602582409791359033416113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100401721606527572688944075 150602582409791359033416113)
  ·
    refine ⟨112951936807343519275062085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150602582409791359033416113 112951936807343519275062085)
    ·
      refine ⟨21178488151376909864074141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112951936807343519275062085 21178488151376909864074141)
      ·
        refine ⟨7941933056766341199027803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21178488151376909864074141 7941933056766341199027803)
        ·
          refine ⟨11912899585149511798541705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941933056766341199027803 11912899585149511798541705)
          ·
            refine ⟨8934674688862133848906279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11912899585149511798541705 8934674688862133848906279)
            ·
              refine ⟨13402012033293200773359419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934674688862133848906279 13402012033293200773359419)
              ·
                refine ⟨20103018049939801160039129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402012033293200773359419 20103018049939801160039129)
                ·
                  refine ⟨15077263537454850870029347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20103018049939801160039129 15077263537454850870029347)
                  ·
                    refine ⟨22615895306182276305044021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15077263537454850870029347 22615895306182276305044021)
                    ·
                      refine ⟨2120240184954588403597877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22615895306182276305044021 2120240184954588403597877)
                      ·
                        rfl

theorem cell23_4129153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4129153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129153 prefixEnd_4129153 := by exact prefixLift 4129153
  have htrace : WordTrace (prefixWord ++ tailWord_4129153) baseStart_4129153 baseEnd_4129153 := by
    simpa [prefixWord, tailWord_4129153, baseEnd_4129153] using wordTrace_append hprefix tailTrace_4129153
  have hstable : (prefixWord ++ tailWord_4129153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129153).length < 2 ^ (prefixWord ++ tailWord_4129153).sum := by decide
  have hdescent : baseEnd_4129153 < baseStart_4129153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129184 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2]
def baseStart_4129184 : Nat := 118140960795 + 4129184 * 2 ^ 59
def prefixEnd_4129184 : Nat := 4983230072969 + 3 ^ 40 * 4129184 * 2
def baseEnd_4129184 : Nat := 2120256102854877782310235

theorem tailTrace_4129184 : CollatzResearch.WordTrace tailWord_4129184 prefixEnd_4129184 2120256102854877782310235 := by
  unfold tailWord_4129184
  simp only [CollatzResearch.WordTrace]
  refine ⟨75301856536339525663897303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100402475381786034218529737 75301856536339525663897303)
  ·
    refine ⟨112952784804509288495845955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75301856536339525663897303 112952784804509288495845955)
    ·
      refine ⟨169429177206763932743768933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112952784804509288495845955 169429177206763932743768933)
      ·
        refine ⟨31767970726268237389456675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169429177206763932743768933 31767970726268237389456675)
        ·
          refine ⟨47651956089402356084185013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31767970726268237389456675 47651956089402356084185013)
          ·
            refine ⟨4467370883381470882892345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47651956089402356084185013 4467370883381470882892345)
            ·
              refine ⟨3350528162536103162169259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467370883381470882892345 3350528162536103162169259)
              ·
                refine ⟨5025792243804154743253889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350528162536103162169259 5025792243804154743253889)
                ·
                  refine ⟨3769344182853116057440417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025792243804154743253889 3769344182853116057440417)
                  ·
                    refine ⟨2827008137139837043080313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3769344182853116057440417 2827008137139837043080313)
                    ·
                      refine ⟨2120256102854877782310235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827008137139837043080313 2120256102854877782310235)
                      ·
                        rfl

theorem cell23_4129184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_4129184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129184 prefixEnd_4129184 := by exact prefixLift 4129184
  have htrace : WordTrace (prefixWord ++ tailWord_4129184) baseStart_4129184 baseEnd_4129184 := by
    simpa [prefixWord, tailWord_4129184, baseEnd_4129184] using wordTrace_append hprefix tailTrace_4129184
  have hstable : (prefixWord ++ tailWord_4129184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129184).length < 2 ^ (prefixWord ++ tailWord_4129184).sum := by decide
  have hdescent : baseEnd_4129184 < baseStart_4129184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129223 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_4129223 : Nat := 118140960795 + 4129223 * 2 ^ 59
def prefixEnd_4129223 : Nat := 4983230072969 + 3 ^ 40 * 4129223 * 2
def baseEnd_4129223 : Nat := 2120276128600403129722555

theorem tailTrace_4129223 : CollatzResearch.WordTrace tailWord_4129223 prefixEnd_4129223 2120276128600403129722555 := by
  unfold tailWord_4129223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150605135519537760988464323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100403423679691840658976215 150605135519537760988464323)
  ·
    refine ⟨225907703279306641482696485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150605135519537760988464323 225907703279306641482696485)
    ·
      refine ⟨42357694364869995278005591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225907703279306641482696485 42357694364869995278005591)
      ·
        refine ⟨63536541547304992917008387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42357694364869995278005591 63536541547304992917008387)
        ·
          refine ⟨95304812320957489375512581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63536541547304992917008387 95304812320957489375512581)
          ·
            refine ⟨17869652310179529257908609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95304812320957489375512581 17869652310179529257908609)
            ·
              refine ⟨13402239232634646943431457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17869652310179529257908609 13402239232634646943431457)
              ·
                refine ⟨10051679424475985207573593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402239232634646943431457 10051679424475985207573593)
                ·
                  refine ⟨7538759568356988905680195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10051679424475985207573593 7538759568356988905680195)
                  ·
                    refine ⟨11308139352535483358520293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538759568356988905680195 11308139352535483358520293)
                    ·
                      refine ⟨2120276128600403129722555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11308139352535483358520293 2120276128600403129722555)
                      ·
                        rfl

theorem cell23_4129223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_4129223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129223 prefixEnd_4129223 := by exact prefixLift 4129223
  have htrace : WordTrace (prefixWord ++ tailWord_4129223) baseStart_4129223 baseEnd_4129223 := by
    simpa [prefixWord, tailWord_4129223, baseEnd_4129223] using wordTrace_append hprefix tailTrace_4129223
  have hstable : (prefixWord ++ tailWord_4129223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129223).length < 2 ^ (prefixWord ++ tailWord_4129223).sum := by decide
  have hdescent : baseEnd_4129223 < baseStart_4129223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129226 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4129226 : Nat := 118140960795 + 4129226 * 2 ^ 59
def prefixEnd_4129226 : Nat := 4983230072969 + 3 ^ 40 * 4129226 * 2
def baseEnd_4129226 : Nat := 2120277669042366617985041

theorem tailTrace_4129226 : CollatzResearch.WordTrace tailWord_4129226 prefixEnd_4129226 2120277669042366617985041 := by
  unfold tailWord_4129226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37651311234631723125205883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100403496625684595000549021 37651311234631723125205883)
  ·
    refine ⟨56476966851947584687808825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37651311234631723125205883 56476966851947584687808825)
    ·
      refine ⟨42357725138960688515856619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56476966851947584687808825 42357725138960688515856619)
      ·
        refine ⟨63536587708441032773784929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42357725138960688515856619 63536587708441032773784929)
        ·
          refine ⟨47652440781330774580338697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63536587708441032773784929 47652440781330774580338697)
          ·
            refine ⟨35739330585998080935254023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47652440781330774580338697 35739330585998080935254023)
            ·
              refine ⟨53608995878997121402881035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35739330585998080935254023 53608995878997121402881035)
              ·
                refine ⟨80413493818495682104321553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53608995878997121402881035 80413493818495682104321553)
                ·
                  refine ⟨60310120363871761578241165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80413493818495682104321553 60310120363871761578241165)
                  ·
                    refine ⟨22616295136451910591840437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60310120363871761578241165 22616295136451910591840437)
                    ·
                      refine ⟨2120277669042366617985041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22616295136451910591840437 2120277669042366617985041)
                      ·
                        rfl

theorem cell23_4129226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4129226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129226 prefixEnd_4129226 := by exact prefixLift 4129226
  have htrace : WordTrace (prefixWord ++ tailWord_4129226) baseStart_4129226 baseEnd_4129226 := by
    simpa [prefixWord, tailWord_4129226, baseEnd_4129226] using wordTrace_append hprefix tailTrace_4129226
  have hstable : (prefixWord ++ tailWord_4129226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129226).length < 2 ^ (prefixWord ++ tailWord_4129226).sum := by decide
  have hdescent : baseEnd_4129226 < baseStart_4129226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129330 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4129330 : Nat := 118140960795 + 4129330 * 2 ^ 59
def prefixEnd_4129330 : Nat := 4983230072969 + 3 ^ 40 * 4129330 * 2
def baseEnd_4129330 : Nat := 2120331071030434211084563

theorem tailTrace_4129330 : CollatzResearch.WordTrace tailWord_4129330 prefixEnd_4129330 2120331071030434211084563 := by
  unfold tailWord_4129330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37652259532537529565652361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100406025420100078841739629 37652259532537529565652361)
  ·
    refine ⟨28239194649403147174239271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37652259532537529565652361 28239194649403147174239271)
    ·
      refine ⟨42358791974104720761358907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239194649403147174239271 42358791974104720761358907)
      ·
        refine ⟨63538187961157081142038361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42358791974104720761358907 63538187961157081142038361)
        ·
          refine ⟨47653640970867810856528771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63538187961157081142038361 47653640970867810856528771)
          ·
            refine ⟨71480461456301716284793157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47653640970867810856528771 71480461456301716284793157)
            ·
              refine ⟨13402586523056571803398717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71480461456301716284793157 13402586523056571803398717)
              ·
                refine ⟨5025969946146214426274519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13402586523056571803398717 5025969946146214426274519)
                ·
                  refine ⟨7538954919219321639411779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025969946146214426274519 7538954919219321639411779)
                  ·
                    refine ⟨11308432378828982459117669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538954919219321639411779 11308432378828982459117669)
                    ·
                      refine ⟨2120331071030434211084563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11308432378828982459117669 2120331071030434211084563)
                      ·
                        rfl

theorem cell23_4129330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4129330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129330 prefixEnd_4129330 := by exact prefixLift 4129330
  have htrace : WordTrace (prefixWord ++ tailWord_4129330) baseStart_4129330 baseEnd_4129330 := by
    simpa [prefixWord, tailWord_4129330, baseEnd_4129330] using wordTrace_append hprefix tailTrace_4129330
  have hstable : (prefixWord ++ tailWord_4129330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129330).length < 2 ^ (prefixWord ++ tailWord_4129330).sum := by decide
  have hdescent : baseEnd_4129330 < baseStart_4129330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129334 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4129334 : Nat := 118140960795 + 4129334 * 2 ^ 59
def prefixEnd_4129334 : Nat := 4983230072969 + 3 ^ 40 * 4129334 * 2
def baseEnd_4129334 : Nat := 2120333124953052195434545

theorem tailTrace_4129334 : CollatzResearch.WordTrace tailWord_4129334 prefixEnd_4129334 2120333124953052195434545 := by
  unfold tailWord_4129334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413074001383476684109691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100406122681423751297170037 9413074001383476684109691)
  ·
    refine ⟨14119611002075215026164537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413074001383476684109691 14119611002075215026164537)
    ·
      refine ⟨10589708251556411269623403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14119611002075215026164537 10589708251556411269623403)
      ·
        refine ⟨15884562377334616904435105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589708251556411269623403 15884562377334616904435105)
        ·
          refine ⟨11913421783000962678326329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15884562377334616904435105 11913421783000962678326329)
          ·
            refine ⟨8935066337250722008744747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11913421783000962678326329 8935066337250722008744747)
            ·
              refine ⟨13402599505876083013117121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935066337250722008744747 13402599505876083013117121)
              ·
                refine ⟨10051949629407062259837841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402599505876083013117121 10051949629407062259837841)
                ·
                  refine ⟨7538962222055296694878381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10051949629407062259837841 7538962222055296694878381)
                  ·
                    refine ⟨2827110833270736260579393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7538962222055296694878381 2827110833270736260579393)
                    ·
                      refine ⟨2120333124953052195434545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827110833270736260579393 2120333124953052195434545)
                      ·
                        rfl

theorem cell23_4129334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4129334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129334 prefixEnd_4129334 := by exact prefixLift 4129334
  have htrace : WordTrace (prefixWord ++ tailWord_4129334) baseStart_4129334 baseEnd_4129334 := by
    simpa [prefixWord, tailWord_4129334, baseEnd_4129334] using wordTrace_append hprefix tailTrace_4129334
  have hstable : (prefixWord ++ tailWord_4129334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129334).length < 2 ^ (prefixWord ++ tailWord_4129334).sum := by decide
  have hdescent : baseEnd_4129334 < baseStart_4129334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129340 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_4129340 : Nat := 118140960795 + 4129340 * 2 ^ 59
def prefixEnd_4129340 : Nat := 4983230072969 + 3 ^ 40 * 4129340 * 2
def baseEnd_4129340 : Nat := 706778735278993057319839

theorem tailTrace_4129340 : CollatzResearch.WordTrace tailWord_4129340 prefixEnd_4129340 706778735278993057319839 := by
  unfold tailWord_4129340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75304701430056944985236737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100406268573409259980315649 75304701430056944985236737)
  ·
    refine ⟨56478526072542708738927553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75304701430056944985236737 56478526072542708738927553)
    ·
      refine ⟨42358894554407031554195665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56478526072542708738927553 42358894554407031554195665)
      ·
        refine ⟨31769170915805273665646749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42358894554407031554195665 31769170915805273665646749)
        ·
          refine ⟨11913439093426977624617531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31769170915805273665646749 11913439093426977624617531)
          ·
            refine ⟨17870158640140466436926297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11913439093426977624617531 17870158640140466436926297)
            ·
              refine ⟨13402618980105349827694723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17870158640140466436926297 13402618980105349827694723)
              ·
                refine ⟨20103928470158024741542085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402618980105349827694723 20103928470158024741542085)
                ·
                  refine ⟨3769486588154629639039141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20103928470158024741542085 3769486588154629639039141)
                  ·
                    refine ⟨706778735278993057319839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3769486588154629639039141 706778735278993057319839)
                    ·
                      rfl

theorem cell23_4129340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_4129340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129340 prefixEnd_4129340 := by exact prefixLift 4129340
  have htrace : WordTrace (prefixWord ++ tailWord_4129340) baseStart_4129340 baseEnd_4129340 := by
    simpa [prefixWord, tailWord_4129340, baseEnd_4129340] using wordTrace_append hprefix tailTrace_4129340
  have hstable : (prefixWord ++ tailWord_4129340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129340).length < 2 ^ (prefixWord ++ tailWord_4129340).sum := by decide
  have hdescent : baseEnd_4129340 < baseStart_4129340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129341 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4129341 : Nat := 118140960795 + 4129341 * 2 ^ 59
def prefixEnd_4129341 : Nat := 4983230072969 + 3 ^ 40 * 4129341 * 2
def baseEnd_4129341 : Nat := 2120336719317633668047013

theorem tailTrace_4129341 : CollatzResearch.WordTrace tailWord_4129341 prefixEnd_4129341 2120336719317633668047013 := by
  unfold tailWord_4129341
  simp only [CollatzResearch.WordTrace]
  refine ⟨150609439333110267141259877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100406292888740178094173251 150609439333110267141259877)
  ·
    refine ⟨28239269874958175088986227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150609439333110267141259877 28239269874958175088986227)
    ·
      refine ⟨42358904812437262633479341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239269874958175088986227 42358904812437262633479341)
      ·
        refine ⟨15884589304663973487554753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42358904812437262633479341 15884589304663973487554753)
        ·
          refine ⟨11913441978497980115666065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15884589304663973487554753 11913441978497980115666065)
          ·
            refine ⟨8935081483873485086749549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11913441978497980115666065 8935081483873485086749549)
            ·
              refine ⟨3350655556452556907531081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935081483873485086749549 3350655556452556907531081)
              ·
                refine ⟨2512991667339417680648311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350655556452556907531081 2512991667339417680648311)
                ·
                  refine ⟨3769487501009126520972467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512991667339417680648311 3769487501009126520972467)
                  ·
                    refine ⟨5654231251513689781458701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769487501009126520972467 5654231251513689781458701)
                    ·
                      refine ⟨2120336719317633668047013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654231251513689781458701 2120336719317633668047013)
                      ·
                        rfl

theorem cell23_4129341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4129341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129341 prefixEnd_4129341 := by exact prefixLift 4129341
  have htrace : WordTrace (prefixWord ++ tailWord_4129341) baseStart_4129341 baseEnd_4129341 := by
    simpa [prefixWord, tailWord_4129341, baseEnd_4129341] using wordTrace_append hprefix tailTrace_4129341
  have hstable : (prefixWord ++ tailWord_4129341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129341).length < 2 ^ (prefixWord ++ tailWord_4129341).sum := by decide
  have hdescent : baseEnd_4129341 < baseStart_4129341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129348 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 6]
def baseStart_4129348 : Nat := 118140960795 + 4129348 * 2 ^ 59
def prefixEnd_4129348 : Nat := 4983230072969 + 3 ^ 40 * 4129348 * 2
def baseEnd_4129348 : Nat := 235593368186912793406609

theorem tailTrace_4129348 : CollatzResearch.WordTrace tailWord_4129348 prefixEnd_4129348 235593368186912793406609 := by
  unfold tailWord_4129348
  simp only [CollatzResearch.WordTrace]
  refine ⟨75304847322042453668382349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100406463096056604891176465 75304847322042453668382349)
  ·
    refine ⟨28239317745765920125643381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75304847322042453668382349 28239317745765920125643381)
    ·
      refine ⟨2647436038665555011779067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28239317745765920125643381 2647436038665555011779067)
      ·
        refine ⟨3971154057998332517668601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647436038665555011779067 3971154057998332517668601)
        ·
          refine ⟨2978365543498749388251451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3971154057998332517668601 2978365543498749388251451)
          ·
            refine ⟨4467548315248124082377177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978365543498749388251451 4467548315248124082377177)
            ·
              refine ⟨3350661236436093061782883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467548315248124082377177 3350661236436093061782883)
              ·
                refine ⟨5025991854654139592674325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350661236436093061782883 5025991854654139592674325)
                ·
                  refine ⟨235593368186912793406609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5025991854654139592674325 235593368186912793406609)
                  ·
                    rfl

theorem cell23_4129348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_4129348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129348 prefixEnd_4129348 := by exact prefixLift 4129348
  have htrace : WordTrace (prefixWord ++ tailWord_4129348) baseStart_4129348 baseEnd_4129348 := by
    simpa [prefixWord, tailWord_4129348, baseEnd_4129348] using wordTrace_append hprefix tailTrace_4129348
  have hstable : (prefixWord ++ tailWord_4129348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129348).length < 2 ^ (prefixWord ++ tailWord_4129348).sum := by decide
  have hdescent : baseEnd_4129348 < baseStart_4129348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129380 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_4129380 : Nat := 118140960795 + 4129380 * 2 ^ 59
def prefixEnd_4129380 : Nat := 4983230072969 + 3 ^ 40 * 4129380 * 2
def baseEnd_4129380 : Nat := 2120356745063159015459333

theorem tailTrace_4129380 : CollatzResearch.WordTrace tailWord_4129380 prefixEnd_4129380 2120356745063159015459333 := by
  unfold tailWord_4129380
  simp only [CollatzResearch.WordTrace]
  refine ⟨75305430889984488400964797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100407241186645984534619729 75305430889984488400964797)
  ·
    refine ⟨28239536583744183150361799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75305430889984488400964797 28239536583744183150361799)
    ·
      refine ⟨42359304875616274725542699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239536583744183150361799 42359304875616274725542699)
      ·
        refine ⟨63538957313424412088314049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42359304875616274725542699 63538957313424412088314049)
        ·
          refine ⟨47654217985068309066235537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63538957313424412088314049 47654217985068309066235537)
          ·
            refine ⟨35740663488801231799676653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47654217985068309066235537 35740663488801231799676653)
            ·
              refine ⟨13402748808300461924878745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35740663488801231799676653 13402748808300461924878745)
              ·
                refine ⟨10052061606225346443659059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402748808300461924878745 10052061606225346443659059)
                ·
                  refine ⟨15078092409338019665488589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052061606225346443659059 15078092409338019665488589)
                  ·
                    refine ⟨5654284653501757374558221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15078092409338019665488589 5654284653501757374558221)
                    ·
                      refine ⟨2120356745063159015459333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654284653501757374558221 2120356745063159015459333)
                      ·
                        rfl

theorem cell23_4129380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_4129380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129380 prefixEnd_4129380 := by exact prefixLift 4129380
  have htrace : WordTrace (prefixWord ++ tailWord_4129380) baseStart_4129380 baseEnd_4129380 := by
    simpa [prefixWord, tailWord_4129380, baseEnd_4129380] using wordTrace_append hprefix tailTrace_4129380
  have hstable : (prefixWord ++ tailWord_4129380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129380).length < 2 ^ (prefixWord ++ tailWord_4129380).sum := by decide
  have hdescent : baseEnd_4129380 < baseStart_4129380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129384 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4129384 : Nat := 118140960795 + 4129384 * 2 ^ 59
def prefixEnd_4129384 : Nat := 4983230072969 + 3 ^ 40 * 4129384 * 2
def baseEnd_4129384 : Nat := 2120358798985776999809315

theorem tailTrace_4129384 : CollatzResearch.WordTrace tailWord_4129384 prefixEnd_4129384 2120358798985776999809315 := by
  unfold tailWord_4129384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75305503835977242742537603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100407338447969656990050137 75305503835977242742537603)
  ·
    refine ⟨112958255753965864113806405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75305503835977242742537603 112958255753965864113806405)
    ·
      refine ⟨21179672953868599521338701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112958255753965864113806405 21179672953868599521338701)
      ·
        refine ⟨7942377357700724820502013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21179672953868599521338701 7942377357700724820502013)
        ·
          refine ⟨2978391509137771807688255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7942377357700724820502013 2978391509137771807688255)
          ·
            refine ⟨4467587263706657711532383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978391509137771807688255 4467587263706657711532383)
            ·
              refine ⟨6701380895559986567298575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467587263706657711532383 6701380895559986567298575)
              ·
                refine ⟨10052071343339979850947863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701380895559986567298575 10052071343339979850947863)
                ·
                  refine ⟨15078107015009969776421795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052071343339979850947863 15078107015009969776421795)
                  ·
                    refine ⟨22617160522514954664632693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15078107015009969776421795 22617160522514954664632693)
                    ·
                      refine ⟨2120358798985776999809315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22617160522514954664632693 2120358798985776999809315)
                      ·
                        rfl

theorem cell23_4129384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4129384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129384 prefixEnd_4129384 := by exact prefixLift 4129384
  have htrace : WordTrace (prefixWord ++ tailWord_4129384) baseStart_4129384 baseEnd_4129384 := by
    simpa [prefixWord, tailWord_4129384, baseEnd_4129384] using wordTrace_append hprefix tailTrace_4129384
  have hstable : (prefixWord ++ tailWord_4129384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129384).length < 2 ^ (prefixWord ++ tailWord_4129384).sum := by decide
  have hdescent : baseEnd_4129384 < baseStart_4129384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129398 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4129398 : Nat := 118140960795 + 4129398 * 2 ^ 59
def prefixEnd_4129398 : Nat := 4983230072969 + 3 ^ 40 * 4129398 * 2
def baseEnd_4129398 : Nat := 2120365987714939945034251

theorem tailTrace_4129398 : CollatzResearch.WordTrace tailWord_4129398 prefixEnd_4129398 2120365987714939945034251 := by
  unfold tailWord_4129398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413219893368985367255303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100407678862602510584056565 9413219893368985367255303)
  ·
    refine ⟨14119829840053478050882955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413219893368985367255303 14119829840053478050882955)
    ·
      refine ⟨21179744760080217076324433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14119829840053478050882955 21179744760080217076324433)
      ·
        refine ⟨15884808570060162807243325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21179744760080217076324433 15884808570060162807243325)
        ·
          refine ⟨5956803213772561052716247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15884808570060162807243325 5956803213772561052716247)
          ·
            refine ⟨8935204820658841579074371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956803213772561052716247 8935204820658841579074371)
            ·
              refine ⟨13402807230988262368611557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935204820658841579074371 13402807230988262368611557)
              ·
                refine ⟨2513026355810299194114667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13402807230988262368611557 2513026355810299194114667)
                ·
                  refine ⟨3769539533715448791172001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513026355810299194114667 3769539533715448791172001)
                  ·
                    refine ⟨2827154650286586593379001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3769539533715448791172001 2827154650286586593379001)
                    ·
                      refine ⟨2120365987714939945034251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827154650286586593379001 2120365987714939945034251)
                      ·
                        rfl

theorem cell23_4129398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4129398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129398 prefixEnd_4129398 := by exact prefixLift 4129398
  have htrace : WordTrace (prefixWord ++ tailWord_4129398) baseStart_4129398 baseEnd_4129398 := by
    simpa [prefixWord, tailWord_4129398, baseEnd_4129398] using wordTrace_append hprefix tailTrace_4129398
  have hstable : (prefixWord ++ tailWord_4129398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129398).length < 2 ^ (prefixWord ++ tailWord_4129398).sum := by decide
  have hdescent : baseEnd_4129398 < baseStart_4129398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129413 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_4129413 : Nat := 118140960795 + 4129413 * 2 ^ 59
def prefixEnd_4129413 : Nat := 4983230072969 + 3 ^ 40 * 4129413 * 2
def baseEnd_4129413 : Nat := 706791229974919128782227

theorem tailTrace_4129413 : CollatzResearch.WordTrace tailWord_4129413 prefixEnd_4129413 706791229974919128782227 := by
  unfold tailWord_4129413
  simp only [CollatzResearch.WordTrace]
  refine ⟨150612065388849423437880893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100408043592566282291920595 150612065388849423437880893)
  ·
    refine ⟨56479524520818533789205335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150612065388849423437880893 56479524520818533789205335)
    ·
      refine ⟨84719286781227800683808003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56479524520818533789205335 84719286781227800683808003)
      ·
        refine ⟨127078930171841701025712005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84719286781227800683808003 127078930171841701025712005)
        ·
          refine ⟨23827299407220318942321001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127078930171841701025712005 23827299407220318942321001)
          ·
            refine ⟨17870474555415239206740751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23827299407220318942321001 17870474555415239206740751)
            ·
              refine ⟨26805711833122858810111127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17870474555415239206740751 26805711833122858810111127)
              ·
                refine ⟨40208567749684288215166691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26805711833122858810111127 40208567749684288215166691)
                ·
                  refine ⟨60312851624526432322750037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40208567749684288215166691 60312851624526432322750037)
                  ·
                    refine ⟨706791229974919128782227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60312851624526432322750037 706791229974919128782227)
                    ·
                      rfl

theorem cell23_4129413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_4129413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129413 prefixEnd_4129413 := by exact prefixLift 4129413
  have htrace : WordTrace (prefixWord ++ tailWord_4129413) baseStart_4129413 baseEnd_4129413 := by
    simpa [prefixWord, tailWord_4129413, baseEnd_4129413] using wordTrace_append hprefix tailTrace_4129413
  have hstable : (prefixWord ++ tailWord_4129413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129413).length < 2 ^ (prefixWord ++ tailWord_4129413).sum := by decide
  have hdescent : baseEnd_4129413 < baseStart_4129413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129433 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_4129433 : Nat := 118140960795 + 4129433 * 2 ^ 59
def prefixEnd_4129433 : Nat := 4983230072969 + 3 ^ 40 * 4129433 * 2
def baseEnd_4129433 : Nat := 2120383959537847308096589

theorem tailTrace_4129433 : CollatzResearch.WordTrace tailWord_4129433 prefixEnd_4129433 2120383959537847308096589 := by
  unfold tailWord_4129433
  simp only [CollatzResearch.WordTrace]
  refine ⟨150612794848776966853608953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100408529899184644569072635 150612794848776966853608953)
  ·
    refine ⟨112959596136582725140206715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150612794848776966853608953 112959596136582725140206715)
    ·
      refine ⟨169439394204874087710310073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112959596136582725140206715 169439394204874087710310073)
      ·
        refine ⟨127079545653655565782732555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169439394204874087710310073 127079545653655565782732555)
        ·
          refine ⟨190619318480483348674098833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127079545653655565782732555 190619318480483348674098833)
          ·
            refine ⟨142964488860362511505574125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190619318480483348674098833 142964488860362511505574125)
            ·
              refine ⟨53611683322635941814590297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142964488860362511505574125 53611683322635941814590297)
              ·
                refine ⟨40208762491976956360942723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53611683322635941814590297 40208762491976956360942723)
                ·
                  refine ⟨60313143737965434541414085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40208762491976956360942723 60313143737965434541414085)
                  ·
                    refine ⟨11308714450868518976515141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60313143737965434541414085 11308714450868518976515141)
                    ·
                      refine ⟨2120383959537847308096589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11308714450868518976515141 2120383959537847308096589)
                      ·
                        rfl

theorem cell23_4129433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_4129433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129433 prefixEnd_4129433 := by exact prefixLift 4129433
  have htrace : WordTrace (prefixWord ++ tailWord_4129433) baseStart_4129433 baseEnd_4129433 := by
    simpa [prefixWord, tailWord_4129433, baseEnd_4129433] using wordTrace_append hprefix tailTrace_4129433
  have hstable : (prefixWord ++ tailWord_4129433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129433).length < 2 ^ (prefixWord ++ tailWord_4129433).sum := by decide
  have hdescent : baseEnd_4129433 < baseStart_4129433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129437 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4129437 : Nat := 118140960795 + 4129437 * 2 ^ 59
def prefixEnd_4129437 : Nat := 4983230072969 + 3 ^ 40 * 4129437 * 2
def baseEnd_4129437 : Nat := 2120386013460465292446571

theorem tailTrace_4129437 : CollatzResearch.WordTrace tailWord_4129437 prefixEnd_4129437 2120386013460465292446571 := by
  unfold tailWord_4129437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150612940740762475536754565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100408627160508317024503043 150612940740762475536754565)
  ·
    refine ⟨28239926388892964163141481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150612940740762475536754565 28239926388892964163141481)
    ·
      refine ⟨21179944791669723122356111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28239926388892964163141481 21179944791669723122356111)
      ·
        refine ⟨31769917187504584683534167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21179944791669723122356111 31769917187504584683534167)
        ·
          refine ⟨47654875781256877025301251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31769917187504584683534167 47654875781256877025301251)
          ·
            refine ⟨71482313671885315537951877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47654875781256877025301251 71482313671885315537951877)
            ·
              refine ⟨13402933813478496663365977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71482313671885315537951877 13402933813478496663365977)
              ·
                refine ⟨10052200360108872497524483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402933813478496663365977 10052200360108872497524483)
                ·
                  refine ⟨15078300540163308746286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052200360108872497524483 15078300540163308746286725)
                  ·
                    refine ⟨2827181351280620389928761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15078300540163308746286725 2827181351280620389928761)
                    ·
                      refine ⟨2120386013460465292446571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827181351280620389928761 2120386013460465292446571)
                      ·
                        rfl

theorem cell23_4129437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4129437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129437 prefixEnd_4129437 := by exact prefixLift 4129437
  have htrace : WordTrace (prefixWord ++ tailWord_4129437) baseStart_4129437 baseEnd_4129437 := by
    simpa [prefixWord, tailWord_4129437, baseEnd_4129437] using wordTrace_append hprefix tailTrace_4129437
  have hstable : (prefixWord ++ tailWord_4129437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129437).length < 2 ^ (prefixWord ++ tailWord_4129437).sum := by decide
  have hdescent : baseEnd_4129437 < baseStart_4129437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129471 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 2, 2, 2]
def baseStart_4129471 : Nat := 118140960795 + 4129471 * 2 ^ 59
def prefixEnd_4129471 : Nat := 4983230072969 + 3 ^ 40 * 4129471 * 2
def baseEnd_4129471 : Nat := 2120403471802718159421415

theorem tailTrace_4129471 : CollatzResearch.WordTrace tailWord_4129471 prefixEnd_4129471 2120403471802718159421415 := by
  unfold tailWord_4129471
  simp only [CollatzResearch.WordTrace]
  refine ⟨150614180822639299343492267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100409453881759532895661511 150614180822639299343492267)
  ·
    refine ⟨225921271233958949015238401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150614180822639299343492267 225921271233958949015238401)
    ·
      refine ⟨169440953425469211761428801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225921271233958949015238401 169440953425469211761428801)
      ·
        refine ⟨127080715069101908821071601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169440953425469211761428801 127080715069101908821071601)
        ·
          refine ⟨95310536301826431615803701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127080715069101908821071601 95310536301826431615803701)
          ·
            refine ⟨8935362778296227963981597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95310536301826431615803701 8935362778296227963981597)
            ·
              refine ⟨3350761041861085486493099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935362778296227963981597 3350761041861085486493099)
              ·
                refine ⟨5026141562791628229739649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350761041861085486493099 5026141562791628229739649)
                ·
                  refine ⟨3769606172093721172304737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026141562791628229739649 3769606172093721172304737)
                  ·
                    refine ⟨2827204629070290879228553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3769606172093721172304737 2827204629070290879228553)
                    ·
                      refine ⟨2120403471802718159421415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827204629070290879228553 2120403471802718159421415)
                      ·
                        rfl

theorem cell23_4129471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_4129471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129471 prefixEnd_4129471 := by exact prefixLift 4129471
  have htrace : WordTrace (prefixWord ++ tailWord_4129471) baseStart_4129471 baseEnd_4129471 := by
    simpa [prefixWord, tailWord_4129471, baseEnd_4129471] using wordTrace_append hprefix tailTrace_4129471
  have hstable : (prefixWord ++ tailWord_4129471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129471).length < 2 ^ (prefixWord ++ tailWord_4129471).sum := by decide
  have hdescent : baseEnd_4129471 < baseStart_4129471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129483 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_4129483 : Nat := 118140960795 + 4129483 * 2 ^ 59
def prefixEnd_4129483 : Nat := 4983230072969 + 3 ^ 40 * 4129483 * 2
def baseEnd_4129483 : Nat := 2120409633570572112471359

theorem tailTrace_4129483 : CollatzResearch.WordTrace tailWord_4129483 prefixEnd_4129483 2120409633570572112471359 := by
  unfold tailWord_4129483
  simp only [CollatzResearch.WordTrace]
  refine ⟨150614618498595825392929103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100409745665730550261952735 150614618498595825392929103)
  ·
    refine ⟨225921927747893738089393655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150614618498595825392929103 225921927747893738089393655)
    ·
      refine ⟨338882891621840607134090483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225921927747893738089393655 338882891621840607134090483)
      ·
        refine ⟨508324337432760910701135725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338882891621840607134090483 508324337432760910701135725)
        ·
          refine ⟨190621626537285341512925897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508324337432760910701135725 190621626537285341512925897)
          ·
            refine ⟨142966219902964006134694423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190621626537285341512925897 142966219902964006134694423)
            ·
              refine ⟨214449329854446009202041635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142966219902964006134694423 214449329854446009202041635)
              ·
                refine ⟨321673994781669013803062453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214449329854446009202041635 321673994781669013803062453)
                ·
                  refine ⟨30156937010781470044037105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321673994781669013803062453 30156937010781470044037105)
                  ·
                    refine ⟨22617702758086102533027829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30156937010781470044037105 22617702758086102533027829)
                    ·
                      refine ⟨2120409633570572112471359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22617702758086102533027829 2120409633570572112471359)
                      ·
                        rfl

theorem cell23_4129483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_4129483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129483 prefixEnd_4129483 := by exact prefixLift 4129483
  have htrace : WordTrace (prefixWord ++ tailWord_4129483) baseStart_4129483 baseEnd_4129483 := by
    simpa [prefixWord, tailWord_4129483, baseEnd_4129483] using wordTrace_append hprefix tailTrace_4129483
  have hstable : (prefixWord ++ tailWord_4129483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129483).length < 2 ^ (prefixWord ++ tailWord_4129483).sum := by decide
  have hdescent : baseEnd_4129483 < baseStart_4129483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129507 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 2, 5]
def baseStart_4129507 : Nat := 118140960795 + 4129507 * 2 ^ 59
def prefixEnd_4129507 : Nat := 4983230072969 + 3 ^ 40 * 4129507 * 2
def baseEnd_4129507 : Nat := 706807319035426672857083

theorem tailTrace_4129507 : CollatzResearch.WordTrace tailWord_4129507 prefixEnd_4129507 706807319035426672857083 := by
  unfold tailWord_4129507
  simp only [CollatzResearch.WordTrace]
  refine ⟨150615493850508877491802775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100410329233672584994535183 150615493850508877491802775)
  ·
    refine ⟨225923240775763316237704163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150615493850508877491802775 225923240775763316237704163)
    ·
      refine ⟨338884861163644974356556245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225923240775763316237704163 338884861163644974356556245)
      ·
        refine ⟨7942613933522929086481787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 338884861163644974356556245 7942613933522929086481787)
        ·
          refine ⟨11913920900284393629722681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942613933522929086481787 11913920900284393629722681)
          ·
            refine ⟨8935440675213295222292011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11913920900284393629722681 8935440675213295222292011)
            ·
              refine ⟨13403161012819942833438017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935440675213295222292011 13403161012819942833438017)
              ·
                refine ⟨10052370759614957125078513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13403161012819942833438017 10052370759614957125078513)
                ·
                  refine ⟨7539278069711217843808885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10052370759614957125078513 7539278069711217843808885)
                  ·
                    refine ⟨706807319035426672857083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7539278069711217843808885 706807319035426672857083)
                    ·
                      rfl

theorem cell23_4129507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].length) (baseStart_4129507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129507 prefixEnd_4129507 := by exact prefixLift 4129507
  have htrace : WordTrace (prefixWord ++ tailWord_4129507) baseStart_4129507 baseEnd_4129507 := by
    simpa [prefixWord, tailWord_4129507, baseEnd_4129507] using wordTrace_append hprefix tailTrace_4129507
  have hstable : (prefixWord ++ tailWord_4129507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129507).length < 2 ^ (prefixWord ++ tailWord_4129507).sum := by decide
  have hdescent : baseEnd_4129507 < baseStart_4129507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129530 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_4129530 : Nat := 118140960795 + 4129530 * 2 ^ 59
def prefixEnd_4129530 : Nat := 4983230072969 + 3 ^ 40 * 4129530 * 2
def baseEnd_4129530 : Nat := 2120433767161333428583643

theorem tailTrace_4129530 : CollatzResearch.WordTrace tailWord_4129530 prefixEnd_4129530 2120433767161333428583643 := by
  unfold tailWord_4129530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654083182356388104972511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100410888486283701613260029 37654083182356388104972511)
  ·
    refine ⟨56481124773534582157458767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37654083182356388104972511 56481124773534582157458767)
    ·
      refine ⟨84721687160301873236188151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56481124773534582157458767 84721687160301873236188151)
      ·
        refine ⟨127082530740452809854282227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84721687160301873236188151 127082530740452809854282227)
        ·
          refine ⟨190623796110679214781423341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127082530740452809854282227 190623796110679214781423341)
          ·
            refine ⟨71483923541504705543033753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190623796110679214781423341 71483923541504705543033753)
            ·
              refine ⟨53612942656128529157275315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71483923541504705543033753 53612942656128529157275315)
              ·
                refine ⟨80419413984192793735912973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53612942656128529157275315 80419413984192793735912973)
                ·
                  refine ⟨30157280244072297650967365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80419413984192793735912973 30157280244072297650967365)
                  ·
                    refine ⟨5654490045763555809556381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30157280244072297650967365 5654490045763555809556381)
                    ·
                      refine ⟨2120433767161333428583643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654490045763555809556381 2120433767161333428583643)
                      ·
                        rfl

theorem cell23_4129530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_4129530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129530 prefixEnd_4129530 := by exact prefixLift 4129530
  have htrace : WordTrace (prefixWord ++ tailWord_4129530) baseStart_4129530 baseEnd_4129530 := by
    simpa [prefixWord, tailWord_4129530, baseEnd_4129530] using wordTrace_append hprefix tailTrace_4129530
  have hstable : (prefixWord ++ tailWord_4129530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129530).length < 2 ^ (prefixWord ++ tailWord_4129530).sum := by decide
  have hdescent : baseEnd_4129530 < baseStart_4129530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129567 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 6]
def baseStart_4129567 : Nat := 118140960795 + 4129567 * 2 ^ 59
def prefixEnd_4129567 : Nat := 4983230072969 + 3 ^ 40 * 4129567 * 2
def baseEnd_4129567 : Nat := 235605862882838864868997

theorem tailTrace_4129567 : CollatzResearch.WordTrace tailWord_4129567 prefixEnd_4129567 235605862882838864868997 := by
  unfold tailWord_4129567
  simp only [CollatzResearch.WordTrace]
  refine ⟨150617682230291507738986955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100411788153527671825991303 150617682230291507738986955)
  ·
    refine ⟨225926523345437261608480433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150617682230291507738986955 225926523345437261608480433)
    ·
      refine ⟨169444892509077946206360325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225926523345437261608480433 169444892509077946206360325)
      ·
        refine ⟨31770917345452114913692561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169444892509077946206360325 31770917345452114913692561)
        ·
          refine ⟨23828188009089086185269421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770917345452114913692561 23828188009089086185269421)
          ·
            refine ⟨8935570503408407319476033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23828188009089086185269421 8935570503408407319476033)
            ·
              refine ⟨6701677877556305489607025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935570503408407319476033 6701677877556305489607025)
              ·
                refine ⟨5026258408167229117205269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701677877556305489607025 5026258408167229117205269)
                ·
                  refine ⟨235605862882838864868997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5026258408167229117205269 235605862882838864868997)
                  ·
                    rfl

theorem cell23_4129567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 6].length) (baseStart_4129567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129567 prefixEnd_4129567 := by exact prefixLift 4129567
  have htrace : WordTrace (prefixWord ++ tailWord_4129567) baseStart_4129567 baseEnd_4129567 := by
    simpa [prefixWord, tailWord_4129567, baseEnd_4129567] using wordTrace_append hprefix tailTrace_4129567
  have hstable : (prefixWord ++ tailWord_4129567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129567).length < 2 ^ (prefixWord ++ tailWord_4129567).sum := by decide
  have hdescent : baseEnd_4129567 < baseStart_4129567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129580 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_4129580 : Nat := 118140960795 + 4129580 * 2 ^ 59
def prefixEnd_4129580 : Nat := 4983230072969 + 3 ^ 40 * 4129580 * 2
def baseEnd_4129580 : Nat := 706819813731352744319471

theorem tailTrace_4129580 : CollatzResearch.WordTrace tailWord_4129580 prefixEnd_4129580 706819813731352744319471 := by
  unfold tailWord_4129580
  simp only [CollatzResearch.WordTrace]
  refine ⟨75309078189622205479605097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100412104252829607306140129 75309078189622205479605097)
  ·
    refine ⟨56481808642216654109703823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75309078189622205479605097 56481808642216654109703823)
    ·
      refine ⟨84722712963324981164555735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56481808642216654109703823 84722712963324981164555735)
      ·
        refine ⟨127084069444987471746833603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84722712963324981164555735 127084069444987471746833603)
        ·
          refine ⟨190626104167481207620250405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127084069444987471746833603 190626104167481207620250405)
          ·
            refine ⟨35742394531402726428796951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190626104167481207620250405 35742394531402726428796951)
            ·
              refine ⟨53613591797104089643195427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35742394531402726428796951 53613591797104089643195427)
              ·
                refine ⟨80420387695656134464793141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53613591797104089643195427 80420387695656134464793141)
                ·
                  refine ⟨7539411346467762606074357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80420387695656134464793141 7539411346467762606074357)
                  ·
                    refine ⟨706819813731352744319471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7539411346467762606074357 706819813731352744319471)
                    ·
                      rfl

theorem cell23_4129580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_4129580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129580 prefixEnd_4129580 := by exact prefixLift 4129580
  have htrace : WordTrace (prefixWord ++ tailWord_4129580) baseStart_4129580 baseEnd_4129580 := by
    simpa [prefixWord, tailWord_4129580, baseEnd_4129580] using wordTrace_append hprefix tailTrace_4129580
  have hstable : (prefixWord ++ tailWord_4129580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129580).length < 2 ^ (prefixWord ++ tailWord_4129580).sum := by decide
  have hdescent : baseEnd_4129580 < baseStart_4129580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129598 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4129598 : Nat := 118140960795 + 4129598 * 2 ^ 59
def prefixEnd_4129598 : Nat := 4983230072969 + 3 ^ 40 * 4129598 * 2
def baseEnd_4129598 : Nat := 2120468683845839162533331

theorem tailTrace_4129598 : CollatzResearch.WordTrace tailWord_4129598 prefixEnd_4129598 2120468683845839162533331 := by
  unfold tailWord_4129598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827351611647400004170681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100412541928786133355576965 18827351611647400004170681)
  ·
    refine ⟨14120513708735550003128011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18827351611647400004170681 14120513708735550003128011)
    ·
      refine ⟨21180770563103325004692017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120513708735550003128011 21180770563103325004692017)
      ·
        refine ⟨15885577922327493753519013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21180770563103325004692017 15885577922327493753519013)
        ·
          refine ⟨2978545860436405078784815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15885577922327493753519013 2978545860436405078784815)
          ·
            refine ⟨4467818790654607618177223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978545860436405078784815 4467818790654607618177223)
            ·
              refine ⟨6701728185981911427265835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467818790654607618177223 6701728185981911427265835)
              ·
                refine ⟨10052592278972867140898753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701728185981911427265835 10052592278972867140898753)
                ·
                  refine ⟨7539444209229650355674065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10052592278972867140898753 7539444209229650355674065)
                  ·
                    refine ⟨5654583156922237766755549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539444209229650355674065 5654583156922237766755549)
                    ·
                      refine ⟨2120468683845839162533331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654583156922237766755549 2120468683845839162533331)
                      ·
                        rfl

theorem cell23_4129598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4129598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129598 prefixEnd_4129598 := by exact prefixLift 4129598
  have htrace : WordTrace (prefixWord ++ tailWord_4129598) baseStart_4129598 baseEnd_4129598 := by
    simpa [prefixWord, tailWord_4129598, baseEnd_4129598] using wordTrace_append hprefix tailTrace_4129598
  have hstable : (prefixWord ++ tailWord_4129598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129598).length < 2 ^ (prefixWord ++ tailWord_4129598).sum := by decide
  have hdescent : baseEnd_4129598 < baseStart_4129598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129610 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4129610 : Nat := 118140960795 + 4129610 * 2 ^ 59
def prefixEnd_4129610 : Nat := 4983230072969 + 3 ^ 40 * 4129610 * 2
def baseEnd_4129610 : Nat := 706824948537897705194425

theorem tailTrace_4129610 : CollatzResearch.WordTrace tailWord_4129610 prefixEnd_4129610 706824948537897705194425 := by
  unfold tailWord_4129610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654812642283931520700571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100412833712757150721868189 37654812642283931520700571)
  ·
    refine ⟨56482218963425897281050857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37654812642283931520700571 56482218963425897281050857)
    ·
      refine ⟨42361664222569422960788143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56482218963425897281050857 42361664222569422960788143)
      ·
        refine ⟨63542496333854134441182215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42361664222569422960788143 63542496333854134441182215)
        ·
          refine ⟨95313744500781201661773323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63542496333854134441182215 95313744500781201661773323)
          ·
            refine ⟨142970616751171802492659985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95313744500781201661773323 142970616751171802492659985)
            ·
              refine ⟨107227962563378851869494989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142970616751171802492659985 107227962563378851869494989)
              ·
                refine ⟨40210485961267069451060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107227962563378851869494989 40210485961267069451060621)
                ·
                  refine ⟨15078932235475151044147733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40210485961267069451060621 15078932235475151044147733)
                  ·
                    refine ⟨706824948537897705194425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15078932235475151044147733 706824948537897705194425)
                    ·
                      rfl

theorem cell23_4129610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4129610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129610 prefixEnd_4129610 := by exact prefixLift 4129610
  have htrace : WordTrace (prefixWord ++ tailWord_4129610) baseStart_4129610 baseEnd_4129610 := by
    simpa [prefixWord, tailWord_4129610, baseEnd_4129610] using wordTrace_append hprefix tailTrace_4129610
  have hstable : (prefixWord ++ tailWord_4129610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129610).length < 2 ^ (prefixWord ++ tailWord_4129610).sum := by decide
  have hdescent : baseEnd_4129610 < baseStart_4129610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129628 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4129628 : Nat := 118140960795 + 4129628 * 2 ^ 59
def prefixEnd_4129628 : Nat := 4983230072969 + 3 ^ 40 * 4129628 * 2
def baseEnd_4129628 : Nat := 2120484088265474045158193

theorem tailTrace_4129628 : CollatzResearch.WordTrace tailWord_4129628 prefixEnd_4129628 2120484088265474045158193 := by
  unfold tailWord_4129628
  simp only [CollatzResearch.WordTrace]
  refine ⟨75309953541535257578478769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100413271388713676771305025 75309953541535257578478769)
  ·
    refine ⟨56482465156151443183859077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75309953541535257578478769 56482465156151443183859077)
    ·
      refine ⟨10590462216778395596973577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56482465156151443183859077 10590462216778395596973577)
      ·
        refine ⟨7942846662583796697730183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10590462216778395596973577 7942846662583796697730183)
        ·
          refine ⟨11914269993875695046595275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942846662583796697730183 11914269993875695046595275)
          ·
            refine ⟨17871404990813542569892913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914269993875695046595275 17871404990813542569892913)
            ·
              refine ⟨13403553743110156927419685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17871404990813542569892913 13403553743110156927419685)
              ·
                refine ⟨2513166326833154423891191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13403553743110156927419685 2513166326833154423891191)
                ·
                  refine ⟨3769749490249731635836787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513166326833154423891191 3769749490249731635836787)
                  ·
                    refine ⟨5654624235374597453755181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769749490249731635836787 5654624235374597453755181)
                    ·
                      refine ⟨2120484088265474045158193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654624235374597453755181 2120484088265474045158193)
                      ·
                        rfl

theorem cell23_4129628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4129628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129628 prefixEnd_4129628 := by exact prefixLift 4129628
  have htrace : WordTrace (prefixWord ++ tailWord_4129628) baseStart_4129628 baseEnd_4129628 := by
    simpa [prefixWord, tailWord_4129628, baseEnd_4129628] using wordTrace_append hprefix tailTrace_4129628
  have hstable : (prefixWord ++ tailWord_4129628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129628).length < 2 ^ (prefixWord ++ tailWord_4129628).sum := by decide
  have hdescent : baseEnd_4129628 < baseStart_4129628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129637 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4129637 : Nat := 118140960795 + 4129637 * 2 ^ 59
def prefixEnd_4129637 : Nat := 4983230072969 + 3 ^ 40 * 4129637 * 2
def baseEnd_4129637 : Nat := 2120488709591364509945651

theorem tailTrace_4129637 : CollatzResearch.WordTrace tailWord_4129637 prefixEnd_4129637 2120488709591364509945651 := by
  unfold tailWord_4129637
  simp only [CollatzResearch.WordTrace]
  refine ⟨150620235340037909694035165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100413490226691939796023443 150620235340037909694035165)
  ·
    refine ⟨56482588252514216135263187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150620235340037909694035165 56482588252514216135263187)
    ·
      refine ⟨84723882378771324202894781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56482588252514216135263187 84723882378771324202894781)
      ·
        refine ⟨31771455892039246576085543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84723882378771324202894781 31771455892039246576085543)
        ·
          refine ⟨47657183838058869864128315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31771455892039246576085543 47657183838058869864128315)
          ·
            refine ⟨71485775757088304796192473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47657183838058869864128315 71485775757088304796192473)
            ·
              refine ⟨53614331817816228597144355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71485775757088304796192473 53614331817816228597144355)
              ·
                refine ⟨80421497726724342895716533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53614331817816228597144355 80421497726724342895716533)
                ·
                  refine ⟨7539515411880407146473425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80421497726724342895716533 7539515411880407146473425)
                  ·
                    refine ⟨5654636558910305359855069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539515411880407146473425 5654636558910305359855069)
                    ·
                      refine ⟨2120488709591364509945651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654636558910305359855069 2120488709591364509945651)
                      ·
                        rfl

theorem cell23_4129637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4129637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129637 prefixEnd_4129637 := by exact prefixLift 4129637
  have htrace : WordTrace (prefixWord ++ tailWord_4129637) baseStart_4129637 baseEnd_4129637 := by
    simpa [prefixWord, tailWord_4129637, baseEnd_4129637] using wordTrace_append hprefix tailTrace_4129637
  have hstable : (prefixWord ++ tailWord_4129637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129637).length < 2 ^ (prefixWord ++ tailWord_4129637).sum := by decide
  have hdescent : baseEnd_4129637 < baseStart_4129637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129657 : List Nat := [1, 2, 1, 3, 2, 3, 4, 7]
def baseStart_4129657 : Nat := 118140960795 + 4129657 * 2 ^ 59
def prefixEnd_4129657 : Nat := 4983230072969 + 3 ^ 40 * 4129657 * 2
def baseEnd_4129657 : Nat := 78536999229794608581317

theorem tailTrace_4129657 : CollatzResearch.WordTrace tailWord_4129657 prefixEnd_4129657 78536999229794608581317 := by
  unfold tailWord_4129657
  simp only [CollatzResearch.WordTrace]
  refine ⟨150620964799965453109763225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100413976533310302073175483 150620964799965453109763225)
  ·
    refine ⟨112965723599974089832322419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150620964799965453109763225 112965723599974089832322419)
    ·
      refine ⟨169448585399961134748483629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112965723599974089832322419 169448585399961134748483629)
      ·
        refine ⟨63543219524985425530681361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169448585399961134748483629 63543219524985425530681361)
        ·
          refine ⟨47657414643739069148011021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63543219524985425530681361 47657414643739069148011021)
          ·
            refine ⟨17871530491402150930504133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47657414643739069148011021 17871530491402150930504133)
            ·
              refine ⟨3350911967137903299469525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17871530491402150930504133 3350911967137903299469525)
              ·
                refine ⟨78536999229794608581317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3350911967137903299469525 78536999229794608581317)
                ·
                  rfl

theorem cell23_4129657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 7].length) (baseStart_4129657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129657 prefixEnd_4129657 := by exact prefixLift 4129657
  have htrace : WordTrace (prefixWord ++ tailWord_4129657) baseStart_4129657 baseEnd_4129657 := by
    simpa [prefixWord, tailWord_4129657, baseEnd_4129657] using wordTrace_append hprefix tailTrace_4129657
  have hstable : (prefixWord ++ tailWord_4129657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129657).length < 2 ^ (prefixWord ++ tailWord_4129657).sum := by decide
  have hdescent : baseEnd_4129657 < baseStart_4129657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_4129660 : Nat := 118140960795 + 4129660 * 2 ^ 59
def prefixEnd_4129660 : Nat := 4983230072969 + 3 ^ 40 * 4129660 * 2
def baseEnd_4129660 : Nat := 2120500519646417919958045

theorem tailTrace_4129660 : CollatzResearch.WordTrace tailWord_4129660 prefixEnd_4129660 2120500519646417919958045 := by
  unfold tailWord_4129660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75310537109477292311061217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100414049479303056414748289 75310537109477292311061217)
  ·
    refine ⟨56482902832107969233295913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75310537109477292311061217 56482902832107969233295913)
    ·
      refine ⟨42362177124080976924971935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56482902832107969233295913 42362177124080976924971935)
      ·
        refine ⟨63543265686121465387457903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362177124080976924971935 63543265686121465387457903)
        ·
          refine ⟨95314898529182198081186855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63543265686121465387457903 95314898529182198081186855)
          ·
            refine ⟨142972347793773297121780283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95314898529182198081186855 142972347793773297121780283)
            ·
              refine ⟨214458521690659945682670425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142972347793773297121780283 214458521690659945682670425)
              ·
                refine ⟨160843891267994959262002819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214458521690659945682670425 160843891267994959262002819)
                ·
                  refine ⟨241265836901992438893004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160843891267994959262002819 241265836901992438893004229)
                  ·
                    refine ⟨45237344419123582292438293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241265836901992438893004229 45237344419123582292438293)
                    ·
                      refine ⟨2120500519646417919958045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45237344419123582292438293 2120500519646417919958045)
                      ·
                        rfl

theorem cell23_4129660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_4129660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129660 prefixEnd_4129660 := by exact prefixLift 4129660
  have htrace : WordTrace (prefixWord ++ tailWord_4129660) baseStart_4129660 baseEnd_4129660 := by
    simpa [prefixWord, tailWord_4129660, baseEnd_4129660] using wordTrace_append hprefix tailTrace_4129660
  have hstable : (prefixWord ++ tailWord_4129660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129660).length < 2 ^ (prefixWord ++ tailWord_4129660).sum := by decide
  have hdescent : baseEnd_4129660 < baseStart_4129660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129662 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4129662 : Nat := 118140960795 + 4129662 * 2 ^ 59
def prefixEnd_4129662 : Nat := 4983230072969 + 3 ^ 40 * 4129662 * 2
def baseEnd_4129662 : Nat := 2120501546607726912133037

theorem tailTrace_4129662 : CollatzResearch.WordTrace tailWord_4129662 prefixEnd_4129662 2120501546607726912133037 := by
  unfold tailWord_4129662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827643395618417370461905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100414098109964892642463493 18827643395618417370461905)
  ·
    refine ⟨14120732546713813027846429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18827643395618417370461905 14120732546713813027846429)
    ·
      refine ⟨5295274705017679885442411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14120732546713813027846429 5295274705017679885442411)
      ·
        refine ⟨7942912057526519828163617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295274705017679885442411 7942912057526519828163617)
        ·
          refine ⟨5957184043144889871122713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7942912057526519828163617 5957184043144889871122713)
          ·
            refine ⟨4467888032358667403342035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5957184043144889871122713 4467888032358667403342035)
            ·
              refine ⟨6701832048538001105013053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467888032358667403342035 6701832048538001105013053)
              ·
                refine ⟨2513187018201750414379895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6701832048538001105013053 2513187018201750414379895)
                ·
                  refine ⟨3769780527302625621569843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513187018201750414379895 3769780527302625621569843)
                  ·
                    refine ⟨5654670790953938432354765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3769780527302625621569843 5654670790953938432354765)
                    ·
                      refine ⟨2120501546607726912133037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654670790953938432354765 2120501546607726912133037)
                      ·
                        rfl

theorem cell23_4129662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4129662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129662 prefixEnd_4129662 := by exact prefixLift 4129662
  have htrace : WordTrace (prefixWord ++ tailWord_4129662) baseStart_4129662 baseEnd_4129662 := by
    simpa [prefixWord, tailWord_4129662, baseEnd_4129662] using wordTrace_append hprefix tailTrace_4129662
  have hstable : (prefixWord ++ tailWord_4129662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129662).length < 2 ^ (prefixWord ++ tailWord_4129662).sum := by decide
  have hdescent : baseEnd_4129662 < baseStart_4129662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129667 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3]
def baseStart_4129667 : Nat := 118140960795 + 4129667 * 2 ^ 59
def prefixEnd_4129667 : Nat := 4983230072969 + 3 ^ 40 * 4129667 * 2
def baseEnd_4129667 : Nat := 2120504114010999392570513

theorem tailTrace_4129667 : CollatzResearch.WordTrace tailWord_4129667 prefixEnd_4129667 2120504114010999392570513 := by
  unfold tailWord_4129667
  simp only [CollatzResearch.WordTrace]
  refine ⟨150621329529929224817627255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100414219686619483211751503 150621329529929224817627255)
  ·
    refine ⟨225931994294893837226440883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150621329529929224817627255 225931994294893837226440883)
    ·
      refine ⟨338897991442340755839661325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225931994294893837226440883 338897991442340755839661325)
      ·
        refine ⟨127086746790877783439872997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338897991442340755839661325 127086746790877783439872997)
        ·
          refine ⟨23828765023289584394976187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127086746790877783439872997 23828765023289584394976187)
          ·
            refine ⟨35743147534934376592464281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828765023289584394976187 35743147534934376592464281)
            ·
              refine ⟨26807360651200782444348211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35743147534934376592464281 26807360651200782444348211)
              ·
                refine ⟨40211040976801173666522317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26807360651200782444348211 40211040976801173666522317)
                ·
                  refine ⟨15079140366300440124945869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40211040976801173666522317 15079140366300440124945869)
                  ·
                    refine ⟨5654677637362665046854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15079140366300440124945869 5654677637362665046854701)
                    ·
                      refine ⟨2120504114010999392570513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654677637362665046854701 2120504114010999392570513)
                      ·
                        rfl

theorem cell23_4129667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_4129667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129667 prefixEnd_4129667 := by exact prefixLift 4129667
  have htrace : WordTrace (prefixWord ++ tailWord_4129667) baseStart_4129667 baseEnd_4129667 := by
    simpa [prefixWord, tailWord_4129667, baseEnd_4129667] using wordTrace_append hprefix tailTrace_4129667
  have hstable : (prefixWord ++ tailWord_4129667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129667).length < 2 ^ (prefixWord ++ tailWord_4129667).sum := by decide
  have hdescent : baseEnd_4129667 < baseStart_4129667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129680 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_4129680 : Nat := 118140960795 + 4129680 * 2 ^ 59
def prefixEnd_4129680 : Nat := 4983230072969 + 3 ^ 40 * 4129680 * 2
def baseEnd_4129680 : Nat := 2120510789259507841707953

theorem tailTrace_4129680 : CollatzResearch.WordTrace tailWord_4129680 prefixEnd_4129680 2120510789259507841707953 := by
  unfold tailWord_4129680
  simp only [CollatzResearch.WordTrace]
  refine ⟨75310901839441064018925247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100414535785921418691900329 75310901839441064018925247)
  ·
    refine ⟨112966352759161596028387871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75310901839441064018925247 112966352759161596028387871)
    ·
      refine ⟨169449529138742394042581807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112966352759161596028387871 169449529138742394042581807)
      ·
        refine ⟨254174293708113591063872711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169449529138742394042581807 254174293708113591063872711)
        ·
          refine ⟨381261440562170386595809067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254174293708113591063872711 381261440562170386595809067)
          ·
            refine ⟨571892160843255579893713601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381261440562170386595809067 571892160843255579893713601)
            ·
              refine ⟨428919120632441684920285201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571892160843255579893713601 428919120632441684920285201)
              ·
                refine ⟨321689340474331263690213901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428919120632441684920285201 321689340474331263690213901)
                ·
                  refine ⟨120633502677874223883830213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321689340474331263690213901 120633502677874223883830213)
                  ·
                    refine ⟨22618781752101416978218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120633502677874223883830213 22618781752101416978218165)
                    ·
                      refine ⟨2120510789259507841707953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22618781752101416978218165 2120510789259507841707953)
                      ·
                        rfl

theorem cell23_4129680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_4129680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129680 prefixEnd_4129680 := by exact prefixLift 4129680
  have htrace : WordTrace (prefixWord ++ tailWord_4129680) baseStart_4129680 baseEnd_4129680 := by
    simpa [prefixWord, tailWord_4129680, baseEnd_4129680] using wordTrace_append hprefix tailTrace_4129680
  have hstable : (prefixWord ++ tailWord_4129680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129680).length < 2 ^ (prefixWord ++ tailWord_4129680).sum := by decide
  have hdescent : baseEnd_4129680 < baseStart_4129680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129685 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_4129685 : Nat := 118140960795 + 4129685 * 2 ^ 59
def prefixEnd_4129685 : Nat := 4983230072969 + 3 ^ 40 * 4129685 * 2
def baseEnd_4129685 : Nat := 2120513356662780322145431

theorem tailTrace_4129685 : CollatzResearch.WordTrace tailWord_4129685 prefixEnd_4129685 2120513356662780322145431 := by
  unfold tailWord_4129685
  simp only [CollatzResearch.WordTrace]
  refine ⟨150621986043864013891782509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100414657362576009261188339 150621986043864013891782509)
  ·
    refine ⟨56483244766449005209418441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150621986043864013891782509 56483244766449005209418441)
    ·
      refine ⟨42362433574836753907063831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56483244766449005209418441 42362433574836753907063831)
      ·
        refine ⟨63543650362255130860595747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362433574836753907063831 63543650362255130860595747)
        ·
          refine ⟨95315475543382696290893621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63543650362255130860595747 95315475543382696290893621)
          ·
            refine ⟨8935825832192127777271277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95315475543382696290893621 8935825832192127777271277)
            ·
              refine ⟨3350934687072047916476729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935825832192127777271277 3350934687072047916476729)
              ·
                refine ⟨2513201015304035937357547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350934687072047916476729 2513201015304035937357547)
                ·
                  refine ⟨3769801522956053906036321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513201015304035937357547 3769801522956053906036321)
                  ·
                    refine ⟨2827351142217040429527241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3769801522956053906036321 2827351142217040429527241)
                    ·
                      refine ⟨2120513356662780322145431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827351142217040429527241 2120513356662780322145431)
                      ·
                        rfl

theorem cell23_4129685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_4129685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129685 prefixEnd_4129685 := by exact prefixLift 4129685
  have htrace : WordTrace (prefixWord ++ tailWord_4129685) baseStart_4129685 baseEnd_4129685 := by
    simpa [prefixWord, tailWord_4129685, baseEnd_4129685] using wordTrace_append hprefix tailTrace_4129685
  have hstable : (prefixWord ++ tailWord_4129685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129685).length < 2 ^ (prefixWord ++ tailWord_4129685).sum := by decide
  have hdescent : baseEnd_4129685 < baseStart_4129685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129728 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2]
def baseStart_4129728 : Nat := 118140960795 + 4129728 * 2 ^ 59
def prefixEnd_4129728 : Nat := 4983230072969 + 3 ^ 40 * 4129728 * 2
def baseEnd_4129728 : Nat := 2120535436330923653907733

theorem tailTrace_4129728 : CollatzResearch.WordTrace tailWord_4129728 prefixEnd_4129728 2120535436330923653907733 := by
  unfold tailWord_4129728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75311777191354116117798919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100415702921805488157065225 75311777191354116117798919)
  ·
    refine ⟨112967665787031174176698379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75311777191354116117798919 112967665787031174176698379)
    ·
      refine ⟨169451498680546761265047569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112967665787031174176698379 169451498680546761265047569)
      ·
        refine ⟨127088624010410070948785677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169451498680546761265047569 127088624010410070948785677)
        ·
          refine ⟨47658234003903776605794629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127088624010410070948785677 47658234003903776605794629)
          ·
            refine ⟨8935918875731958113586493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47658234003903776605794629 8935918875731958113586493)
            ·
              refine ⟨3350969578399484292594935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935918875731958113586493 3350969578399484292594935)
              ·
                refine ⟨5026454367599226438892403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350969578399484292594935 5026454367599226438892403)
                ·
                  refine ⟨7539681551398839658338605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026454367599226438892403 7539681551398839658338605)
                  ·
                    refine ⟨2827380581774564871876977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7539681551398839658338605 2827380581774564871876977)
                    ·
                      refine ⟨2120535436330923653907733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827380581774564871876977 2120535436330923653907733)
                      ·
                        rfl

theorem cell23_4129728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_4129728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129728 prefixEnd_4129728 := by exact prefixLift 4129728
  have htrace : WordTrace (prefixWord ++ tailWord_4129728) baseStart_4129728 baseEnd_4129728 := by
    simpa [prefixWord, tailWord_4129728, baseEnd_4129728] using wordTrace_append hprefix tailTrace_4129728
  have hstable : (prefixWord ++ tailWord_4129728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129728).length < 2 ^ (prefixWord ++ tailWord_4129728).sum := by decide
  have hdescent : baseEnd_4129728 < baseStart_4129728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129754 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_4129754 : Nat := 118140960795 + 4129754 * 2 ^ 59
def prefixEnd_4129754 : Nat := 4983230072969 + 3 ^ 40 * 4129754 * 2
def baseEnd_4129754 : Nat := 2120548786827940552182613

theorem tailTrace_4129754 : CollatzResearch.WordTrace tailWord_4129754 prefixEnd_4129754 2120548786827940552182613 := by
  unfold tailWord_4129754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656125670153509669011079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100416335120409359117362877 37656125670153509669011079)
  ·
    refine ⟨56484188505230264503516619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37656125670153509669011079 56484188505230264503516619)
    ·
      refine ⟨84726282757845396755274929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56484188505230264503516619 84726282757845396755274929)
      ·
        refine ⟨63544712068384047566456197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84726282757845396755274929 63544712068384047566456197)
        ·
          refine ⟨11914633512822008918710537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63544712068384047566456197 11914633512822008918710537)
          ·
            refine ⟨8935975134616506689032903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11914633512822008918710537 8935975134616506689032903)
            ·
              refine ⟨13403962701924760033549355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935975134616506689032903 13403962701924760033549355)
              ·
                refine ⟨20105944052887140050324033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403962701924760033549355 20105944052887140050324033)
                ·
                  refine ⟨15079458039665355037743025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20105944052887140050324033 15079458039665355037743025)
                  ·
                    refine ⟨11309593529749016278307269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15079458039665355037743025 11309593529749016278307269)
                    ·
                      refine ⟨2120548786827940552182613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11309593529749016278307269 2120548786827940552182613)
                      ·
                        rfl

theorem cell23_4129754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_4129754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129754 prefixEnd_4129754 := by exact prefixLift 4129754
  have htrace : WordTrace (prefixWord ++ tailWord_4129754) baseStart_4129754 baseEnd_4129754 := by
    simpa [prefixWord, tailWord_4129754, baseEnd_4129754] using wordTrace_append hprefix tailTrace_4129754
  have hstable : (prefixWord ++ tailWord_4129754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129754).length < 2 ^ (prefixWord ++ tailWord_4129754).sum := by decide
  have hdescent : baseEnd_4129754 < baseStart_4129754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129831 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4129831 : Nat := 118140960795 + 4129831 * 2 ^ 59
def prefixEnd_4129831 : Nat := 4983230072969 + 3 ^ 40 * 4129831 * 2
def baseEnd_4129831 : Nat := 2120588324838336750919759

theorem tailTrace_4129831 : CollatzResearch.WordTrace tailWord_4129831 prefixEnd_4129831 2120588324838336750919759 := by
  unfold tailWord_4129831
  simp only [CollatzResearch.WordTrace]
  refine ⟨150627311101335080826597347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100418207400890053884398231 150627311101335080826597347)
  ·
    refine ⟨225940966652002621239896021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150627311101335080826597347 225940966652002621239896021)
    ·
      refine ⟨5295491405906311435310063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225940966652002621239896021 5295491405906311435310063)
      ·
        refine ⟨7943237108859467152965095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295491405906311435310063 7943237108859467152965095)
        ·
          refine ⟨11914855663289200729447643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943237108859467152965095 11914855663289200729447643)
          ·
            refine ⟨17872283494933801094171465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914855663289200729447643 17872283494933801094171465)
            ·
              refine ⟨13404212621200350820628599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872283494933801094171465 13404212621200350820628599)
              ·
                refine ⟨20106318931800526230942899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404212621200350820628599 20106318931800526230942899)
                ·
                  refine ⟨30159478397700789346414349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20106318931800526230942899 30159478397700789346414349)
                  ·
                    refine ⟨11309804399137796004905381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30159478397700789346414349 11309804399137796004905381)
                    ·
                      refine ⟨2120588324838336750919759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11309804399137796004905381 2120588324838336750919759)
                      ·
                        rfl

theorem cell23_4129831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4129831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129831 prefixEnd_4129831 := by exact prefixLift 4129831
  have htrace : WordTrace (prefixWord ++ tailWord_4129831) baseStart_4129831 baseEnd_4129831 := by
    simpa [prefixWord, tailWord_4129831, baseEnd_4129831] using wordTrace_append hprefix tailTrace_4129831
  have hstable : (prefixWord ++ tailWord_4129831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129831).length < 2 ^ (prefixWord ++ tailWord_4129831).sum := by decide
  have hdescent : baseEnd_4129831 < baseStart_4129831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129885 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4129885 : Nat := 118140960795 + 4129885 * 2 ^ 59
def prefixEnd_4129885 : Nat := 4983230072969 + 3 ^ 40 * 4129885 * 2
def baseEnd_4129885 : Nat := 2120616052793679539644511

theorem tailTrace_4129885 : CollatzResearch.WordTrace tailWord_4129885 prefixEnd_4129885 2120616052793679539644511 := by
  unfold tailWord_4129885
  simp only [CollatzResearch.WordTrace]
  refine ⟨150629280643139448049063109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100419520428759632032708739 150629280643139448049063109)
  ·
    refine ⟨28242990120588646509199333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150629280643139448049063109 28242990120588646509199333)
    ·
      refine ⟨5295560647610371220474875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28242990120588646509199333 5295560647610371220474875)
      ·
        refine ⟨7943340971415556830712313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295560647610371220474875 7943340971415556830712313)
        ·
          refine ⟨5957505728561667623034235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943340971415556830712313 5957505728561667623034235)
          ·
            refine ⟨8936258592842501434551353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957505728561667623034235 8936258592842501434551353)
            ·
              refine ⟨6702193944631876075913515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936258592842501434551353 6702193944631876075913515)
              ·
                refine ⟨10053290916947814113870273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702193944631876075913515 10053290916947814113870273)
                ·
                  refine ⟨7539968187710860585402705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10053290916947814113870273 7539968187710860585402705)
                  ·
                    refine ⟨5654976140783145439052029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539968187710860585402705 5654976140783145439052029)
                    ·
                      refine ⟨2120616052793679539644511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5654976140783145439052029 2120616052793679539644511)
                      ·
                        rfl

theorem cell23_4129885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4129885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129885 prefixEnd_4129885 := by exact prefixLift 4129885
  have htrace : WordTrace (prefixWord ++ tailWord_4129885) baseStart_4129885 baseEnd_4129885 := by
    simpa [prefixWord, tailWord_4129885, baseEnd_4129885] using wordTrace_append hprefix tailTrace_4129885
  have hstable : (prefixWord ++ tailWord_4129885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129885).length < 2 ^ (prefixWord ++ tailWord_4129885).sum := by decide
  have hdescent : baseEnd_4129885 < baseStart_4129885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129909 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4129909 : Nat := 118140960795 + 4129909 * 2 ^ 59
def prefixEnd_4129909 : Nat := 4983230072969 + 3 ^ 40 * 4129909 * 2
def baseEnd_4129909 : Nat := 706876125443129148581467

theorem tailTrace_4129909 : CollatzResearch.WordTrace tailWord_4129909 prefixEnd_4129909 706876125443129148581467 := by
  unfold tailWord_4129909
  simp only [CollatzResearch.WordTrace]
  refine ⟨150630155995052500147936781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100420103996701666765291187 150630155995052500147936781)
  ·
    refine ⟨56486308498144687555476293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150630155995052500147936781 56486308498144687555476293)
    ·
      refine ⟨10591182843402128916651805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56486308498144687555476293 10591182843402128916651805)
      ·
        refine ⟨3971693566275798343744427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10591182843402128916651805 3971693566275798343744427)
        ·
          refine ⟨5957540349413697515616641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971693566275798343744427 5957540349413697515616641)
          ·
            refine ⟨4468155262060273136712481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5957540349413697515616641 4468155262060273136712481)
            ·
              refine ⟨3351116446545204852534361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468155262060273136712481 3351116446545204852534361)
              ·
                refine ⟨2513337334908903639400771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351116446545204852534361 2513337334908903639400771)
                ·
                  refine ⟨3770006002363355459101157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513337334908903639400771 3770006002363355459101157)
                  ·
                    refine ⟨706876125443129148581467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770006002363355459101157 706876125443129148581467)
                    ·
                      rfl

theorem cell23_4129909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4129909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129909 prefixEnd_4129909 := by exact prefixLift 4129909
  have htrace : WordTrace (prefixWord ++ tailWord_4129909) baseStart_4129909 baseEnd_4129909 := by
    simpa [prefixWord, tailWord_4129909, baseEnd_4129909] using wordTrace_append hprefix tailTrace_4129909
  have hstable : (prefixWord ++ tailWord_4129909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129909).length < 2 ^ (prefixWord ++ tailWord_4129909).sum := by decide
  have hdescent : baseEnd_4129909 < baseStart_4129909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129921 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4129921 : Nat := 118140960795 + 4129921 * 2 ^ 59
def prefixEnd_4129921 : Nat := 4983230072969 + 3 ^ 40 * 4129921 * 2
def baseEnd_4129921 : Nat := 2120634538097241398794345

theorem tailTrace_4129921 : CollatzResearch.WordTrace tailWord_4129921 prefixEnd_4129921 2120634538097241398794345 := by
  unfold tailWord_4129921
  simp only [CollatzResearch.WordTrace]
  refine ⟨150630593671009026197373617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100420395780672684131582411 150630593671009026197373617)
  ·
    refine ⟨112972945253256769648030213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150630593671009026197373617 112972945253256769648030213)
    ·
      refine ⟨21182427234985644309005665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112972945253256769648030213 21182427234985644309005665)
      ·
        refine ⟨15886820426239233231754249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21182427234985644309005665 15886820426239233231754249)
        ·
          refine ⟨11915115319679424923815687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15886820426239233231754249 11915115319679424923815687)
          ·
            refine ⟨17872672979519137385723531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915115319679424923815687 17872672979519137385723531)
            ·
              refine ⟨26809009469278706078585297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872672979519137385723531 26809009469278706078585297)
              ·
                refine ⟨20106757101959029558938973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26809009469278706078585297 20106757101959029558938973)
                ·
                  refine ⟨7540033913234636084602115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20106757101959029558938973 7540033913234636084602115)
                  ·
                    refine ⟨11310050869851954126903173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540033913234636084602115 11310050869851954126903173)
                    ·
                      refine ⟨2120634538097241398794345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11310050869851954126903173 2120634538097241398794345)
                      ·
                        rfl

theorem cell23_4129921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4129921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129921 prefixEnd_4129921 := by exact prefixLift 4129921
  have htrace : WordTrace (prefixWord ++ tailWord_4129921) baseStart_4129921 baseEnd_4129921 := by
    simpa [prefixWord, tailWord_4129921, baseEnd_4129921] using wordTrace_append hprefix tailTrace_4129921
  have hstable : (prefixWord ++ tailWord_4129921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129921).length < 2 ^ (prefixWord ++ tailWord_4129921).sum := by decide
  have hdescent : baseEnd_4129921 < baseStart_4129921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129985 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4129985 : Nat := 118140960795 + 4129985 * 2 ^ 59
def prefixEnd_4129985 : Nat := 4983230072969 + 3 ^ 40 * 4129985 * 2
def baseEnd_4129985 : Nat := 2120667400859129148394051

theorem tailTrace_4129985 : CollatzResearch.WordTrace tailWord_4129985 prefixEnd_4129985 2120667400859129148394051 := by
  unfold tailWord_4129985
  simp only [CollatzResearch.WordTrace]
  refine ⟨150632927942777165127703409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100421951961851443418468939 150632927942777165127703409)
  ·
    refine ⟨112974695957082873845777557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150632927942777165127703409 112974695957082873845777557)
    ·
      refine ⟨5295688872988259711520823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112974695957082873845777557 5295688872988259711520823)
      ·
        refine ⟨7943533309482389567281235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295688872988259711520823 7943533309482389567281235)
        ·
          refine ⟨11915299964223584350921853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943533309482389567281235 11915299964223584350921853)
          ·
            refine ⟨4468237486583844131595695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11915299964223584350921853 4468237486583844131595695)
            ·
              refine ⟨6702356229875766197393543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468237486583844131595695 6702356229875766197393543)
              ·
                refine ⟨10053534344813649296090315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702356229875766197393543 10053534344813649296090315)
                ·
                  refine ⟨15080301517220473944135473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053534344813649296090315 15080301517220473944135473)
                  ·
                    refine ⟨11310226137915355458101605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15080301517220473944135473 11310226137915355458101605)
                    ·
                      refine ⟨2120667400859129148394051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11310226137915355458101605 2120667400859129148394051)
                      ·
                        rfl

theorem cell23_4129985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4129985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4129985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4129985 prefixEnd_4129985 := by exact prefixLift 4129985
  have htrace : WordTrace (prefixWord ++ tailWord_4129985) baseStart_4129985 baseEnd_4129985 := by
    simpa [prefixWord, tailWord_4129985, baseEnd_4129985] using wordTrace_append hprefix tailTrace_4129985
  have hstable : (prefixWord ++ tailWord_4129985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129985).length < 2 ^ (prefixWord ++ tailWord_4129985).sum := by decide
  have hdescent : baseEnd_4129985 < baseStart_4129985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130064 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_4130064 : Nat := 118140960795 + 4130064 * 2 ^ 59
def prefixEnd_4130064 : Nat := 4983230072969 + 3 ^ 40 * 4130064 * 2
def baseEnd_4130064 : Nat := 706902655276944779768729

theorem tailTrace_4130064 : CollatzResearch.WordTrace tailWord_4130064 prefixEnd_4130064 706902655276944779768729 := by
  unfold tailWord_4130064
  simp only [CollatzResearch.WordTrace]
  refine ⟨75317904654745480809914623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100423872872993974413219497 75317904654745480809914623)
  ·
    refine ⟨112976856982118221214871935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75317904654745480809914623 112976856982118221214871935)
    ·
      refine ⟨169465285473177331822307903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112976856982118221214871935 169465285473177331822307903)
      ·
        refine ⟨254197928209765997733461855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169465285473177331822307903 254197928209765997733461855)
        ·
          refine ⟨381296892314648996600192783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254197928209765997733461855 381296892314648996600192783)
          ·
            refine ⟨571945338471973494900289175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381296892314648996600192783 571945338471973494900289175)
            ·
              refine ⟨857918007707960242350433763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571945338471973494900289175 857918007707960242350433763)
              ·
                refine ⟨1286877011561940363525650645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857918007707960242350433763 1286877011561940363525650645)
                ·
                  refine ⟨30161179958482977270132437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1286877011561940363525650645 30161179958482977270132437)
                  ·
                    refine ⟨706902655276944779768729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30161179958482977270132437 706902655276944779768729)
                    ·
                      rfl

theorem cell23_4130064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_4130064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130064 prefixEnd_4130064 := by exact prefixLift 4130064
  have htrace : WordTrace (prefixWord ++ tailWord_4130064) baseStart_4130064 baseEnd_4130064 := by
    simpa [prefixWord, tailWord_4130064, baseEnd_4130064] using wordTrace_append hprefix tailTrace_4130064
  have hstable : (prefixWord ++ tailWord_4130064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130064).length < 2 ^ (prefixWord ++ tailWord_4130064).sum := by decide
  have hdescent : baseEnd_4130064 < baseStart_4130064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130066 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4130066 : Nat := 118140960795 + 4130066 * 2 ^ 59
def prefixEnd_4130066 : Nat := 4983230072969 + 3 ^ 40 * 4130066 * 2
def baseEnd_4130066 : Nat := 2120708992792143331481179

theorem tailTrace_4130066 : CollatzResearch.WordTrace tailWord_4130066 prefixEnd_4130066 2120708992792143331481179 := by
  unfold tailWord_4130066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37658970563870928990350513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100423921503655810640934701 37658970563870928990350513)
  ·
    refine ⟨28244227922903196742762885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37658970563870928990350513 28244227922903196742762885)
    ·
      refine ⟨5295792735544349389268041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28244227922903196742762885 5295792735544349389268041)
      ·
        refine ⟨3971844551658262041951031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5295792735544349389268041 3971844551658262041951031)
        ·
          refine ⟨5957766827487393062926547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971844551658262041951031 5957766827487393062926547)
          ·
            refine ⟨8936650241231089594389821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957766827487393062926547 8936650241231089594389821)
            ·
              refine ⟨3351243840461658597896183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8936650241231089594389821 3351243840461658597896183)
              ·
                refine ⟨5026865760692487896844275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351243840461658597896183 5026865760692487896844275)
                ·
                  refine ⟨7540298641038731845266413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026865760692487896844275 7540298641038731845266413)
                  ·
                    refine ⟨2827611990389524441974905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7540298641038731845266413 2827611990389524441974905)
                    ·
                      refine ⟨2120708992792143331481179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827611990389524441974905 2120708992792143331481179)
                      ·
                        rfl

theorem cell23_4130066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4130066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130066 prefixEnd_4130066 := by exact prefixLift 4130066
  have htrace : WordTrace (prefixWord ++ tailWord_4130066) baseStart_4130066 baseEnd_4130066 := by
    simpa [prefixWord, tailWord_4130066, baseEnd_4130066] using wordTrace_append hprefix tailTrace_4130066
  have hstable : (prefixWord ++ tailWord_4130066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130066).length < 2 ^ (prefixWord ++ tailWord_4130066).sum := by decide
  have hdescent : baseEnd_4130066 < baseStart_4130066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130085 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 5]
def baseStart_4130085 : Nat := 118140960795 + 4130085 * 2 ^ 59
def prefixEnd_4130085 : Nat := 4983230072969 + 3 ^ 40 * 4130085 * 2
def baseEnd_4130085 : Nat := 235635416547175417460399

theorem tailTrace_4130085 : CollatzResearch.WordTrace tailWord_4130085 prefixEnd_4130085 235635416547175417460399 := by
  unfold tailWord_4130085
  simp only [CollatzResearch.WordTrace]
  refine ⟨150636575242414882206343709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100424383494943254804229139 150636575242414882206343709)
  ·
    refine ⟨56488715715905580827378891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150636575242414882206343709 56488715715905580827378891)
    ·
      refine ⟨84733073573858371241068337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56488715715905580827378891 84733073573858371241068337)
      ·
        refine ⟨63549805180393778430801253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84733073573858371241068337 63549805180393778430801253)
        ·
          refine ⟨11915588471323833455775235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63549805180393778430801253 11915588471323833455775235)
          ·
            refine ⟨17873382706985750183662853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915588471323833455775235 17873382706985750183662853)
            ·
              refine ⟨3351259257559828159436785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17873382706985750183662853 3351259257559828159436785)
              ·
                refine ⟨2513444443169871119577589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351259257559828159436785 2513444443169871119577589)
                ·
                  refine ⟨235635416547175417460399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513444443169871119577589 235635416547175417460399)
                  ·
                    rfl

theorem cell23_4130085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_4130085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130085 prefixEnd_4130085 := by exact prefixLift 4130085
  have htrace : WordTrace (prefixWord ++ tailWord_4130085) baseStart_4130085 baseEnd_4130085 := by
    simpa [prefixWord, tailWord_4130085, baseEnd_4130085] using wordTrace_append hprefix tailTrace_4130085
  have hstable : (prefixWord ++ tailWord_4130085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130085).length < 2 ^ (prefixWord ++ tailWord_4130085).sum := by decide
  have hdescent : baseEnd_4130085 < baseStart_4130085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130138 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_4130138 : Nat := 118140960795 + 4130138 * 2 ^ 59
def prefixEnd_4130138 : Nat := 4983230072969 + 3 ^ 40 * 4130138 * 2
def baseEnd_4130138 : Nat := 2120745963399267049780847

theorem tailTrace_4130138 : CollatzResearch.WordTrace tailWord_4130138 prefixEnd_4130138 2120745963399267049780847 := by
  unfold tailWord_4130138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37659627077805718064505767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100425672207481914838682045 37659627077805718064505767)
  ·
    refine ⟨56489440616708577096758651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37659627077805718064505767 56489440616708577096758651)
    ·
      refine ⟨84734160925062865645137977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56489440616708577096758651 84734160925062865645137977)
      ·
        refine ⟨63550620693797149233853483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84734160925062865645137977 63550620693797149233853483)
        ·
          refine ⟨95325931040695723850780225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63550620693797149233853483 95325931040695723850780225)
          ·
            refine ⟨71494448280521792888085169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95325931040695723850780225 71494448280521792888085169)
            ·
              refine ⟨53620836210391344666063877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71494448280521792888085169 53620836210391344666063877)
              ·
                refine ⟨10053906789448377124886977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53620836210391344666063877 10053906789448377124886977)
                ·
                  refine ⟨7540430092086282843665233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10053906789448377124886977 7540430092086282843665233)
                  ·
                    refine ⟨5655322569064712132748925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7540430092086282843665233 5655322569064712132748925)
                    ·
                      refine ⟨2120745963399267049780847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5655322569064712132748925 2120745963399267049780847)
                      ·
                        rfl

theorem cell23_4130138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_4130138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130138 prefixEnd_4130138 := by exact prefixLift 4130138
  have htrace : WordTrace (prefixWord ++ tailWord_4130138) baseStart_4130138 baseEnd_4130138 := by
    simpa [prefixWord, tailWord_4130138, baseEnd_4130138] using wordTrace_append hprefix tailTrace_4130138
  have hstable : (prefixWord ++ tailWord_4130138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130138).length < 2 ^ (prefixWord ++ tailWord_4130138).sum := by decide
  have hdescent : baseEnd_4130138 < baseStart_4130138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130188 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_4130188 : Nat := 118140960795 + 4130188 * 2 ^ 59
def prefixEnd_4130188 : Nat := 4983230072969 + 3 ^ 40 * 4130188 * 2
def baseEnd_4130188 : Nat := 706923879143997284718539

theorem tailTrace_4130188 : CollatzResearch.WordTrace tailWord_4130188 prefixEnd_4130188 706923879143997284718539 := by
  unfold tailWord_4130188
  simp only [CollatzResearch.WordTrace]
  refine ⟨75320165980520865398671609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100426887974027820531562145 75320165980520865398671609)
  ·
    refine ⟨56490124485390649049003707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75320165980520865398671609 56490124485390649049003707)
    ·
      refine ⟨84735186728085973573505561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56490124485390649049003707 84735186728085973573505561)
      ·
        refine ⟨63551390046064480180129171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84735186728085973573505561 63551390046064480180129171)
        ·
          refine ⟨95327085069096720270193757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63551390046064480180129171 95327085069096720270193757)
          ·
            refine ⟨35747656900911270101322659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95327085069096720270193757 35747656900911270101322659)
            ·
              refine ⟨53621485351366905151983989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35747656900911270101322659 53621485351366905151983989)
              ·
                refine ⟨5027014251690647357998499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53621485351366905151983989 5027014251690647357998499)
                ·
                  refine ⟨7540521377535971036997749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027014251690647357998499 7540521377535971036997749)
                  ·
                    refine ⟨706923879143997284718539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7540521377535971036997749 706923879143997284718539)
                    ·
                      rfl

theorem cell23_4130188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_4130188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130188 prefixEnd_4130188 := by exact prefixLift 4130188
  have htrace : WordTrace (prefixWord ++ tailWord_4130188) baseStart_4130188 baseEnd_4130188 := by
    simpa [prefixWord, tailWord_4130188, baseEnd_4130188] using wordTrace_append hprefix tailTrace_4130188
  have hstable : (prefixWord ++ tailWord_4130188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130188).length < 2 ^ (prefixWord ++ tailWord_4130188).sum := by decide
  have hdescent : baseEnd_4130188 < baseStart_4130188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130208 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4130208 : Nat := 118140960795 + 4130208 * 2 ^ 59
def prefixEnd_4130208 : Nat := 4983230072969 + 3 ^ 40 * 4130208 * 2
def baseEnd_4130208 : Nat := 2120781907045081775905525

theorem tailTrace_4130208 : CollatzResearch.WordTrace tailWord_4130208 prefixEnd_4130208 2120781907045081775905525 := by
  unfold tailWord_4130208
  simp only [CollatzResearch.WordTrace]
  refine ⟨75320530710484637106535639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100427374280646182808714185 75320530710484637106535639)
  ·
    refine ⟨112980796065726955659803459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75320530710484637106535639 112980796065726955659803459)
    ·
      refine ⟨169471194098590433489705189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112980796065726955659803459 169471194098590433489705189)
      ·
        refine ⟨31775848893485706279319723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169471194098590433489705189 31775848893485706279319723)
        ·
          refine ⟨47663773340228559418979585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31775848893485706279319723 47663773340228559418979585)
          ·
            refine ⟨35747830005171419564234689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47663773340228559418979585 35747830005171419564234689)
            ·
              refine ⟨26810872503878564673176017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35747830005171419564234689 26810872503878564673176017)
              ·
                refine ⟨20108154377908923504882013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810872503878564673176017 20108154377908923504882013)
                ·
                  refine ⟨7540557891715846314330755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20108154377908923504882013 7540557891715846314330755)
                  ·
                    refine ⟨11310836837573769471496133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540557891715846314330755 11310836837573769471496133)
                    ·
                      refine ⟨2120781907045081775905525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11310836837573769471496133 2120781907045081775905525)
                      ·
                        rfl

theorem cell23_4130208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4130208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130208 prefixEnd_4130208 := by exact prefixLift 4130208
  have htrace : WordTrace (prefixWord ++ tailWord_4130208) baseStart_4130208 baseEnd_4130208 := by
    simpa [prefixWord, tailWord_4130208, baseEnd_4130208] using wordTrace_append hprefix tailTrace_4130208
  have hstable : (prefixWord ++ tailWord_4130208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130208).length < 2 ^ (prefixWord ++ tailWord_4130208).sum := by decide
  have hdescent : baseEnd_4130208 < baseStart_4130208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130231 : List Nat := [1, 1, 3, 1, 3, 2, 1, 11]
def baseStart_4130231 : Nat := 118140960795 + 4130231 * 2 ^ 59
def prefixEnd_4130231 : Nat := 4983230072969 + 3 ^ 40 * 4130231 * 2
def baseEnd_4130231 : Nat := 78547915448153155033997

theorem tailTrace_4130231 : CollatzResearch.WordTrace tailWord_4130231 prefixEnd_4130231 78547915448153155033997 := by
  unfold tailWord_4130231
  simp only [CollatzResearch.WordTrace]
  refine ⟨150641900299885949141158547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100427933533257299427439031 150641900299885949141158547)
  ·
    refine ⟨225962850449828923711737821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150641900299885949141158547 225962850449828923711737821)
    ·
      refine ⟨84736068918685846391901683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225962850449828923711737821 84736068918685846391901683)
      ·
        refine ⟨127104103378028769587852525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84736068918685846391901683 127104103378028769587852525)
        ·
          refine ⟨47664038766760788595444697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127104103378028769587852525 47664038766760788595444697)
          ·
            refine ⟨35748029075070591446583523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47664038766760788595444697 35748029075070591446583523)
            ·
              refine ⟨53622043612605887169875285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35748029075070591446583523 53622043612605887169875285)
              ·
                refine ⟨78547915448153155033997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53622043612605887169875285 78547915448153155033997)
                ·
                  rfl

theorem cell23_4130231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 11].length) (baseStart_4130231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130231 prefixEnd_4130231 := by exact prefixLift 4130231
  have htrace : WordTrace (prefixWord ++ tailWord_4130231) baseStart_4130231 baseEnd_4130231 := by
    simpa [prefixWord, tailWord_4130231, baseEnd_4130231] using wordTrace_append hprefix tailTrace_4130231
  have hstable : (prefixWord ++ tailWord_4130231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130231).length < 2 ^ (prefixWord ++ tailWord_4130231).sum := by decide
  have hdescent : baseEnd_4130231 < baseStart_4130231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130252 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_4130252 : Nat := 118140960795 + 4130252 * 2 ^ 59
def prefixEnd_4130252 : Nat := 4983230072969 + 3 ^ 40 * 4130252 * 2
def baseEnd_4130252 : Nat := 706934833397959867918441

theorem tailTrace_4130252 : CollatzResearch.WordTrace tailWord_4130252 prefixEnd_4130252 706934833397959867918441 := by
  unfold tailWord_4130252
  simp only [CollatzResearch.WordTrace]
  refine ⟨75321333116404934863836505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100428444155206579818448673 75321333116404934863836505)
  ·
    refine ⟨56490999837303701147877379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75321333116404934863836505 56490999837303701147877379)
    ·
      refine ⟨84736499755955551721816069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56490999837303701147877379 84736499755955551721816069)
      ·
        refine ⟨15888093704241665947840513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84736499755955551721816069 15888093704241665947840513)
        ·
          refine ⟨11916070278181249460880385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15888093704241665947840513 11916070278181249460880385)
          ·
            refine ⟨8937052708635937095660289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916070278181249460880385 8937052708635937095660289)
            ·
              refine ⟨6702789531476952821745217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937052708635937095660289 6702789531476952821745217)
              ·
                refine ⟨5027092148607714616308913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702789531476952821745217 5027092148607714616308913)
                ·
                  refine ⟨3770319111455785962231685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027092148607714616308913 3770319111455785962231685)
                  ·
                    refine ⟨706934833397959867918441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770319111455785962231685 706934833397959867918441)
                    ·
                      rfl

theorem cell23_4130252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_4130252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130252 prefixEnd_4130252 := by exact prefixLift 4130252
  have htrace : WordTrace (prefixWord ++ tailWord_4130252) baseStart_4130252 baseEnd_4130252 := by
    simpa [prefixWord, tailWord_4130252, baseEnd_4130252] using wordTrace_append hprefix tailTrace_4130252
  have hstable : (prefixWord ++ tailWord_4130252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130252).length < 2 ^ (prefixWord ++ tailWord_4130252).sum := by decide
  have hdescent : baseEnd_4130252 < baseStart_4130252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130262 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4130262 : Nat := 118140960795 + 4130262 * 2 ^ 59
def prefixEnd_4130262 : Nat := 4983230072969 + 3 ^ 40 * 4130262 * 2
def baseEnd_4130262 : Nat := 2120809635000424564630277

theorem tailTrace_4130262 : CollatzResearch.WordTrace tailWord_4130262 prefixEnd_4130262 2120809635000424564630277 := by
  unfold tailWord_4130262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415189435173352589721065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100428687308515760957024693 9415189435173352589721065)
  ·
    refine ⟨7061392076380014442290799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9415189435173352589721065 7061392076380014442290799)
    ·
      refine ⟨10592088114570021663436199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061392076380014442290799 10592088114570021663436199)
      ·
        refine ⟨15888132171855032495154299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592088114570021663436199 15888132171855032495154299)
        ·
          refine ⟨23832198257782548742731449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888132171855032495154299 23832198257782548742731449)
          ·
            refine ⟨17874148693336911557048587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23832198257782548742731449 17874148693336911557048587)
            ·
              refine ⟨26811223040005367335572881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874148693336911557048587 26811223040005367335572881)
              ·
                refine ⟨20108417280004025501679661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26811223040005367335572881 20108417280004025501679661)
                ·
                  refine ⟨7540656480001509563129873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20108417280004025501679661 7540656480001509563129873)
                  ·
                    refine ⟨5655492360001132172347405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7540656480001509563129873 5655492360001132172347405)
                    ·
                      refine ⟨2120809635000424564630277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5655492360001132172347405 2120809635000424564630277)
                      ·
                        rfl

theorem cell23_4130262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4130262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130262 prefixEnd_4130262 := by exact prefixLift 4130262
  have htrace : WordTrace (prefixWord ++ tailWord_4130262) baseStart_4130262 baseEnd_4130262 := by
    simpa [prefixWord, tailWord_4130262, baseEnd_4130262] using wordTrace_append hprefix tailTrace_4130262
  have hstable : (prefixWord ++ tailWord_4130262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130262).length < 2 ^ (prefixWord ++ tailWord_4130262).sum := by decide
  have hdescent : baseEnd_4130262 < baseStart_4130262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130275 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4130275 : Nat := 118140960795 + 4130275 * 2 ^ 59
def prefixEnd_4130275 : Nat := 4983230072969 + 3 ^ 40 * 4130275 * 2
def baseEnd_4130275 : Nat := 2120816310248933013767717

theorem tailTrace_4130275 : CollatzResearch.WordTrace tailWord_4130275 prefixEnd_4130275 2120816310248933013767717 := by
  unfold tailWord_4130275
  simp only [CollatzResearch.WordTrace]
  refine ⟨150643505111726544655760279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100429003407817696437173519 150643505111726544655760279)
  ·
    refine ⟨225965257667589816983640419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150643505111726544655760279 225965257667589816983640419)
    ·
      refine ⟨338947886501384725475460629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225965257667589816983640419 338947886501384725475460629)
      ·
        refine ⟨15888182179752409006662217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338947886501384725475460629 15888182179752409006662217)
        ·
          refine ⟨11916136634814306754996663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15888182179752409006662217 11916136634814306754996663)
          ·
            refine ⟨17874204952221460132494995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11916136634814306754996663 17874204952221460132494995)
            ·
              refine ⟨26811307428332190198742493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874204952221460132494995 26811307428332190198742493)
              ·
                refine ⟨10054240285624571324528435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26811307428332190198742493 10054240285624571324528435)
                ·
                  refine ⟨15081360428436856986792653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054240285624571324528435 15081360428436856986792653)
                  ·
                    refine ⟨5655510160663821370047245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15081360428436856986792653 5655510160663821370047245)
                    ·
                      refine ⟨2120816310248933013767717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5655510160663821370047245 2120816310248933013767717)
                      ·
                        rfl

theorem cell23_4130275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4130275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130275 prefixEnd_4130275 := by exact prefixLift 4130275
  have htrace : WordTrace (prefixWord ++ tailWord_4130275) baseStart_4130275 baseEnd_4130275 := by
    simpa [prefixWord, tailWord_4130275, baseEnd_4130275] using wordTrace_append hprefix tailTrace_4130275
  have hstable : (prefixWord ++ tailWord_4130275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130275).length < 2 ^ (prefixWord ++ tailWord_4130275).sum := by decide
  have hdescent : baseEnd_4130275 < baseStart_4130275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130293 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4130293 : Nat := 118140960795 + 4130293 * 2 ^ 59
def prefixEnd_4130293 : Nat := 4983230072969 + 3 ^ 40 * 4130293 * 2
def baseEnd_4130293 : Nat := 2120825552900713943342635

theorem tailTrace_4130293 : CollatzResearch.WordTrace tailWord_4130293 prefixEnd_4130293 2120825552900713943342635 := by
  unfold tailWord_4130293
  simp only [CollatzResearch.WordTrace]
  refine ⟨150644161625661333729915533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100429441083774222486610355 150644161625661333729915533)
  ·
    refine ⟨56491560609623000148718325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150644161625661333729915533 56491560609623000148718325)
    ·
      refine ⟨5296083807152156263942343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56491560609623000148718325 5296083807152156263942343)
      ·
        refine ⟨7944125710728234395913515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296083807152156263942343 7944125710728234395913515)
        ·
          refine ⟨11916188566092351593870273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944125710728234395913515 11916188566092351593870273)
          ·
            refine ⟨8937141424569263695402705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916188566092351593870273 8937141424569263695402705)
            ·
              refine ⟨6702856068426947771552029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937141424569263695402705 6702856068426947771552029)
              ·
                refine ⟨2513571025660105414332011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702856068426947771552029 2513571025660105414332011)
                ·
                  refine ⟨3770356538490158121498017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513571025660105414332011 3770356538490158121498017)
                  ·
                    refine ⟨2827767403867618591123513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770356538490158121498017 2827767403867618591123513)
                    ·
                      refine ⟨2120825552900713943342635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827767403867618591123513 2120825552900713943342635)
                      ·
                        rfl

theorem cell23_4130293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4130293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130293 prefixEnd_4130293 := by exact prefixLift 4130293
  have htrace : WordTrace (prefixWord ++ tailWord_4130293) baseStart_4130293 baseEnd_4130293 := by
    simpa [prefixWord, tailWord_4130293, baseEnd_4130293] using wordTrace_append hprefix tailTrace_4130293
  have hstable : (prefixWord ++ tailWord_4130293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130293).length < 2 ^ (prefixWord ++ tailWord_4130293).sum := by decide
  have hdescent : baseEnd_4130293 < baseStart_4130293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130310 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4130310 : Nat := 118140960795 + 4130310 * 2 ^ 59
def prefixEnd_4130310 : Nat := 4983230072969 + 3 ^ 40 * 4130310 * 2
def baseEnd_4130310 : Nat := 2120834282071840376830057

theorem tailTrace_4130310 : CollatzResearch.WordTrace tailWord_4130310 prefixEnd_4130310 2120834282071840376830057 := by
  unfold tailWord_4130310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707649427081242051040137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100429854444399830422189589 4707649427081242051040137)
  ·
    refine ⟨3530737070310931538280103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4707649427081242051040137 3530737070310931538280103)
    ·
      refine ⟨5296105605466397307420155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530737070310931538280103 5296105605466397307420155)
      ·
        refine ⟨7944158408199595961130233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296105605466397307420155 7944158408199595961130233)
        ·
          refine ⟨5958118806149696970847675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7944158408199595961130233 5958118806149696970847675)
          ·
            refine ⟨8937178209224545456271513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958118806149696970847675 8937178209224545456271513)
            ·
              refine ⟨6702883656918409092203635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937178209224545456271513 6702883656918409092203635)
              ·
                refine ⟨10054325485377613638305453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702883656918409092203635 10054325485377613638305453)
                ·
                  refine ⟨3770372057016605114364545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10054325485377613638305453 3770372057016605114364545)
                  ·
                    refine ⟨2827779042762453835773409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770372057016605114364545 2827779042762453835773409)
                    ·
                      refine ⟨2120834282071840376830057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2827779042762453835773409 2120834282071840376830057)
                      ·
                        rfl

theorem cell23_4130310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4130310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130310 prefixEnd_4130310 := by exact prefixLift 4130310
  have htrace : WordTrace (prefixWord ++ tailWord_4130310) baseStart_4130310 baseEnd_4130310 := by
    simpa [prefixWord, tailWord_4130310, baseEnd_4130310] using wordTrace_append hprefix tailTrace_4130310
  have hstable : (prefixWord ++ tailWord_4130310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130310).length < 2 ^ (prefixWord ++ tailWord_4130310).sum := by decide
  have hdescent : baseEnd_4130310 < baseStart_4130310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130522 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_4130522 : Nat := 118140960795 + 4130522 * 2 ^ 59
def prefixEnd_4130522 : Nat := 4983230072969 + 3 ^ 40 * 4130522 * 2
def baseEnd_4130522 : Nat := 706981046656864515793027

theorem tailTrace_4130522 : CollatzResearch.WordTrace tailWord_4130522 prefixEnd_4130522 706981046656864515793027 := by
  unfold tailWord_4130522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37663128485457926460000455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100435009294554470560001213 37663128485457926460000455)
  ·
    refine ⟨56494692728186889690000683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37663128485457926460000455 56494692728186889690000683)
    ·
      refine ⟨84742039092280334535001025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56494692728186889690000683 84742039092280334535001025)
      ·
        refine ⟨63556529319210250901250769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84742039092280334535001025 63556529319210250901250769)
        ·
          refine ⟨47667396989407688175938077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63556529319210250901250769 47667396989407688175938077)
          ·
            refine ⟨17875273871027883065976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47667396989407688175938077 17875273871027883065976779)
            ·
              refine ⟨26812910806541824598965169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17875273871027883065976779 26812910806541824598965169)
              ·
                refine ⟨20109683104906368449223877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26812910806541824598965169 20109683104906368449223877)
                ·
                  refine ⟨3770565582169944084229477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20109683104906368449223877 3770565582169944084229477)
                  ·
                    refine ⟨706981046656864515793027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770565582169944084229477 706981046656864515793027)
                    ·
                      rfl

theorem cell23_4130522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_4130522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130522 prefixEnd_4130522 := by exact prefixLift 4130522
  have htrace : WordTrace (prefixWord ++ tailWord_4130522) baseStart_4130522 baseEnd_4130522 := by
    simpa [prefixWord, tailWord_4130522, baseEnd_4130522] using wordTrace_append hprefix tailTrace_4130522
  have hstable : (prefixWord ++ tailWord_4130522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130522).length < 2 ^ (prefixWord ++ tailWord_4130522).sum := by decide
  have hdescent : baseEnd_4130522 < baseStart_4130522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130532 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_4130532 : Nat := 118140960795 + 4130532 * 2 ^ 59
def prefixEnd_4130532 : Nat := 4983230072969 + 3 ^ 40 * 4130532 * 2
def baseEnd_4130532 : Nat := 2120948274777138508254035

theorem tailTrace_4130532 : CollatzResearch.WordTrace tailWord_4130532 prefixEnd_4130532 2120948274777138508254035 := by
  unfold tailWord_4130532
  simp only [CollatzResearch.WordTrace]
  refine ⟨75326439335897738773932925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100435252447863651698577233 75326439335897738773932925)
  ·
    refine ⟨28247414750961652040224847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75326439335897738773932925 28247414750961652040224847)
    ·
      refine ⟨42371122126442478060337271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28247414750961652040224847 42371122126442478060337271)
      ·
        refine ⟨63556683189663717090505907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42371122126442478060337271 63556683189663717090505907)
        ·
          refine ⟨95335024784495575635758861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63556683189663717090505907 95335024784495575635758861)
          ·
            refine ⟨35750634294185840863409573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95335024784495575635758861 35750634294185840863409573)
            ·
              refine ⟨6703243930159845161889295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35750634294185840863409573 6703243930159845161889295)
              ·
                refine ⟨10054865895239767742833943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703243930159845161889295 10054865895239767742833943)
                ·
                  refine ⟨15082298842859651614250915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054865895239767742833943 15082298842859651614250915)
                  ·
                    refine ⟨22623448264289477421376373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15082298842859651614250915 22623448264289477421376373)
                    ·
                      refine ⟨2120948274777138508254035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22623448264289477421376373 2120948274777138508254035)
                      ·
                        rfl

theorem cell23_4130532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_4130532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130532 prefixEnd_4130532 := by exact prefixLift 4130532
  have htrace : WordTrace (prefixWord ++ tailWord_4130532) baseStart_4130532 baseEnd_4130532 := by
    simpa [prefixWord, tailWord_4130532, baseEnd_4130532] using wordTrace_append hprefix tailTrace_4130532
  have hstable : (prefixWord ++ tailWord_4130532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130532).length < 2 ^ (prefixWord ++ tailWord_4130532).sum := by decide
  have hdescent : baseEnd_4130532 < baseStart_4130532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130575 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_4130575 : Nat := 118140960795 + 4130575 * 2 ^ 59
def prefixEnd_4130575 : Nat := 4983230072969 + 3 ^ 40 * 4130575 * 2
def baseEnd_4130575 : Nat := 2120970354445281840016337

theorem tailTrace_4130575 : CollatzResearch.WordTrace tailWord_4130575 prefixEnd_4130575 2120970354445281840016337 := by
  unfold tailWord_4130575
  simp only [CollatzResearch.WordTrace]
  refine ⟨150654447010639695891681179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100436298007093130594454119 150654447010639695891681179)
  ·
    refine ⟨225981670515959543837521769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150654447010639695891681179 225981670515959543837521769)
    ·
      refine ⟨169486252886969657878141327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225981670515959543837521769 169486252886969657878141327)
      ·
        refine ⟨254229379330454486817211991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169486252886969657878141327 254229379330454486817211991)
        ·
          refine ⟨381344068995681730225817987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254229379330454486817211991 381344068995681730225817987)
          ·
            refine ⟨572016103493522595338726981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381344068995681730225817987 572016103493522595338726981)
            ·
              refine ⟨107253019405035486626011309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572016103493522595338726981 107253019405035486626011309)
              ·
                refine ⟨40219882276888307484754241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107253019405035486626011309 40219882276888307484754241)
                ·
                  refine ⟨30164911707666230613565681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40219882276888307484754241 30164911707666230613565681)
                  ·
                    refine ⟨22623683780749672960174261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30164911707666230613565681 22623683780749672960174261)
                    ·
                      refine ⟨2120970354445281840016337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22623683780749672960174261 2120970354445281840016337)
                      ·
                        rfl

theorem cell23_4130575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_4130575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130575 prefixEnd_4130575 := by exact prefixLift 4130575
  have htrace : WordTrace (prefixWord ++ tailWord_4130575) baseStart_4130575 baseEnd_4130575 := by
    simpa [prefixWord, tailWord_4130575, baseEnd_4130575] using wordTrace_append hprefix tailTrace_4130575
  have hstable : (prefixWord ++ tailWord_4130575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130575).length < 2 ^ (prefixWord ++ tailWord_4130575).sum := by decide
  have hdescent : baseEnd_4130575 < baseStart_4130575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130590 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4130590 : Nat := 118140960795 + 4130590 * 2 ^ 59
def prefixEnd_4130590 : Nat := 4983230072969 + 3 ^ 40 * 4130590 * 2
def baseEnd_4130590 : Nat := 706992685551699760442923

theorem tailTrace_4130590 : CollatzResearch.WordTrace tailWord_4130590 prefixEnd_4130590 706992685551699760442923 := by
  unfold tailWord_4130590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831874263198169181684653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100436662737056902302318149 18831874263198169181684653)
  ·
    refine ⟨7061952848699313443131745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18831874263198169181684653 7061952848699313443131745)
    ·
      refine ⟨5296464636524485082348809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7061952848699313443131745 5296464636524485082348809)
      ·
        refine ⟨3972348477393363811761607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5296464636524485082348809 3972348477393363811761607)
        ·
          refine ⟨5958522716090045717642411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972348477393363811761607 5958522716090045717642411)
          ·
            refine ⟨8937784074135068576463617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958522716090045717642411 8937784074135068576463617)
            ·
              refine ⟨6703338055601301432347713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937784074135068576463617 6703338055601301432347713)
              ·
                refine ⟨5027503541700976074260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703338055601301432347713 5027503541700976074260785)
                ·
                  refine ⟨3770627656275732055695589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027503541700976074260785 3770627656275732055695589)
                  ·
                    refine ⟨706992685551699760442923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770627656275732055695589 706992685551699760442923)
                    ·
                      rfl

theorem cell23_4130590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4130590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130590 prefixEnd_4130590 := by exact prefixLift 4130590
  have htrace : WordTrace (prefixWord ++ tailWord_4130590) baseStart_4130590 baseEnd_4130590 := by
    simpa [prefixWord, tailWord_4130590, baseEnd_4130590] using wordTrace_append hprefix tailTrace_4130590
  have hstable : (prefixWord ++ tailWord_4130590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130590).length < 2 ^ (prefixWord ++ tailWord_4130590).sum := by decide
  have hdescent : baseEnd_4130590 < baseStart_4130590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130596 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_4130596 : Nat := 118140960795 + 4130596 * 2 ^ 59
def prefixEnd_4130596 : Nat := 4983230072969 + 3 ^ 40 * 4130596 * 2
def baseEnd_4130596 : Nat := 2120981137539026257853741

theorem tailTrace_4130596 : CollatzResearch.WordTrace tailWord_4130596 prefixEnd_4130596 2120981137539026257853741 := by
  unfold tailWord_4130596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75327606471781808239097821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100436808629042410985463761 75327606471781808239097821)
  ·
    refine ⟨28247852426918178089661683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75327606471781808239097821 28247852426918178089661683)
    ·
      refine ⟨42371778640377267134492525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28247852426918178089661683 42371778640377267134492525)
      ·
        refine ⟨15889416990141475175434697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42371778640377267134492525 15889416990141475175434697)
        ·
          refine ⟨11917062742606106381576023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15889416990141475175434697 11917062742606106381576023)
          ·
            refine ⟨17875594113909159572364035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917062742606106381576023 17875594113909159572364035)
            ·
              refine ⟨26813391170863739358546053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17875594113909159572364035 26813391170863739358546053)
              ·
                refine ⟨5027510844536951129727385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26813391170863739358546053 5027510844536951129727385)
                ·
                  refine ⟨3770633133402713347295539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027510844536951129727385 3770633133402713347295539)
                  ·
                    refine ⟨5655949700104070020943309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3770633133402713347295539 5655949700104070020943309)
                    ·
                      refine ⟨2120981137539026257853741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5655949700104070020943309 2120981137539026257853741)
                      ·
                        rfl

theorem cell23_4130596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_4130596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130596 prefixEnd_4130596 := by exact prefixLift 4130596
  have htrace : WordTrace (prefixWord ++ tailWord_4130596) baseStart_4130596 baseEnd_4130596 := by
    simpa [prefixWord, tailWord_4130596, baseEnd_4130596] using wordTrace_append hprefix tailTrace_4130596
  have hstable : (prefixWord ++ tailWord_4130596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130596).length < 2 ^ (prefixWord ++ tailWord_4130596).sum := by decide
  have hdescent : baseEnd_4130596 < baseStart_4130596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130659 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 7]
def baseStart_4130659 : Nat := 118140960795 + 4130659 * 2 ^ 59
def prefixEnd_4130659 : Nat := 4983230072969 + 3 ^ 40 * 4130659 * 2
def baseEnd_4130659 : Nat := 235668165202251056818439

theorem tailTrace_4130659 : CollatzResearch.WordTrace tailWord_4130659 prefixEnd_4130659 235668165202251056818439 := by
  unfold tailWord_4130659
  simp only [CollatzResearch.WordTrace]
  refine ⟨150657510742335378237739031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100438340494890252158492687 150657510742335378237739031)
  ·
    refine ⟨225986266113503067356608547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150657510742335378237739031 225986266113503067356608547)
    ·
      refine ⟨338979399170254601034912821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225986266113503067356608547 338979399170254601034912821)
      ·
        refine ⟨31779318672211368847023077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338979399170254601034912821 31779318672211368847023077)
        ·
          refine ⟨5958622251039631658816827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31779318672211368847023077 5958622251039631658816827)
          ·
            refine ⟨8937933376559447488225241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958622251039631658816827 8937933376559447488225241)
            ·
              refine ⟨6703450032419585616168931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937933376559447488225241 6703450032419585616168931)
              ·
                refine ⟨10055175048629378424253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703450032419585616168931 10055175048629378424253397)
                ·
                  refine ⟨235668165202251056818439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10055175048629378424253397 235668165202251056818439)
                  ·
                    rfl

theorem cell23_4130659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 7].length) (baseStart_4130659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130659 prefixEnd_4130659 := by exact prefixLift 4130659
  have htrace : WordTrace (prefixWord ++ tailWord_4130659) baseStart_4130659 baseEnd_4130659 := by
    simpa [prefixWord, tailWord_4130659, baseEnd_4130659] using wordTrace_append hprefix tailTrace_4130659
  have hstable : (prefixWord ++ tailWord_4130659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130659).length < 2 ^ (prefixWord ++ tailWord_4130659).sum := by decide
  have hdescent : baseEnd_4130659 < baseStart_4130659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130669 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4130669 : Nat := 118140960795 + 4130669 * 2 ^ 59
def prefixEnd_4130669 : Nat := 4983230072969 + 3 ^ 40 * 4130669 * 2
def baseEnd_4130669 : Nat := 2121018621626804472240905

theorem tailTrace_4130669 : CollatzResearch.WordTrace tailWord_4130669 prefixEnd_4130669 2121018621626804472240905 := by
  unfold tailWord_4130669
  simp only [CollatzResearch.WordTrace]
  refine ⟨150657875472299149945603061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100438583648199433297068707 150657875472299149945603061)
  ·
    refine ⟨14124175825528045307400287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150657875472299149945603061 14124175825528045307400287)
    ·
      refine ⟨21186263738292067961100431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124175825528045307400287 21186263738292067961100431)
      ·
        refine ⟨31779395607438101941650647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21186263738292067961100431 31779395607438101941650647)
        ·
          refine ⟨47669093411157152912475971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31779395607438101941650647 47669093411157152912475971)
          ·
            refine ⟨71503640116735729368713957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47669093411157152912475971 71503640116735729368713957)
            ·
              refine ⟨13406932521887949256633867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71503640116735729368713957 13406932521887949256633867)
              ·
                refine ⟨20110398782831923884950801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13406932521887949256633867 20110398782831923884950801)
                ·
                  refine ⟨15082799087123942913713101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20110398782831923884950801 15082799087123942913713101)
                  ·
                    refine ⟨5656049657671478592642413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15082799087123942913713101 5656049657671478592642413)
                    ·
                      refine ⟨2121018621626804472240905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656049657671478592642413 2121018621626804472240905)
                      ·
                        rfl

theorem cell23_4130669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4130669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130669 prefixEnd_4130669 := by exact prefixLift 4130669
  have htrace : WordTrace (prefixWord ++ tailWord_4130669) baseStart_4130669 baseEnd_4130669 := by
    simpa [prefixWord, tailWord_4130669, baseEnd_4130669] using wordTrace_append hprefix tailTrace_4130669
  have hstable : (prefixWord ++ tailWord_4130669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130669).length < 2 ^ (prefixWord ++ tailWord_4130669).sum := by decide
  have hdescent : baseEnd_4130669 < baseStart_4130669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130706 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4130706 : Nat := 118140960795 + 4130706 * 2 ^ 59
def prefixEnd_4130706 : Nat := 4983230072969 + 3 ^ 40 * 4130706 * 2
def baseEnd_4130706 : Nat := 707012540137006942492745

theorem tailTrace_4130706 : CollatzResearch.WordTrace tailWord_4130706 prefixEnd_4130706 707012540137006942492745 := by
  unfold tailWord_4130706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37664806243291276316174993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100439483315443403509799981 37664806243291276316174993)
  ·
    refine ⟨28248604682468457237131245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37664806243291276316174993 28248604682468457237131245)
    ·
      refine ⟨10593226755925671463924217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28248604682468457237131245 10593226755925671463924217)
      ·
        refine ⟨7944920066944253597943163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10593226755925671463924217 7944920066944253597943163)
        ·
          refine ⟨11917380100416380396914745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944920066944253597943163 11917380100416380396914745)
          ·
            refine ⟨8938035075312285297686059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11917380100416380396914745 8938035075312285297686059)
            ·
              refine ⟨13407052612968427946529089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938035075312285297686059 13407052612968427946529089)
              ·
                refine ⟨10055289459726320959896817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407052612968427946529089 10055289459726320959896817)
                ·
                  refine ⟨7541467094794740719922613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055289459726320959896817 7541467094794740719922613)
                  ·
                    refine ⟨707012540137006942492745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7541467094794740719922613 707012540137006942492745)
                    ·
                      rfl

theorem cell23_4130706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4130706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130706 prefixEnd_4130706 := by exact prefixLift 4130706
  have htrace : WordTrace (prefixWord ++ tailWord_4130706) baseStart_4130706 baseEnd_4130706 := by
    simpa [prefixWord, tailWord_4130706, baseEnd_4130706] using wordTrace_append hprefix tailTrace_4130706
  have hstable : (prefixWord ++ tailWord_4130706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130706).length < 2 ^ (prefixWord ++ tailWord_4130706).sum := by decide
  have hdescent : baseEnd_4130706 < baseStart_4130706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130709 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4130709 : Nat := 118140960795 + 4130709 * 2 ^ 59
def prefixEnd_4130709 : Nat := 4983230072969 + 3 ^ 40 * 4130709 * 2
def baseEnd_4130709 : Nat := 2121039160852984315740721

theorem tailTrace_4130709 : CollatzResearch.WordTrace tailWord_4130709 prefixEnd_4130709 2121039160852984315740721 := by
  unfold tailWord_4130709
  simp only [CollatzResearch.WordTrace]
  refine ⟨150659334392154236777059181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100439556261436157851372787 150659334392154236777059181)
  ·
    refine ⟨56497250397057838791397193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150659334392154236777059181 56497250397057838791397193)
    ·
      refine ⟨42372937797793379093547895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56497250397057838791397193 42372937797793379093547895)
      ·
        refine ⟨63559406696690068640321843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42372937797793379093547895 63559406696690068640321843)
        ·
          refine ⟨95339110045035102960482765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63559406696690068640321843 95339110045035102960482765)
          ·
            refine ⟨35752166266888163610181037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95339110045035102960482765 35752166266888163610181037)
            ·
              refine ⟨13407062350083061353817889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35752166266888163610181037 13407062350083061353817889)
              ·
                refine ⟨10055296762562296015363417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407062350083061353817889 10055296762562296015363417)
                ·
                  refine ⟨7541472571921722011522563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055296762562296015363417 7541472571921722011522563)
                  ·
                    refine ⟨11312208857882583017283845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7541472571921722011522563 11312208857882583017283845)
                    ·
                      refine ⟨2121039160852984315740721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11312208857882583017283845 2121039160852984315740721)
                      ·
                        rfl

theorem cell23_4130709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4130709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130709 prefixEnd_4130709 := by exact prefixLift 4130709
  have htrace : WordTrace (prefixWord ++ tailWord_4130709) baseStart_4130709 baseEnd_4130709 := by
    simpa [prefixWord, tailWord_4130709, baseEnd_4130709] using wordTrace_append hprefix tailTrace_4130709
  have hstable : (prefixWord ++ tailWord_4130709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130709).length < 2 ^ (prefixWord ++ tailWord_4130709).sum := by decide
  have hdescent : baseEnd_4130709 < baseStart_4130709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130710 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4130710 : Nat := 118140960795 + 4130710 * 2 ^ 59
def prefixEnd_4130710 : Nat := 4983230072969 + 3 ^ 40 * 4130710 * 2
def baseEnd_4130710 : Nat := 235671074925959867980913

theorem tailTrace_4130710 : CollatzResearch.WordTrace tailWord_4130710 prefixEnd_4130710 235671074925959867980913 := by
  unfold tailWord_4130710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416210679071913371740349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100439580576767075965230389 9416210679071913371740349)
  ·
    refine ⟨3531079004651967514402631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9416210679071913371740349 3531079004651967514402631)
    ·
      refine ⟨5296618506977951271603947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531079004651967514402631 5296618506977951271603947)
      ·
        refine ⟨7944927760466926907405921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296618506977951271603947 7944927760466926907405921)
        ·
          refine ⟨5958695820350195180554441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7944927760466926907405921 5958695820350195180554441)
          ·
            refine ⟨4469021865262646385415831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5958695820350195180554441 4469021865262646385415831)
            ·
              refine ⟨6703532797893969578123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469021865262646385415831 6703532797893969578123747)
              ·
                refine ⟨10055299196840954367185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703532797893969578123747 10055299196840954367185621)
                ·
                  refine ⟨235671074925959867980913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10055299196840954367185621 235671074925959867980913)
                  ·
                    rfl

theorem cell23_4130710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4130710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130710 prefixEnd_4130710 := by exact prefixLift 4130710
  have htrace : WordTrace (prefixWord ++ tailWord_4130710) baseStart_4130710 baseEnd_4130710 := by
    simpa [prefixWord, tailWord_4130710, baseEnd_4130710] using wordTrace_append hprefix tailTrace_4130710
  have hstable : (prefixWord ++ tailWord_4130710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130710).length < 2 ^ (prefixWord ++ tailWord_4130710).sum := by decide
  have hdescent : baseEnd_4130710 < baseStart_4130710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130770 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_4130770 : Nat := 118140960795 + 4130770 * 2 ^ 59
def prefixEnd_4130770 : Nat := 4983230072969 + 3 ^ 40 * 4130770 * 2
def baseEnd_4130770 : Nat := 707023494390969525692647

theorem tailTrace_4130770 : CollatzResearch.WordTrace tailWord_4130770 prefixEnd_4130770 707023494390969525692647 := by
  unfold tailWord_4130770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37665389811233311048757441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100441039496622162796686509 37665389811233311048757441)
  ·
    refine ⟨28249042358424983286568081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37665389811233311048757441 28249042358424983286568081)
    ·
      refine ⟨21186781768818737464926061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28249042358424983286568081 21186781768818737464926061)
      ·
        refine ⟨7945043163307026549347273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21186781768818737464926061 7945043163307026549347273)
        ·
          refine ⟨5958782372480269912010455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7945043163307026549347273 5958782372480269912010455)
          ·
            refine ⟨8938173558720404868015683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958782372480269912010455 8938173558720404868015683)
            ·
              refine ⟨13407260338080607302023525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938173558720404868015683 13407260338080607302023525)
              ·
                refine ⟨2513861313390113869129411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13407260338080607302023525 2513861313390113869129411)
                ·
                  refine ⟨3770791970085170803694117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513861313390113869129411 3770791970085170803694117)
                  ·
                    refine ⟨707023494390969525692647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770791970085170803694117 707023494390969525692647)
                    ·
                      rfl

theorem cell23_4130770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_4130770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130770 prefixEnd_4130770 := by exact prefixLift 4130770
  have htrace : WordTrace (prefixWord ++ tailWord_4130770) baseStart_4130770 baseEnd_4130770 := by
    simpa [prefixWord, tailWord_4130770, baseEnd_4130770] using wordTrace_append hprefix tailTrace_4130770
  have hstable : (prefixWord ++ tailWord_4130770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130770).length < 2 ^ (prefixWord ++ tailWord_4130770).sum := by decide
  have hdescent : baseEnd_4130770 < baseStart_4130770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130776 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4130776 : Nat := 118140960795 + 4130776 * 2 ^ 59
def prefixEnd_4130776 : Nat := 4983230072969 + 3 ^ 40 * 4130776 * 2
def baseEnd_4130776 : Nat := 2121073564056835553602913

theorem tailTrace_4130776 : CollatzResearch.WordTrace tailWord_4130776 prefixEnd_4130776 2121073564056835553602913 := by
  unfold tailWord_4130776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75330889041455753609874091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100441185388607671479832121 75330889041455753609874091)
  ·
    refine ⟨112996333562183630414811137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75330889041455753609874091 112996333562183630414811137)
    ·
      refine ⟨84747250171637722811108353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112996333562183630414811137 84747250171637722811108353)
      ·
        refine ⟨63560437628728292108331265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84747250171637722811108353 63560437628728292108331265)
        ·
          refine ⟨47670328221546219081248449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63560437628728292108331265 47670328221546219081248449)
          ·
            refine ⟨35752746166159664310936337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47670328221546219081248449 35752746166159664310936337)
            ·
              refine ⟨26814559624619748233202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35752746166159664310936337 26814559624619748233202253)
              ·
                refine ⟨10055459859232405587450845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26814559624619748233202253 10055459859232405587450845)
                ·
                  refine ⟨3770797447212152095294067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10055459859232405587450845 3770797447212152095294067)
                  ·
                    refine ⟨5656196170818228142941101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3770797447212152095294067 5656196170818228142941101)
                    ·
                      refine ⟨2121073564056835553602913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656196170818228142941101 2121073564056835553602913)
                      ·
                        rfl

theorem cell23_4130776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4130776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130776 prefixEnd_4130776 := by exact prefixLift 4130776
  have htrace : WordTrace (prefixWord ++ tailWord_4130776) baseStart_4130776 baseEnd_4130776 := by
    simpa [prefixWord, tailWord_4130776, baseEnd_4130776] using wordTrace_append hprefix tailTrace_4130776
  have hstable : (prefixWord ++ tailWord_4130776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130776).length < 2 ^ (prefixWord ++ tailWord_4130776).sum := by decide
  have hdescent : baseEnd_4130776 < baseStart_4130776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130797 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4130797 : Nat := 118140960795 + 4130797 * 2 ^ 59
def prefixEnd_4130797 : Nat := 4983230072969 + 3 ^ 40 * 4130797 * 2
def baseEnd_4130797 : Nat := 2121084347150579971440317

theorem tailTrace_4130797 : CollatzResearch.WordTrace tailWord_4130797 prefixEnd_4130797 2121084347150579971440317 := by
  unfold tailWord_4130797
  simp only [CollatzResearch.WordTrace]
  refine ⟨150662544015835427806262645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100441696010556951870841763 150662544015835427806262645)
  ·
    refine ⟨14124613501484571356837123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150662544015835427806262645 14124613501484571356837123)
    ·
      refine ⟨21186920252226857035255685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124613501484571356837123 21186920252226857035255685)
      ·
        refine ⟨3972547547292535694110441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21186920252226857035255685 3972547547292535694110441)
        ·
          refine ⟨2979410660469401770582831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972547547292535694110441 2979410660469401770582831)
          ·
            refine ⟨4469115990704102655874247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979410660469401770582831 4469115990704102655874247)
            ·
              refine ⟨6703673986056153983811371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469115990704102655874247 6703673986056153983811371)
              ·
                refine ⟨10055510979084230975717057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703673986056153983811371 10055510979084230975717057)
                ·
                  refine ⟨7541633234313173231787793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055510979084230975717057 7541633234313173231787793)
                  ·
                    refine ⟨5656224925734879923840845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541633234313173231787793 5656224925734879923840845)
                    ·
                      refine ⟨2121084347150579971440317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656224925734879923840845 2121084347150579971440317)
                      ·
                        rfl

theorem cell23_4130797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4130797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130797 prefixEnd_4130797 := by exact prefixLift 4130797
  have htrace : WordTrace (prefixWord ++ tailWord_4130797) baseStart_4130797 baseEnd_4130797 := by
    simpa [prefixWord, tailWord_4130797, baseEnd_4130797] using wordTrace_append hprefix tailTrace_4130797
  have hstable : (prefixWord ++ tailWord_4130797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130797).length < 2 ^ (prefixWord ++ tailWord_4130797).sum := by decide
  have hdescent : baseEnd_4130797 < baseStart_4130797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130799 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_4130799 : Nat := 118140960795 + 4130799 * 2 ^ 59
def prefixEnd_4130799 : Nat := 4983230072969 + 3 ^ 40 * 4130799 * 2
def baseEnd_4130799 : Nat := 2121085374111888963615307

theorem tailTrace_4130799 : CollatzResearch.WordTrace tailWord_4130799 prefixEnd_4130799 2121085374111888963615307 := by
  unfold tailWord_4130799
  simp only [CollatzResearch.WordTrace]
  refine ⟨150662616961828182147835451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100441744641218788098556967 150662616961828182147835451)
  ·
    refine ⟨225993925442742273221753177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150662616961828182147835451 225993925442742273221753177)
    ·
      refine ⟨169495444082056704916314883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225993925442742273221753177 169495444082056704916314883)
      ·
        refine ⟨254243166123085057374472325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169495444082056704916314883 254243166123085057374472325)
        ·
          refine ⟨47670593648078448257713561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254243166123085057374472325 47670593648078448257713561)
          ·
            refine ⟨35752945236058836193285171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47670593648078448257713561 35752945236058836193285171)
            ·
              refine ⟨53629417854088254289927757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35752945236058836193285171 53629417854088254289927757)
              ·
                refine ⟨20111031695283095358722909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53629417854088254289927757 20111031695283095358722909)
                ·
                  refine ⟨7541636885731160759521091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20111031695283095358722909 7541636885731160759521091)
                  ·
                    refine ⟨11312455328596741139281637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7541636885731160759521091 11312455328596741139281637)
                    ·
                      refine ⟨2121085374111888963615307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11312455328596741139281637 2121085374111888963615307)
                      ·
                        rfl

theorem cell23_4130799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_4130799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130799 prefixEnd_4130799 := by exact prefixLift 4130799
  have htrace : WordTrace (prefixWord ++ tailWord_4130799) baseStart_4130799 baseEnd_4130799 := by
    simpa [prefixWord, tailWord_4130799, baseEnd_4130799] using wordTrace_append hprefix tailTrace_4130799
  have hstable : (prefixWord ++ tailWord_4130799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130799).length < 2 ^ (prefixWord ++ tailWord_4130799).sum := by decide
  have hdescent : baseEnd_4130799 < baseStart_4130799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130809 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_4130809 : Nat := 118140960795 + 4130809 * 2 ^ 59
def prefixEnd_4130809 : Nat := 4983230072969 + 3 ^ 40 * 4130809 * 2
def baseEnd_4130809 : Nat := 707030169639477974830087

theorem tailTrace_4130809 : CollatzResearch.WordTrace tailWord_4130809 prefixEnd_4130809 707030169639477974830087 := by
  unfold tailWord_4130809
  simp only [CollatzResearch.WordTrace]
  refine ⟨150662981691791953855699481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100441987794527969237132987 150662981691791953855699481)
  ·
    refine ⟨112997236268843965391774611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150662981691791953855699481 112997236268843965391774611)
    ·
      refine ⟨169495854403265948087661917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112997236268843965391774611 169495854403265948087661917)
      ·
        refine ⟨63560945401224730532873219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169495854403265948087661917 63560945401224730532873219)
        ·
          refine ⟨95341418101837095799309829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63560945401224730532873219 95341418101837095799309829)
          ·
            refine ⟨17876515894094455462370593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95341418101837095799309829 17876515894094455462370593)
            ·
              refine ⟨13407386920570841596777945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17876515894094455462370593 13407386920570841596777945)
              ·
                refine ⟨10055540190428131197583459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407386920570841596777945 10055540190428131197583459)
                ·
                  refine ⟨15083310285642196796375189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055540190428131197583459 15083310285642196796375189)
                  ·
                    refine ⟨707030169639477974830087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15083310285642196796375189 707030169639477974830087)
                    ·
                      rfl

theorem cell23_4130809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_4130809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130809 prefixEnd_4130809 := by exact prefixLift 4130809
  have htrace : WordTrace (prefixWord ++ tailWord_4130809) baseStart_4130809 baseEnd_4130809 := by
    simpa [prefixWord, tailWord_4130809, baseEnd_4130809] using wordTrace_append hprefix tailTrace_4130809
  have hstable : (prefixWord ++ tailWord_4130809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130809).length < 2 ^ (prefixWord ++ tailWord_4130809).sum := by decide
  have hdescent : baseEnd_4130809 < baseStart_4130809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130853 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_4130853 : Nat := 118140960795 + 4130853 * 2 ^ 59
def prefixEnd_4130853 : Nat := 4983230072969 + 3 ^ 40 * 4130853 * 2
def baseEnd_4130853 : Nat := 2121113102067231752340059

theorem tailTrace_4130853 : CollatzResearch.WordTrace tailWord_4130853 prefixEnd_4130853 2121113102067231752340059 := by
  unfold tailWord_4130853
  simp only [CollatzResearch.WordTrace]
  refine ⟨150664586503632549370301213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100443057669088366246867475 150664586503632549370301213)
  ·
    refine ⟨56499219938862206013862955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150664586503632549370301213 56499219938862206013862955)
    ·
      refine ⟨84748829908293309020794433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56499219938862206013862955 84748829908293309020794433)
      ·
        refine ⟨63561622431219981765595825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84748829908293309020794433 63561622431219981765595825)
        ·
          refine ⟨47671216823414986324196869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63561622431219981765595825 47671216823414986324196869)
          ·
            refine ⟨8938353154390309935786913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47671216823414986324196869 8938353154390309935786913)
            ·
              refine ⟨6703764865792732451840185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938353154390309935786913 6703764865792732451840185)
              ·
                refine ⟨5027823649344549338880139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703764865792732451840185 5027823649344549338880139)
                ·
                  refine ⟨7541735474016824008320209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027823649344549338880139 7541735474016824008320209)
                  ·
                    refine ⟨5656301605512618006240157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541735474016824008320209 5656301605512618006240157)
                    ·
                      refine ⟨2121113102067231752340059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656301605512618006240157 2121113102067231752340059)
                      ·
                        rfl

theorem cell23_4130853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_4130853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130853 prefixEnd_4130853 := by exact prefixLift 4130853
  have htrace : WordTrace (prefixWord ++ tailWord_4130853) baseStart_4130853 baseEnd_4130853 := by
    simpa [prefixWord, tailWord_4130853, baseEnd_4130853] using wordTrace_append hprefix tailTrace_4130853
  have hstable : (prefixWord ++ tailWord_4130853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130853).length < 2 ^ (prefixWord ++ tailWord_4130853).sum := by decide
  have hdescent : baseEnd_4130853 < baseStart_4130853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130889 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_4130889 : Nat := 118140960795 + 4130889 * 2 ^ 59
def prefixEnd_4130889 : Nat := 4983230072969 + 3 ^ 40 * 4130889 * 2
def baseEnd_4130889 : Nat := 2121131587370793611489893

theorem tailTrace_4130889 : CollatzResearch.WordTrace tailWord_4130889 prefixEnd_4130889 2121131587370793611489893 := by
  unfold tailWord_4130889
  simp only [CollatzResearch.WordTrace]
  refine ⟨150665899531502127518611721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100443933021001418345741147 150665899531502127518611721)
  ·
    refine ⟨112999424648626595638958791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150665899531502127518611721 112999424648626595638958791)
    ·
      refine ⟨169499136972939893458438187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112999424648626595638958791 169499136972939893458438187)
      ·
        refine ⟨254248705459409840187657281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169499136972939893458438187 254248705459409840187657281)
        ·
          refine ⟨190686529094557380140742961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254248705459409840187657281 190686529094557380140742961)
          ·
            refine ⟨143014896820918035105557221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190686529094557380140742961 143014896820918035105557221)
            ·
              refine ⟨26815293153922131582291979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143014896820918035105557221 26815293153922131582291979)
              ·
                refine ⟨40222939730883197373437969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26815293153922131582291979 40222939730883197373437969)
                ·
                  refine ⟨30167204798162398030078477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40222939730883197373437969 30167204798162398030078477)
                  ·
                    refine ⟨11312701799310899261279429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30167204798162398030078477 11312701799310899261279429)
                    ·
                      refine ⟨2121131587370793611489893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11312701799310899261279429 2121131587370793611489893)
                      ·
                        rfl

theorem cell23_4130889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_4130889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130889 prefixEnd_4130889 := by exact prefixLift 4130889
  have htrace : WordTrace (prefixWord ++ tailWord_4130889) baseStart_4130889 baseEnd_4130889 := by
    simpa [prefixWord, tailWord_4130889, baseEnd_4130889] using wordTrace_append hprefix tailTrace_4130889
  have hstable : (prefixWord ++ tailWord_4130889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130889).length < 2 ^ (prefixWord ++ tailWord_4130889).sum := by decide
  have hdescent : baseEnd_4130889 < baseStart_4130889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130926 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4130926 : Nat := 118140960795 + 4130926 * 2 ^ 59
def prefixEnd_4130926 : Nat := 4983230072969 + 3 ^ 40 * 4130926 * 2
def baseEnd_4130926 : Nat := 2121150586155009966727223

theorem tailTrace_4130926 : CollatzResearch.WordTrace tailWord_4130926 prefixEnd_4130926 2121150586155009966727223 := by
  unfold tailWord_4130926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833406129046010354713579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100444832688245388558472421 18833406129046010354713579)
  ·
    refine ⟨28250109193569015532070369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833406129046010354713579 28250109193569015532070369)
    ·
      refine ⟨21187581895176761649052777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28250109193569015532070369 21187581895176761649052777)
      ·
        refine ⟨15890686421382571236789583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21187581895176761649052777 15890686421382571236789583)
        ·
          refine ⟨23836029632073856855184375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15890686421382571236789583 23836029632073856855184375)
          ·
            refine ⟨35754044448110785282776563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836029632073856855184375 35754044448110785282776563)
            ·
              refine ⟨53631066672166177924164845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35754044448110785282776563 53631066672166177924164845)
              ·
                refine ⟨20111650002062316721561817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53631066672166177924164845 20111650002062316721561817)
                ·
                  refine ⟨15083737501546737541171363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20111650002062316721561817 15083737501546737541171363)
                  ·
                    refine ⟨22625606252320106311757045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15083737501546737541171363 22625606252320106311757045)
                    ·
                      refine ⟨2121150586155009966727223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22625606252320106311757045 2121150586155009966727223)
                      ·
                        rfl

theorem cell23_4130926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4130926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130926 prefixEnd_4130926 := by exact prefixLift 4130926
  have htrace : WordTrace (prefixWord ++ tailWord_4130926) baseStart_4130926 baseEnd_4130926 := by
    simpa [prefixWord, tailWord_4130926, baseEnd_4130926] using wordTrace_append hprefix tailTrace_4130926
  have hstable : (prefixWord ++ tailWord_4130926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130926).length < 2 ^ (prefixWord ++ tailWord_4130926).sum := by decide
  have hdescent : baseEnd_4130926 < baseStart_4130926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130940 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_4130940 : Nat := 118140960795 + 4130940 * 2 ^ 59
def prefixEnd_4130940 : Nat := 4983230072969 + 3 ^ 40 * 4130940 * 2
def baseEnd_4130940 : Nat := 2121157774884172911952159

theorem tailTrace_4130940 : CollatzResearch.WordTrace tailWord_4130940 prefixEnd_4130940 2121157774884172911952159 := by
  unfold tailWord_4130940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75333879827158681614359137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100445173102878242152478849 75333879827158681614359137)
  ·
    refine ⟨56500409870369011210769353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75333879827158681614359137 56500409870369011210769353)
    ·
      refine ⟨42375307402776758408077015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56500409870369011210769353 42375307402776758408077015)
      ·
        refine ⟨63562961104165137612115523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42375307402776758408077015 63562961104165137612115523)
        ·
          refine ⟨95344441656247706418173285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63562961104165137612115523 95344441656247706418173285)
          ·
            refine ⟨17877082810546444953407491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95344441656247706418173285 17877082810546444953407491)
            ·
              refine ⟨26815624215819667430111237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877082810546444953407491 26815624215819667430111237)
              ·
                refine ⟨5027929540466187643145857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26815624215819667430111237 5027929540466187643145857)
                ·
                  refine ⟨3770947155349640732359393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027929540466187643145857 3770947155349640732359393)
                  ·
                    refine ⟨2828210366512230549269545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770947155349640732359393 2828210366512230549269545)
                    ·
                      refine ⟨2121157774884172911952159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828210366512230549269545 2121157774884172911952159)
                      ·
                        rfl

theorem cell23_4130940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_4130940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130940 prefixEnd_4130940 := by exact prefixLift 4130940
  have htrace : WordTrace (prefixWord ++ tailWord_4130940) baseStart_4130940 baseEnd_4130940 := by
    simpa [prefixWord, tailWord_4130940, baseEnd_4130940] using wordTrace_append hprefix tailTrace_4130940
  have hstable : (prefixWord ++ tailWord_4130940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130940).length < 2 ^ (prefixWord ++ tailWord_4130940).sum := by decide
  have hdescent : baseEnd_4130940 < baseStart_4130940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130969 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_4130969 : Nat := 118140960795 + 4130969 * 2 ^ 59
def prefixEnd_4130969 : Nat := 4983230072969 + 3 ^ 40 * 4130969 * 2
def baseEnd_4130969 : Nat := 2121172665823153298489525

theorem tailTrace_4130969 : CollatzResearch.WordTrace tailWord_4130969 prefixEnd_4130969 2121172665823153298489525 := by
  unfold tailWord_4130969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150668817371212301181523961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100445878247474867454349307 150668817371212301181523961)
  ·
    refine ⟨113001613028409225886142971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150668817371212301181523961 113001613028409225886142971)
    ·
      refine ⟨169502419542613838829214457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113001613028409225886142971 169502419542613838829214457)
      ·
        refine ⟨127126814656960379121910843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169502419542613838829214457 127126814656960379121910843)
        ·
          refine ⟨190690221985440568682866265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127126814656960379121910843 190690221985440568682866265)
          ·
            refine ⟨143017666489080426512149699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190690221985440568682866265 143017666489080426512149699)
            ·
              refine ⟨214526499733620639768224549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143017666489080426512149699 214526499733620639768224549)
              ·
                refine ⟨40223718700053869956542103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214526499733620639768224549 40223718700053869956542103)
                ·
                  refine ⟨60335578050080804934813155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40223718700053869956542103 60335578050080804934813155)
                  ·
                    refine ⟨90503367075121207402219733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60335578050080804934813155 90503367075121207402219733)
                    ·
                      refine ⟨2121172665823153298489525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90503367075121207402219733 2121172665823153298489525)
                      ·
                        rfl

theorem cell23_4130969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_4130969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130969 prefixEnd_4130969 := by exact prefixLift 4130969
  have htrace : WordTrace (prefixWord ++ tailWord_4130969) baseStart_4130969 baseEnd_4130969 := by
    simpa [prefixWord, tailWord_4130969, baseEnd_4130969] using wordTrace_append hprefix tailTrace_4130969
  have hstable : (prefixWord ++ tailWord_4130969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130969).length < 2 ^ (prefixWord ++ tailWord_4130969).sum := by decide
  have hdescent : baseEnd_4130969 < baseStart_4130969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130976 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_4130976 : Nat := 118140960795 + 4130976 * 2 ^ 59
def prefixEnd_4130976 : Nat := 4983230072969 + 3 ^ 40 * 4130976 * 2
def baseEnd_4130976 : Nat := 707058753395911590367331

theorem tailTrace_4130976 : CollatzResearch.WordTrace tailWord_4130976 prefixEnd_4130976 707058753395911590367331 := by
  unfold tailWord_4130976
  simp only [CollatzResearch.WordTrace]
  refine ⟨75334536341093470688514391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100446048454791294251352521 75334536341093470688514391)
  ·
    refine ⟨113001804511640206032771587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75334536341093470688514391 113001804511640206032771587)
    ·
      refine ⟨169502706767460309049157381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113001804511640206032771587 169502706767460309049157381)
      ·
        refine ⟨31781757518898807946717009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169502706767460309049157381 31781757518898807946717009)
        ·
          refine ⟨23836318139174105960037757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31781757518898807946717009 23836318139174105960037757)
          ·
            refine ⟨8938619302190289735014159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23836318139174105960037757 8938619302190289735014159)
            ·
              refine ⟨13407928953285434602521239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938619302190289735014159 13407928953285434602521239)
              ·
                refine ⟨20111893429928151903781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13407928953285434602521239 20111893429928151903781859)
                ·
                  refine ⟨30167840144892227855672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20111893429928151903781859 30167840144892227855672789)
                  ·
                    refine ⟨707058753395911590367331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30167840144892227855672789 707058753395911590367331)
                    ·
                      rfl

theorem cell23_4130976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_4130976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130976 prefixEnd_4130976 := by exact prefixLift 4130976
  have htrace : WordTrace (prefixWord ++ tailWord_4130976) baseStart_4130976 baseEnd_4130976 := by
    simpa [prefixWord, tailWord_4130976, baseEnd_4130976] using wordTrace_append hprefix tailTrace_4130976
  have hstable : (prefixWord ++ tailWord_4130976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130976).length < 2 ^ (prefixWord ++ tailWord_4130976).sum := by decide
  have hdescent : baseEnd_4130976 < baseStart_4130976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130980 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 5]
def baseStart_4130980 : Nat := 118140960795 + 4130980 * 2 ^ 59
def prefixEnd_4130980 : Nat := 4983230072969 + 3 ^ 40 * 4130980 * 2
def baseEnd_4130980 : Nat := 235686479345594750605775

theorem tailTrace_4130980 : CollatzResearch.WordTrace tailWord_4130980 prefixEnd_4130980 235686479345594750605775 := by
  unfold tailWord_4130980
  simp only [CollatzResearch.WordTrace]
  refine ⟨75334609287086225030087197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100446145716114966706782929 75334609287086225030087197)
  ·
    refine ⟨28250478482657334386282699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75334609287086225030087197 28250478482657334386282699)
    ·
      refine ⟨42375717723986001579424049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250478482657334386282699 42375717723986001579424049)
      ·
        refine ⟨31781788292989501184568037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42375717723986001579424049 31781788292989501184568037)
        ·
          refine ⟨5959085304935531472106507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31781788292989501184568037 5959085304935531472106507)
          ·
            refine ⟨8938627957403297208159761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959085304935531472106507 8938627957403297208159761)
            ·
              refine ⟨6703970968052472906119821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938627957403297208159761 6703970968052472906119821)
              ·
                refine ⟨2513989113019677339794933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6703970968052472906119821 2513989113019677339794933)
                ·
                  refine ⟨235686479345594750605775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513989113019677339794933 235686479345594750605775)
                  ·
                    rfl

theorem cell23_4130980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_4130980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4130980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4130980 prefixEnd_4130980 := by exact prefixLift 4130980
  have htrace : WordTrace (prefixWord ++ tailWord_4130980) baseStart_4130980 baseEnd_4130980 := by
    simpa [prefixWord, tailWord_4130980, baseEnd_4130980] using wordTrace_append hprefix tailTrace_4130980
  have hstable : (prefixWord ++ tailWord_4130980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130980).length < 2 ^ (prefixWord ++ tailWord_4130980).sum := by decide
  have hdescent : baseEnd_4130980 < baseStart_4130980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131010 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4131010 : Nat := 118140960795 + 4131010 * 2 ^ 59
def prefixEnd_4131010 : Nat := 4983230072969 + 3 ^ 40 * 4131010 * 2
def baseEnd_4131010 : Nat := 707064572843329212692279

theorem tailTrace_4131010 : CollatzResearch.WordTrace tailWord_4131010 prefixEnd_4131010 707064572843329212692279 := by
  unfold tailWord_4131010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37667578191015941295941621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100446875176042510122510989 37667578191015941295941621)
  ·
    refine ⟨3531335455407744496494527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37667578191015941295941621 3531335455407744496494527)
    ·
      refine ⟨5297003183111616744741791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531335455407744496494527 5297003183111616744741791)
      ·
        refine ⟨7945504774667425117112687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297003183111616744741791 7945504774667425117112687)
        ·
          refine ⟨11918257162001137675669031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945504774667425117112687 11918257162001137675669031)
          ·
            refine ⟨17877385743001706513503547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918257162001137675669031 17877385743001706513503547)
            ·
              refine ⟨26816078614502559770255321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877385743001706513503547 26816078614502559770255321)
              ·
                refine ⟨20112058960876919827691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26816078614502559770255321 20112058960876919827691491)
                ·
                  refine ⟨30168088441315379741537237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20112058960876919827691491 30168088441315379741537237)
                  ·
                    refine ⟨707064572843329212692279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30168088441315379741537237 707064572843329212692279)
                    ·
                      rfl

theorem cell23_4131010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4131010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131010 prefixEnd_4131010 := by exact prefixLift 4131010
  have htrace : WordTrace (prefixWord ++ tailWord_4131010) baseStart_4131010 baseEnd_4131010 := by
    simpa [prefixWord, tailWord_4131010, baseEnd_4131010] using wordTrace_append hprefix tailTrace_4131010
  have hstable : (prefixWord ++ tailWord_4131010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131010).length < 2 ^ (prefixWord ++ tailWord_4131010).sum := by decide
  have hdescent : baseEnd_4131010 < baseStart_4131010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131013 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_4131013 : Nat := 118140960795 + 4131013 * 2 ^ 59
def prefixEnd_4131013 : Nat := 4983230072969 + 3 ^ 40 * 4131013 * 2
def baseEnd_4131013 : Nat := 2121195258971951126339323

theorem tailTrace_4131013 : CollatzResearch.WordTrace tailWord_4131013 prefixEnd_4131013 2121195258971951126339323 := by
  unfold tailWord_4131013
  simp only [CollatzResearch.WordTrace]
  refine ⟨150670422183052896696125693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100446948122035264464083795 150670422183052896696125693)
  ·
    refine ⟨56501408318644836261047135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150670422183052896696125693 56501408318644836261047135)
    ·
      refine ⟨84752112477967254391570703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56501408318644836261047135 84752112477967254391570703)
      ·
        refine ⟨127128168716950881587356055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84752112477967254391570703 127128168716950881587356055)
        ·
          refine ⟨190692253075426322381034083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127128168716950881587356055 190692253075426322381034083)
          ·
            refine ⟨286038379613139483571551125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190692253075426322381034083 286038379613139483571551125)
            ·
              refine ⟨13408049044365913292416459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286038379613139483571551125 13408049044365913292416459)
              ·
                refine ⟨20112073566548869938624689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408049044365913292416459 20112073566548869938624689)
                ·
                  refine ⟨15084055174911652453968517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20112073566548869938624689 15084055174911652453968517)
                  ·
                    refine ⟨2828260345295934835119097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15084055174911652453968517 2828260345295934835119097)
                    ·
                      refine ⟨2121195258971951126339323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828260345295934835119097 2121195258971951126339323)
                      ·
                        rfl

theorem cell23_4131013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_4131013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131013 prefixEnd_4131013 := by exact prefixLift 4131013
  have htrace : WordTrace (prefixWord ++ tailWord_4131013) baseStart_4131013 baseEnd_4131013 := by
    simpa [prefixWord, tailWord_4131013, baseEnd_4131013] using wordTrace_append hprefix tailTrace_4131013
  have hstable : (prefixWord ++ tailWord_4131013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131013).length < 2 ^ (prefixWord ++ tailWord_4131013).sum := by decide
  have hdescent : baseEnd_4131013 < baseStart_4131013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131030 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4131030 : Nat := 118140960795 + 4131030 * 2 ^ 59
def prefixEnd_4131030 : Nat := 4983230072969 + 3 ^ 40 * 4131030 * 2
def baseEnd_4131030 : Nat := 2121203988143077559826745

theorem tailTrace_4131030 : CollatzResearch.WordTrace tailWord_4131030 prefixEnd_4131030 2121203988143077559826745 := by
  unfold tailWord_4131030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416940138999456787468409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100447361482660872399663029 9416940138999456787468409)
  ·
    refine ⟨7062705104249592590601307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9416940138999456787468409 7062705104249592590601307)
    ·
      refine ⟨10594057656374388885901961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7062705104249592590601307 10594057656374388885901961)
      ·
        refine ⟨7945543242280791664426471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10594057656374388885901961 7945543242280791664426471)
        ·
          refine ⟨11918314863421187496639707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945543242280791664426471 11918314863421187496639707)
          ·
            refine ⟨17877472295131781244959561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918314863421187496639707 17877472295131781244959561)
            ·
              refine ⟨13408104221348835933719671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17877472295131781244959561 13408104221348835933719671)
              ·
                refine ⟨20112156332023253900579507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408104221348835933719671 20112156332023253900579507)
                ·
                  refine ⟨30168234498034880850869261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20112156332023253900579507 30168234498034880850869261)
                  ·
                    refine ⟨11313087936763080319075973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30168234498034880850869261 11313087936763080319075973)
                    ·
                      refine ⟨2121203988143077559826745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11313087936763080319075973 2121203988143077559826745)
                      ·
                        rfl

theorem cell23_4131030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4131030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131030 prefixEnd_4131030 := by exact prefixLift 4131030
  have htrace : WordTrace (prefixWord ++ tailWord_4131030) baseStart_4131030 baseEnd_4131030 := by
    simpa [prefixWord, tailWord_4131030, baseEnd_4131030] using wordTrace_append hprefix tailTrace_4131030
  have hstable : (prefixWord ++ tailWord_4131030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131030).length < 2 ^ (prefixWord ++ tailWord_4131030).sum := by decide
  have hdescent : baseEnd_4131030 < baseStart_4131030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131116 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_4131116 : Nat := 118140960795 + 4131116 * 2 ^ 59
def prefixEnd_4131116 : Nat := 4983230072969 + 3 ^ 40 * 4131116 * 2
def baseEnd_4131116 : Nat := 2121248147479364223351349

theorem tailTrace_4131116 : CollatzResearch.WordTrace tailWord_4131116 prefixEnd_4131116 2121248147479364223351349 := by
  unfold tailWord_4131116
  simp only [CollatzResearch.WordTrace]
  refine ⟨75337089450839872643562601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100449452601119830191416801 75337089450839872643562601)
  ·
    refine ⟨56502817088129904482671951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75337089450839872643562601 56502817088129904482671951)
    ·
      refine ⟨84754225632194856724007927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56502817088129904482671951 84754225632194856724007927)
      ·
        refine ⟨127131338448292285086011891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84754225632194856724007927 127131338448292285086011891)
        ·
          refine ⟨190697007672438427629017837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127131338448292285086011891 190697007672438427629017837)
          ·
            refine ⟨71511377877164410360881689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190697007672438427629017837 71511377877164410360881689)
            ·
              refine ⟨53633533407873307770661267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71511377877164410360881689 53633533407873307770661267)
              ·
                refine ⟨80450300111809961655991901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53633533407873307770661267 80450300111809961655991901)
                ·
                  refine ⟨30168862541928735620996963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80450300111809961655991901 30168862541928735620996963)
                  ·
                    refine ⟨45253293812893103431495445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30168862541928735620996963 45253293812893103431495445)
                    ·
                      refine ⟨2121248147479364223351349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45253293812893103431495445 2121248147479364223351349)
                      ·
                        rfl

theorem cell23_4131116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_4131116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131116 prefixEnd_4131116 := by exact prefixLift 4131116
  have htrace : WordTrace (prefixWord ++ tailWord_4131116) baseStart_4131116 baseEnd_4131116 := by
    simpa [prefixWord, tailWord_4131116, baseEnd_4131116] using wordTrace_append hprefix tailTrace_4131116
  have hstable : (prefixWord ++ tailWord_4131116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131116).length < 2 ^ (prefixWord ++ tailWord_4131116).sum := by decide
  have hdescent : baseEnd_4131116 < baseStart_4131116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131123 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3]
def baseStart_4131123 : Nat := 118140960795 + 4131123 * 2 ^ 59
def prefixEnd_4131123 : Nat := 4983230072969 + 3 ^ 40 * 4131123 * 2
def baseEnd_4131123 : Nat := 2121251741843945695963817

theorem tailTrace_4131123 : CollatzResearch.WordTrace tailWord_4131123 prefixEnd_4131123 2121251741843945695963817 := by
  unfold tailWord_4131123
  simp only [CollatzResearch.WordTrace]
  refine ⟨150674434212654385482630023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100449622808436256988420015 150674434212654385482630023)
  ·
    refine ⟨226011651318981578223945035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150674434212654385482630023 226011651318981578223945035)
    ·
      refine ⟨339017476978472367335917553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226011651318981578223945035 339017476978472367335917553)
      ·
        refine ⟨254263107733854275501938165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339017476978472367335917553 254263107733854275501938165)
        ·
          refine ⟨23837166350048838328306703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254263107733854275501938165 23837166350048838328306703)
          ·
            refine ⟨35755749525073257492460055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23837166350048838328306703 35755749525073257492460055)
            ·
              refine ⟨53633624287609886238690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35755749525073257492460055 53633624287609886238690083)
              ·
                refine ⟨80450436431414829358035125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53633624287609886238690083 80450436431414829358035125)
                ·
                  refine ⟨7542228415445140252315793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80450436431414829358035125 7542228415445140252315793)
                  ·
                    refine ⟨5656671311583855189236845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542228415445140252315793 5656671311583855189236845)
                    ·
                      refine ⟨2121251741843945695963817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656671311583855189236845 2121251741843945695963817)
                      ·
                        rfl

theorem cell23_4131123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_4131123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131123 prefixEnd_4131123 := by exact prefixLift 4131123
  have htrace : WordTrace (prefixWord ++ tailWord_4131123) baseStart_4131123 baseEnd_4131123 := by
    simpa [prefixWord, tailWord_4131123, baseEnd_4131123] using wordTrace_append hprefix tailTrace_4131123
  have hstable : (prefixWord ++ tailWord_4131123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131123).length < 2 ^ (prefixWord ++ tailWord_4131123).sum := by decide
  have hdescent : baseEnd_4131123 < baseStart_4131123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131130 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_4131130 : Nat := 118140960795 + 4131130 * 2 ^ 59
def prefixEnd_4131130 : Nat := 4983230072969 + 3 ^ 40 * 4131130 * 2
def baseEnd_4131130 : Nat := 707085112069509056192095

theorem tailTrace_4131130 : CollatzResearch.WordTrace tailWord_4131130 prefixEnd_4131130 707085112069509056192095 := by
  unfold tailWord_4131130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668672380907256419533711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100449793015752683785423229 37668672380907256419533711)
  ·
    refine ⟨56503008571360884629300567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37668672380907256419533711 56503008571360884629300567)
    ·
      refine ⟨84754512857041326943950851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56503008571360884629300567 84754512857041326943950851)
      ·
        refine ⟨127131769285561990415926277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84754512857041326943950851 127131769285561990415926277)
        ·
          refine ⟨23837206741042873202986177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127131769285561990415926277 23837206741042873202986177)
          ·
            refine ⟨17877905055782154902239633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23837206741042873202986177 17877905055782154902239633)
            ·
              refine ⟨13408428791836616176679725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17877905055782154902239633 13408428791836616176679725)
              ·
                refine ⟨5028160796938731066254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408428791836616176679725 5028160796938731066254897)
                ·
                  refine ⟨3771120597704048299691173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028160796938731066254897 3771120597704048299691173)
                  ·
                    refine ⟨707085112069509056192095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771120597704048299691173 707085112069509056192095)
                    ·
                      rfl

theorem cell23_4131130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_4131130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131130 prefixEnd_4131130 := by exact prefixLift 4131130
  have htrace : WordTrace (prefixWord ++ tailWord_4131130) baseStart_4131130 baseEnd_4131130 := by
    simpa [prefixWord, tailWord_4131130, baseEnd_4131130] using wordTrace_append hprefix tailTrace_4131130
  have hstable : (prefixWord ++ tailWord_4131130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131130).length < 2 ^ (prefixWord ++ tailWord_4131130).sum := by decide
  have hdescent : baseEnd_4131130 < baseStart_4131130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131143 : List Nat := [1, 1, 4, 1, 2, 2, 5, 7]
def baseStart_4131143 : Nat := 118140960795 + 4131143 * 2 ^ 59
def prefixEnd_4131143 : Nat := 4983230072969 + 3 ^ 40 * 4131143 * 2
def baseEnd_4131143 : Nat := 78565259683593911767175

theorem tailTrace_4131143 : CollatzResearch.WordTrace tailWord_4131143 prefixEnd_4131143 78565259683593911767175 := by
  unfold tailWord_4131143
  simp only [CollatzResearch.WordTrace]
  refine ⟨150675163672581928898358083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100450109115054619265572055 150675163672581928898358083)
  ·
    refine ⟨226012745508872893347537125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150675163672581928898358083 226012745508872893347537125)
    ·
      refine ⟨42377389782913667502663211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226012745508872893347537125 42377389782913667502663211)
      ·
        refine ⟨63566084674370501253994817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42377389782913667502663211 63566084674370501253994817)
        ·
          refine ⟨47674563505777875940496113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63566084674370501253994817 47674563505777875940496113)
          ·
            refine ⟨35755922629333406955372085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47674563505777875940496113 35755922629333406955372085)
            ·
              refine ⟨3352117746500006902066133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35755922629333406955372085 3352117746500006902066133)
              ·
                refine ⟨78565259683593911767175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3352117746500006902066133 78565259683593911767175)
                ·
                  rfl

theorem cell23_4131143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 7].length) (baseStart_4131143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131143 prefixEnd_4131143 := by exact prefixLift 4131143
  have htrace : WordTrace (prefixWord ++ tailWord_4131143) baseStart_4131143 baseEnd_4131143 := by
    simpa [prefixWord, tailWord_4131143, baseEnd_4131143] using wordTrace_append hprefix tailTrace_4131143
  have hstable : (prefixWord ++ tailWord_4131143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131143).length < 2 ^ (prefixWord ++ tailWord_4131143).sum := by decide
  have hdescent : baseEnd_4131143 < baseStart_4131143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131154 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_4131154 : Nat := 118140960795 + 4131154 * 2 ^ 59
def prefixEnd_4131154 : Nat := 4983230072969 + 3 ^ 40 * 4131154 * 2
def baseEnd_4131154 : Nat := 2121267659744235074676175

theorem tailTrace_4131154 : CollatzResearch.WordTrace tailWord_4131154 prefixEnd_4131154 2121267659744235074676175 := by
  unfold tailWord_4131154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668891218885519444252129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100450376583694718518005677 37668891218885519444252129)
  ·
    refine ⟨28251668414164139583189097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37668891218885519444252129 28251668414164139583189097)
    ·
      refine ⟨21188751310623104687391823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28251668414164139583189097 21188751310623104687391823)
      ·
        refine ⟨31783126965934657031087735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21188751310623104687391823 31783126965934657031087735)
        ·
          refine ⟨47674690448901985546631603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31783126965934657031087735 47674690448901985546631603)
          ·
            refine ⟨71512035673352978319947405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47674690448901985546631603 71512035673352978319947405)
            ·
              refine ⟨26817013377507366869980277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71512035673352978319947405 26817013377507366869980277)
              ·
                refine ⟨2514095004141315644060651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26817013377507366869980277 2514095004141315644060651)
                ·
                  refine ⟨3771142506211973466090977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514095004141315644060651 3771142506211973466090977)
                  ·
                    refine ⟨2828356879658980099568233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771142506211973466090977 2828356879658980099568233)
                    ·
                      refine ⟨2121267659744235074676175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828356879658980099568233 2121267659744235074676175)
                      ·
                        rfl

theorem cell23_4131154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_4131154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131154 prefixEnd_4131154 := by exact prefixLift 4131154
  have htrace : WordTrace (prefixWord ++ tailWord_4131154) baseStart_4131154 baseEnd_4131154 := by
    simpa [prefixWord, tailWord_4131154, baseEnd_4131154] using wordTrace_append hprefix tailTrace_4131154
  have hstable : (prefixWord ++ tailWord_4131154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131154).length < 2 ^ (prefixWord ++ tailWord_4131154).sum := by decide
  have hdescent : baseEnd_4131154 < baseStart_4131154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131157 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4131157 : Nat := 118140960795 + 4131157 * 2 ^ 59
def prefixEnd_4131157 : Nat := 4983230072969 + 3 ^ 40 * 4131157 * 2
def baseEnd_4131157 : Nat := 2121269200186198562938661

theorem tailTrace_4131157 : CollatzResearch.WordTrace tailWord_4131157 prefixEnd_4131157 2121269200186198562938661 := by
  unfold tailWord_4131157
  simp only [CollatzResearch.WordTrace]
  refine ⟨150675674294531209289367725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100450449529687472859578483 150675674294531209289367725)
  ·
    refine ⟨56503377860449203483512897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150675674294531209289367725 56503377860449203483512897)
    ·
      refine ⟨42377533395336902612634673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56503377860449203483512897 42377533395336902612634673)
      ·
        refine ⟨31783150046502676959476005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42377533395336902612634673 31783150046502676959476005)
        ·
          refine ⟨5959340633719251929901751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31783150046502676959476005 5959340633719251929901751)
          ·
            refine ⟨8939010950578877894852627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959340633719251929901751 8939010950578877894852627)
            ·
              refine ⟨13408516425868316842278941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939010950578877894852627 13408516425868316842278941)
              ·
                refine ⟨5028193659700618815854603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408516425868316842278941 5028193659700618815854603)
                ·
                  refine ⟨7542290489550928223781905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028193659700618815854603 7542290489550928223781905)
                  ·
                    refine ⟨5656717867163196167836429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542290489550928223781905 5656717867163196167836429)
                    ·
                      refine ⟨2121269200186198562938661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656717867163196167836429 2121269200186198562938661)
                      ·
                        rfl

theorem cell23_4131157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4131157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131157 prefixEnd_4131157 := by exact prefixLift 4131157
  have htrace : WordTrace (prefixWord ++ tailWord_4131157) baseStart_4131157 baseEnd_4131157 := by
    simpa [prefixWord, tailWord_4131157, baseEnd_4131157] using wordTrace_append hprefix tailTrace_4131157
  have hstable : (prefixWord ++ tailWord_4131157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131157).length < 2 ^ (prefixWord ++ tailWord_4131157).sum := by decide
  have hdescent : baseEnd_4131157 < baseStart_4131157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131197 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_4131197 : Nat := 118140960795 + 4131197 * 2 ^ 59
def prefixEnd_4131197 : Nat := 4983230072969 + 3 ^ 40 * 4131197 * 2
def baseEnd_4131197 : Nat := 2121289739412378406438477

theorem tailTrace_4131197 : CollatzResearch.WordTrace tailWord_4131197 prefixEnd_4131197 2121289739412378406438477 := by
  unfold tailWord_4131197
  simp only [CollatzResearch.WordTrace]
  refine ⟨150677133214386296120823845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100451422142924197413882563 150677133214386296120823845)
  ·
    refine ⟨28251962477697430522654471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150677133214386296120823845 28251962477697430522654471)
    ·
      refine ⟨42377943716546145783981707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28251962477697430522654471 42377943716546145783981707)
      ·
        refine ⟨63566915574819218675972561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42377943716546145783981707 63566915574819218675972561)
        ·
          refine ⟨47675186681114414006979421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63566915574819218675972561 47675186681114414006979421)
          ·
            refine ⟨17878195005417905252617283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47675186681114414006979421 17878195005417905252617283)
            ·
              refine ⟨26817292508126857878925925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17878195005417905252617283 26817292508126857878925925)
              ·
                refine ⟨5028242345273785852298611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26817292508126857878925925 5028242345273785852298611)
                ·
                  refine ⟨7542363517910678778447917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028242345273785852298611 7542363517910678778447917)
                  ·
                    refine ⟨2828386319216504541917969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7542363517910678778447917 2828386319216504541917969)
                    ·
                      refine ⟨2121289739412378406438477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828386319216504541917969 2121289739412378406438477)
                      ·
                        rfl

theorem cell23_4131197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_4131197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131197 prefixEnd_4131197 := by exact prefixLift 4131197
  have htrace : WordTrace (prefixWord ++ tailWord_4131197) baseStart_4131197 baseEnd_4131197 := by
    simpa [prefixWord, tailWord_4131197, baseEnd_4131197] using wordTrace_append hprefix tailTrace_4131197
  have hstable : (prefixWord ++ tailWord_4131197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131197).length < 2 ^ (prefixWord ++ tailWord_4131197).sum := by decide
  have hdescent : baseEnd_4131197 < baseStart_4131197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131214 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4131214 : Nat := 118140960795 + 4131214 * 2 ^ 59
def prefixEnd_4131214 : Nat := 4983230072969 + 3 ^ 40 * 4131214 * 2
def baseEnd_4131214 : Nat := 2121298468583504839925899

theorem tailTrace_4131214 : CollatzResearch.WordTrace tailWord_4131214 prefixEnd_4131214 2121298468583504839925899 := by
  unfold tailWord_4131214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834719156915588503024087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100451835503549805349461797 18834719156915588503024087)
  ·
    refine ⟨28252078735373382754536131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834719156915588503024087 28252078735373382754536131)
    ·
      refine ⟨42378118103060074131804197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28252078735373382754536131 42378118103060074131804197)
      ·
        refine ⟨7945897144323763899713287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42378118103060074131804197 7945897144323763899713287)
        ·
          refine ⟨11918845716485645849569931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945897144323763899713287 11918845716485645849569931)
          ·
            refine ⟨17878268574728468774354897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918845716485645849569931 17878268574728468774354897)
            ·
              refine ⟨13408701431046351580766173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17878268574728468774354897 13408701431046351580766173)
              ·
                refine ⟨5028263036642381842787315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408701431046351580766173 5028263036642381842787315)
                ·
                  refine ⟨7542394554963572764180973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028263036642381842787315 7542394554963572764180973)
                  ·
                    refine ⟨2828397958111339786567865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7542394554963572764180973 2828397958111339786567865)
                    ·
                      refine ⟨2121298468583504839925899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828397958111339786567865 2121298468583504839925899)
                      ·
                        rfl

theorem cell23_4131214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4131214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131214 prefixEnd_4131214 := by exact prefixLift 4131214
  have htrace : WordTrace (prefixWord ++ tailWord_4131214) baseStart_4131214 baseEnd_4131214 := by
    simpa [prefixWord, tailWord_4131214, baseEnd_4131214] using wordTrace_append hprefix tailTrace_4131214
  have hstable : (prefixWord ++ tailWord_4131214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131214).length < 2 ^ (prefixWord ++ tailWord_4131214).sum := by decide
  have hdescent : baseEnd_4131214 < baseStart_4131214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131222 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4131222 : Nat := 118140960795 + 4131222 * 2 ^ 59
def prefixEnd_4131222 : Nat := 4983230072969 + 3 ^ 40 * 4131222 * 2
def baseEnd_4131222 : Nat := 2121302576428740808625863

theorem tailTrace_4131222 : CollatzResearch.WordTrace tailWord_4131222 prefixEnd_4131222 2121302576428740808625863 := by
  unfold tailWord_4131222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417377814955982836905245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100452030026197150260322613 9417377814955982836905245)
  ·
    refine ⟨3531516680608493563839467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9417377814955982836905245 3531516680608493563839467)
    ·
      refine ⟨5297275020912740345759201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531516680608493563839467 5297275020912740345759201)
      ·
        refine ⟨3972956265684555259319401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5297275020912740345759201 3972956265684555259319401)
        ·
          refine ⟨2979717199263416444489551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972956265684555259319401 2979717199263416444489551)
          ·
            refine ⟨4469575798895124666734327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979717199263416444489551 4469575798895124666734327)
            ·
              refine ⟨6704363698342687000101491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469575798895124666734327 6704363698342687000101491)
              ·
                refine ⟨10056545547514030500152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704363698342687000101491 10056545547514030500152237)
                ·
                  refine ⟨3771204580317761437557089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10056545547514030500152237 3771204580317761437557089)
                  ·
                    refine ⟨2828403435238321078167817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771204580317761437557089 2828403435238321078167817)
                    ·
                      refine ⟨2121302576428740808625863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828403435238321078167817 2121302576428740808625863)
                      ·
                        rfl

theorem cell23_4131222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4131222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131222 prefixEnd_4131222 := by exact prefixLift 4131222
  have htrace : WordTrace (prefixWord ++ tailWord_4131222) baseStart_4131222 baseEnd_4131222 := by
    simpa [prefixWord, tailWord_4131222, baseEnd_4131222] using wordTrace_append hprefix tailTrace_4131222
  have hstable : (prefixWord ++ tailWord_4131222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131222).length < 2 ^ (prefixWord ++ tailWord_4131222).sum := by decide
  have hdescent : baseEnd_4131222 < baseStart_4131222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131223 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4131223 : Nat := 118140960795 + 4131223 * 2 ^ 59
def prefixEnd_4131223 : Nat := 4983230072969 + 3 ^ 40 * 4131223 * 2
def baseEnd_4131223 : Nat := 2121303089909395304713357

theorem tailTrace_4131223 : CollatzResearch.WordTrace tailWord_4131223 prefixEnd_4131223 2121303089909395304713357 := by
  unfold tailWord_4131223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150678081512292102561270323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100452054341528068374180215 150678081512292102561270323)
  ·
    refine ⟨226017122268438153841905485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150678081512292102561270323 226017122268438153841905485)
    ·
      refine ⟨84756420850664307690714557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226017122268438153841905485 84756420850664307690714557)
      ·
        refine ⟨31783657818999115384017959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84756420850664307690714557 31783657818999115384017959)
        ·
          refine ⟨47675486728498673076026939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31783657818999115384017959 47675486728498673076026939)
          ·
            refine ⟨71513230092748009614040409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47675486728498673076026939 71513230092748009614040409)
            ·
              refine ⟨53634922569561007210530307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71513230092748009614040409 53634922569561007210530307)
              ·
                refine ⟨80452383854341510815795461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53634922569561007210530307 80452383854341510815795461)
                ·
                  refine ⟨15084821972689033277961649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80452383854341510815795461 15084821972689033277961649)
                  ·
                    refine ⟨11313616479516774958471237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15084821972689033277961649 11313616479516774958471237)
                    ·
                      refine ⟨2121303089909395304713357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11313616479516774958471237 2121303089909395304713357)
                      ·
                        rfl

theorem cell23_4131223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4131223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131223 prefixEnd_4131223 := by exact prefixLift 4131223
  have htrace : WordTrace (prefixWord ++ tailWord_4131223) baseStart_4131223 baseEnd_4131223 := by
    simpa [prefixWord, tailWord_4131223, baseEnd_4131223] using wordTrace_append hprefix tailTrace_4131223
  have hstable : (prefixWord ++ tailWord_4131223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131223).length < 2 ^ (prefixWord ++ tailWord_4131223).sum := by decide
  have hdescent : baseEnd_4131223 < baseStart_4131223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131265 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4131265 : Nat := 118140960795 + 4131265 * 2 ^ 59
def prefixEnd_4131265 : Nat := 4983230072969 + 3 ^ 40 * 4131265 * 2
def baseEnd_4131265 : Nat := 2121324656096884140388165

theorem tailTrace_4131265 : CollatzResearch.WordTrace tailWord_4131265 prefixEnd_4131265 2121324656096884140388165 := by
  unfold tailWord_4131265
  simp only [CollatzResearch.WordTrace]
  refine ⟨150679613378139943734299249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100453075585426629156199499 150679613378139943734299249)
  ·
    refine ⟨113009710033604957800724437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150679613378139943734299249 113009710033604957800724437)
    ·
      refine ⟨2648665078912616198454479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113009710033604957800724437 2648665078912616198454479)
      ·
        refine ⟨3972997618368924297681719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648665078912616198454479 3972997618368924297681719)
        ·
          refine ⟨5959496427553386446522579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972997618368924297681719 5959496427553386446522579)
          ·
            refine ⟨8939244641330079669783869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959496427553386446522579 8939244641330079669783869)
            ·
              refine ⟨3352216740498779876168951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8939244641330079669783869 3352216740498779876168951)
              ·
                refine ⟨5028325110748169814253427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352216740498779876168951 5028325110748169814253427)
                ·
                  refine ⟨7542487666122254721380141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028325110748169814253427 7542487666122254721380141)
                  ·
                    refine ⟨2828432874795845520517553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7542487666122254721380141 2828432874795845520517553)
                    ·
                      refine ⟨2121324656096884140388165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828432874795845520517553 2121324656096884140388165)
                      ·
                        rfl

theorem cell23_4131265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4131265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131265 prefixEnd_4131265 := by exact prefixLift 4131265
  have htrace : WordTrace (prefixWord ++ tailWord_4131265) baseStart_4131265 baseEnd_4131265 := by
    simpa [prefixWord, tailWord_4131265, baseEnd_4131265] using wordTrace_append hprefix tailTrace_4131265
  have hstable : (prefixWord ++ tailWord_4131265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131265).length < 2 ^ (prefixWord ++ tailWord_4131265).sum := by decide
  have hdescent : baseEnd_4131265 < baseStart_4131265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131273 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_4131273 : Nat := 118140960795 + 4131273 * 2 ^ 59
def prefixEnd_4131273 : Nat := 4983230072969 + 3 ^ 40 * 4131273 * 2
def baseEnd_4131273 : Nat := 2121328763942120109088127

theorem tailTrace_4131273 : CollatzResearch.WordTrace tailWord_4131273 prefixEnd_4131273 2121328763942120109088127 := by
  unfold tailWord_4131273
  simp only [CollatzResearch.WordTrace]
  refine ⟨150679905162110961100590473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100453270108073974067060315 150679905162110961100590473)
  ·
    refine ⟨113009928871583220825442855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150679905162110961100590473 113009928871583220825442855)
    ·
      refine ⟨169514893307374831238164283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113009928871583220825442855 169514893307374831238164283)
      ·
        refine ⟨254272339961062246857246425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169514893307374831238164283 254272339961062246857246425)
        ·
          refine ⟨190704254970796685142934819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254272339961062246857246425 190704254970796685142934819)
          ·
            refine ⟨286056382456195027714402229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190704254970796685142934819 286056382456195027714402229)
            ·
              refine ⟨26817785855268283848225209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286056382456195027714402229 26817785855268283848225209)
              ·
                refine ⟨20113339391451212886168907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26817785855268283848225209 20113339391451212886168907)
                ·
                  refine ⟨30170009087176819329253361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20113339391451212886168907 30170009087176819329253361)
                  ·
                    refine ⟨22627506815382614496940021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30170009087176819329253361 22627506815382614496940021)
                    ·
                      refine ⟨2121328763942120109088127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22627506815382614496940021 2121328763942120109088127)
                      ·
                        rfl

theorem cell23_4131273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_4131273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131273 prefixEnd_4131273 := by exact prefixLift 4131273
  have htrace : WordTrace (prefixWord ++ tailWord_4131273) baseStart_4131273 baseEnd_4131273 := by
    simpa [prefixWord, tailWord_4131273, baseEnd_4131273] using wordTrace_append hprefix tailTrace_4131273
  have hstable : (prefixWord ++ tailWord_4131273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131273).length < 2 ^ (prefixWord ++ tailWord_4131273).sum := by decide
  have hdescent : baseEnd_4131273 < baseStart_4131273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131284 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 5]
def baseStart_4131284 : Nat := 118140960795 + 4131284 * 2 ^ 59
def prefixEnd_4131284 : Nat := 4983230072969 + 3 ^ 40 * 4131284 * 2
def baseEnd_4131284 : Nat := 235703823581035507338953

theorem tailTrace_4131284 : CollatzResearch.WordTrace tailWord_4131284 prefixEnd_4131284 235703823581035507338953 := by
  unfold tailWord_4131284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75340153182535554989620453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100453537576714073319493937 75340153182535554989620453)
  ·
    refine ⟨14126278721725416560553835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75340153182535554989620453 14126278721725416560553835)
    ·
      refine ⟨21189418082588124840830753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14126278721725416560553835 21189418082588124840830753)
      ·
        refine ⟨15892063561941093630623065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21189418082588124840830753 15892063561941093630623065)
        ·
          refine ⟨11919047671455820222967299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15892063561941093630623065 11919047671455820222967299)
          ·
            refine ⟨17878571507183730334450949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919047671455820222967299 17878571507183730334450949)
            ·
              refine ⟨3352232157596949437709553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17878571507183730334450949 3352232157596949437709553)
              ·
                refine ⟨2514174118197712078282165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352232157596949437709553 2514174118197712078282165)
                ·
                  refine ⟨235703823581035507338953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514174118197712078282165 235703823581035507338953)
                  ·
                    rfl

theorem cell23_4131284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_4131284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131284 prefixEnd_4131284 := by exact prefixLift 4131284
  have htrace : WordTrace (prefixWord ++ tailWord_4131284) baseStart_4131284 baseEnd_4131284 := by
    simpa [prefixWord, tailWord_4131284, baseEnd_4131284] using wordTrace_append hprefix tailTrace_4131284
  have hstable : (prefixWord ++ tailWord_4131284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131284).length < 2 ^ (prefixWord ++ tailWord_4131284).sum := by decide
  have hdescent : baseEnd_4131284 < baseStart_4131284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131314 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_4131314 : Nat := 118140960795 + 4131314 * 2 ^ 59
def prefixEnd_4131314 : Nat := 4983230072969 + 3 ^ 40 * 4131314 * 2
def baseEnd_4131314 : Nat := 707116605549651482891813

theorem tailTrace_4131314 : CollatzResearch.WordTrace tailWord_4131314 prefixEnd_4131314 707116605549651482891813 := by
  unfold tailWord_4131314
  simp only [CollatzResearch.WordTrace]
  refine ⟨37670350138740606275708249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100454267036641616735221997 37670350138740606275708249)
  ·
    refine ⟨28252762604055454706781187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37670350138740606275708249 28252762604055454706781187)
    ·
      refine ⟨42379143906083182060171781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28252762604055454706781187 42379143906083182060171781)
      ·
        refine ⟨7946089482390596636282209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42379143906083182060171781 7946089482390596636282209)
        ·
          refine ⟨5959567111792947477211657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7946089482390596636282209 5959567111792947477211657)
          ·
            refine ⟨4469675333844710607908743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5959567111792947477211657 4469675333844710607908743)
            ·
              refine ⟨6704513000767065911863115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469675333844710607908743 6704513000767065911863115)
              ·
                refine ⟨10056769501150598867794673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704513000767065911863115 10056769501150598867794673)
                ·
                  refine ⟨7542577125862949150846005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056769501150598867794673 7542577125862949150846005)
                  ·
                    refine ⟨707116605549651482891813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7542577125862949150846005 707116605549651482891813)
                    ·
                      rfl

theorem cell23_4131314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_4131314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131314 prefixEnd_4131314 := by exact prefixLift 4131314
  have htrace : WordTrace (prefixWord ++ tailWord_4131314) baseStart_4131314 baseEnd_4131314 := by
    simpa [prefixWord, tailWord_4131314, baseEnd_4131314] using wordTrace_append hprefix tailTrace_4131314
  have hstable : (prefixWord ++ tailWord_4131314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131314).length < 2 ^ (prefixWord ++ tailWord_4131314).sum := by decide
  have hdescent : baseEnd_4131314 < baseStart_4131314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131320 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_4131320 : Nat := 118140960795 + 4131320 * 2 ^ 59
def prefixEnd_4131320 : Nat := 4983230072969 + 3 ^ 40 * 4131320 * 2
def baseEnd_4131320 : Nat := 2121352897532881425200411

theorem tailTrace_4131320 : CollatzResearch.WordTrace tailWord_4131320 prefixEnd_4131320 2121352897532881425200411 := by
  unfold tailWord_4131320
  simp only [CollatzResearch.WordTrace]
  refine ⟨75340809696470344063775707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100454412928627125418367609 75340809696470344063775707)
  ·
    refine ⟨113011214544705516095663561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75340809696470344063775707 113011214544705516095663561)
    ·
      refine ⟨84758410908529137071747671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113011214544705516095663561 84758410908529137071747671)
      ·
        refine ⟨127137616362793705607621507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84758410908529137071747671 127137616362793705607621507)
        ·
          refine ⟨190706424544190558411432261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127137616362793705607621507 190706424544190558411432261)
          ·
            refine ⟨35757454602035729702143549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190706424544190558411432261 35757454602035729702143549)
            ·
              refine ⟨13409045475763398638303831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35757454602035729702143549 13409045475763398638303831)
              ·
                refine ⟨20113568213645097957455747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409045475763398638303831 20113568213645097957455747)
                ·
                  refine ⟨30170352320467646936183621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20113568213645097957455747 30170352320467646936183621)
                  ·
                    refine ⟨5656941060087683800534429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30170352320467646936183621 5656941060087683800534429)
                    ·
                      refine ⟨2121352897532881425200411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5656941060087683800534429 2121352897532881425200411)
                      ·
                        rfl

theorem cell23_4131320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_4131320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131320 prefixEnd_4131320 := by exact prefixLift 4131320
  have htrace : WordTrace (prefixWord ++ tailWord_4131320) baseStart_4131320 baseEnd_4131320 := by
    simpa [prefixWord, tailWord_4131320, baseEnd_4131320] using wordTrace_append hprefix tailTrace_4131320
  have hstable : (prefixWord ++ tailWord_4131320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131320).length < 2 ^ (prefixWord ++ tailWord_4131320).sum := by decide
  have hdescent : baseEnd_4131320 < baseStart_4131320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131340 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 8]
def baseStart_4131340 : Nat := 118140960795 + 4131340 * 2 ^ 59
def prefixEnd_4131340 : Nat := 4983230072969 + 3 ^ 40 * 4131340 * 2
def baseEnd_4131340 : Nat := 235707018571774594105591

theorem tailTrace_4131340 : CollatzResearch.WordTrace tailWord_4131340 prefixEnd_4131340 235707018571774594105591 := by
  unfold tailWord_4131340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75341174426434115771639737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100454899235245487695519649 75341174426434115771639737)
  ·
    refine ⟨56505880819825586828729803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75341174426434115771639737 56505880819825586828729803)
    ·
      refine ⟨84758821229738380243094705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56505880819825586828729803 84758821229738380243094705)
      ·
        refine ⟨63569115922303785182321029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84758821229738380243094705 63569115922303785182321029)
        ·
          refine ⟨11919209235431959721685193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63569115922303785182321029 11919209235431959721685193)
          ·
            refine ⟨8939406926573969791263895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11919209235431959721685193 8939406926573969791263895)
            ·
              refine ⟨13409110389860954686895843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939406926573969791263895 13409110389860954686895843)
              ·
                refine ⟨20113665584791432030343765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409110389860954686895843 20113665584791432030343765)
                ·
                  refine ⟨235707018571774594105591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20113665584791432030343765 235707018571774594105591)
                  ·
                    rfl

theorem cell23_4131340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_4131340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131340 prefixEnd_4131340 := by exact prefixLift 4131340
  have htrace : WordTrace (prefixWord ++ tailWord_4131340) baseStart_4131340 baseEnd_4131340 := by
    simpa [prefixWord, tailWord_4131340, baseEnd_4131340] using wordTrace_append hprefix tailTrace_4131340
  have hstable : (prefixWord ++ tailWord_4131340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131340).length < 2 ^ (prefixWord ++ tailWord_4131340).sum := by decide
  have hdescent : baseEnd_4131340 < baseStart_4131340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131343 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_4131343 : Nat := 118140960795 + 4131343 * 2 ^ 59
def prefixEnd_4131343 : Nat := 4983230072969 + 3 ^ 40 * 4131343 * 2
def baseEnd_4131343 : Nat := 2121364707587934835212805

theorem tailTrace_4131343 : CollatzResearch.WordTrace tailWord_4131343 prefixEnd_4131343 2121364707587934835212805 := by
  unfold tailWord_4131343
  simp only [CollatzResearch.WordTrace]
  refine ⟨150682458271857363055638683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100454972181238242037092455 150682458271857363055638683)
  ·
    refine ⟨226023687407786044583458025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150682458271857363055638683 226023687407786044583458025)
    ·
      refine ⟨169517765555839533437593519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226023687407786044583458025 169517765555839533437593519)
      ·
        refine ⟨254276648333759300156390279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169517765555839533437593519 254276648333759300156390279)
        ·
          refine ⟨381414972500638950234585419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254276648333759300156390279 381414972500638950234585419)
          ·
            refine ⟨572122458750958425351878129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381414972500638950234585419 572122458750958425351878129)
            ·
              refine ⟨429091844063218819013908597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572122458750958425351878129 429091844063218819013908597)
              ·
                refine ⟨40227360380926764282553931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429091844063218819013908597 40227360380926764282553931)
                ·
                  refine ⟨60341040571390146423830897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40227360380926764282553931 60341040571390146423830897)
                  ·
                    refine ⟨45255780428542609817873173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60341040571390146423830897 45255780428542609817873173)
                    ·
                      refine ⟨2121364707587934835212805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45255780428542609817873173 2121364707587934835212805)
                      ·
                        rfl

theorem cell23_4131343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_4131343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131343 prefixEnd_4131343 := by exact prefixLift 4131343
  have htrace : WordTrace (prefixWord ++ tailWord_4131343) baseStart_4131343 baseEnd_4131343 := by
    simpa [prefixWord, tailWord_4131343, baseEnd_4131343] using wordTrace_append hprefix tailTrace_4131343
  have hstable : (prefixWord ++ tailWord_4131343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131343).length < 2 ^ (prefixWord ++ tailWord_4131343).sum := by decide
  have hdescent : baseEnd_4131343 < baseStart_4131343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131377 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_4131377 : Nat := 118140960795 + 4131377 * 2 ^ 59
def prefixEnd_4131377 : Nat := 4983230072969 + 3 ^ 40 * 4131377 * 2
def baseEnd_4131377 : Nat := 2121382165930187702187649

theorem tailTrace_4131377 : CollatzResearch.WordTrace tailWord_4131377 prefixEnd_4131377 2121382165930187702187649 := by
  unfold tailWord_4131377
  simp only [CollatzResearch.WordTrace]
  refine ⟨150683698353734186862376385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100455798902489457908250923 150683698353734186862376385)
  ·
    refine ⟨113012773765300640146782289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150683698353734186862376385 113012773765300640146782289)
    ·
      refine ⟨84759580323975480110086717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113012773765300640146782289 84759580323975480110086717)
      ·
        refine ⟨31784842621490805041282519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84759580323975480110086717 31784842621490805041282519)
        ·
          refine ⟨47677263932236207561923779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31784842621490805041282519 47677263932236207561923779)
          ·
            refine ⟨71515895898354311342885669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47677263932236207561923779 71515895898354311342885669)
            ·
              refine ⟨13409230480941433376791063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71515895898354311342885669 13409230480941433376791063)
              ·
                refine ⟨20113845721412150065186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409230480941433376791063 20113845721412150065186595)
                ·
                  refine ⟨30170768582118225097779893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20113845721412150065186595 30170768582118225097779893)
                  ·
                    refine ⟨2828509554573583602916865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30170768582118225097779893 2828509554573583602916865)
                    ·
                      refine ⟨2121382165930187702187649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828509554573583602916865 2121382165930187702187649)
                      ·
                        rfl

theorem cell23_4131377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_4131377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131377 prefixEnd_4131377 := by exact prefixLift 4131377
  have htrace : WordTrace (prefixWord ++ tailWord_4131377) baseStart_4131377 baseEnd_4131377 := by
    simpa [prefixWord, tailWord_4131377, baseEnd_4131377] using wordTrace_append hprefix tailTrace_4131377
  have hstable : (prefixWord ++ tailWord_4131377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131377).length < 2 ^ (prefixWord ++ tailWord_4131377).sum := by decide
  have hdescent : baseEnd_4131377 < baseStart_4131377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131424 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2]
def baseStart_4131424 : Nat := 118140960795 + 4131424 * 2 ^ 59
def prefixEnd_4131424 : Nat := 4983230072969 + 3 ^ 40 * 4131424 * 2
def baseEnd_4131424 : Nat := 2121406299520949018299933

theorem tailTrace_4131424 : CollatzResearch.WordTrace tailWord_4131424 prefixEnd_4131424 2121406299520949018299933 := by
  unfold tailWord_4131424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75342706292281956944668663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100456941723042609259558217 75342706292281956944668663)
  ·
    refine ⟨113014059438422935417002995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75342706292281956944668663 113014059438422935417002995)
    ·
      refine ⟨169521089157634403125504493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113014059438422935417002995 169521089157634403125504493)
      ·
        refine ⟨63570408434112901172064185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169521089157634403125504493 63570408434112901172064185)
        ·
          refine ⟨47677806325584675879048139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63570408434112901172064185 47677806325584675879048139)
          ·
            refine ⟨71516709488377013818572209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47677806325584675879048139 71516709488377013818572209)
            ·
              refine ⟨53637532116282760363929157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71516709488377013818572209 53637532116282760363929157)
              ·
                refine ⟨10057037271803017568236717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53637532116282760363929157 10057037271803017568236717)
                ·
                  refine ⟨3771388976926131588088769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10057037271803017568236717 3771388976926131588088769)
                  ·
                    refine ⟨2828541732694598691066577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771388976926131588088769 2828541732694598691066577)
                    ·
                      refine ⟨2121406299520949018299933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828541732694598691066577 2121406299520949018299933)
                      ·
                        rfl

theorem cell23_4131424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_4131424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131424 prefixEnd_4131424 := by exact prefixLift 4131424
  have htrace : WordTrace (prefixWord ++ tailWord_4131424) baseStart_4131424 baseEnd_4131424 := by
    simpa [prefixWord, tailWord_4131424, baseEnd_4131424] using wordTrace_append hprefix tailTrace_4131424
  have hstable : (prefixWord ++ tailWord_4131424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131424).length < 2 ^ (prefixWord ++ tailWord_4131424).sum := by decide
  have hdescent : baseEnd_4131424 < baseStart_4131424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131427 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3]
def baseStart_4131427 : Nat := 118140960795 + 4131427 * 2 ^ 59
def prefixEnd_4131427 : Nat := 4983230072969 + 3 ^ 40 * 4131427 * 2
def baseEnd_4131427 : Nat := 2121407839962912506562419

theorem tailTrace_4131427 : CollatzResearch.WordTrace tailWord_4131427 prefixEnd_4131427 2121407839962912506562419 := by
  unfold tailWord_4131427
  simp only [CollatzResearch.WordTrace]
  refine ⟨150685522003553045401696535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100457014669035363601131023 150685522003553045401696535)
  ·
    refine ⟨226028283005329568102544803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150685522003553045401696535 226028283005329568102544803)
    ·
      refine ⟨339042424507994352153817205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226028283005329568102544803 339042424507994352153817205)
      ·
        refine ⟨31785227297624470514420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339042424507994352153817205 31785227297624470514420363)
        ·
          refine ⟨47677840946436705771630545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31785227297624470514420363 47677840946436705771630545)
          ·
            refine ⟨35758380709827529328722909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47677840946436705771630545 35758380709827529328722909)
            ·
              refine ⟨13409392766185323498271091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35758380709827529328722909 13409392766185323498271091)
              ·
                refine ⟨20114089149277985247406637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409392766185323498271091 20114089149277985247406637)
                ·
                  refine ⟨7542783430979244467777489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20114089149277985247406637 7542783430979244467777489)
                  ·
                    refine ⟨5657087573234433350833117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542783430979244467777489 5657087573234433350833117)
                    ·
                      refine ⟨2121407839962912506562419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657087573234433350833117 2121407839962912506562419)
                      ·
                        rfl

theorem cell23_4131427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_4131427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131427 prefixEnd_4131427 := by exact prefixLift 4131427
  have htrace : WordTrace (prefixWord ++ tailWord_4131427) baseStart_4131427 baseEnd_4131427 := by
    simpa [prefixWord, tailWord_4131427, baseEnd_4131427] using wordTrace_append hprefix tailTrace_4131427
  have hstable : (prefixWord ++ tailWord_4131427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131427).length < 2 ^ (prefixWord ++ tailWord_4131427).sum := by decide
  have hdescent : baseEnd_4131427 < baseStart_4131427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131437 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4131437 : Nat := 118140960795 + 4131437 * 2 ^ 59
def prefixEnd_4131437 : Nat := 4983230072969 + 3 ^ 40 * 4131437 * 2
def baseEnd_4131437 : Nat := 2121412974769457467437373

theorem tailTrace_4131437 : CollatzResearch.WordTrace tailWord_4131437 prefixEnd_4131437 2121412974769457467437373 := by
  unfold tailWord_4131437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150685886733516817109560565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100457257822344544739707043 150685886733516817109560565)
  ·
    refine ⟨14126801881267201604021303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150685886733516817109560565 14126801881267201604021303)
    ·
      refine ⟨21190202821900802406031955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14126801881267201604021303 21190202821900802406031955)
      ·
        refine ⟨31785304232851203609047933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21190202821900802406031955 31785304232851203609047933)
        ·
          refine ⟨11919489087319201353392975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31785304232851203609047933 11919489087319201353392975)
          ·
            refine ⟨17879233630978802030089463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919489087319201353392975 17879233630978802030089463)
            ·
              refine ⟨26818850446468203045134195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879233630978802030089463 26818850446468203045134195)
              ·
                refine ⟨40228275669702304567701293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26818850446468203045134195 40228275669702304567701293)
                ·
                  refine ⟨15085603376138364212887985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40228275669702304567701293 15085603376138364212887985)
                  ·
                    refine ⟨11314202532103773159665989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15085603376138364212887985 11314202532103773159665989)
                    ·
                      refine ⟨2121412974769457467437373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11314202532103773159665989 2121412974769457467437373)
                      ·
                        rfl

theorem cell23_4131437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4131437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131437 prefixEnd_4131437 := by exact prefixLift 4131437
  have htrace : WordTrace (prefixWord ++ tailWord_4131437) baseStart_4131437 baseEnd_4131437 := by
    simpa [prefixWord, tailWord_4131437, baseEnd_4131437] using wordTrace_append hprefix tailTrace_4131437
  have hstable : (prefixWord ++ tailWord_4131437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131437).length < 2 ^ (prefixWord ++ tailWord_4131437).sum := by decide
  have hdescent : baseEnd_4131437 < baseStart_4131437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131457 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4131457 : Nat := 118140960795 + 4131457 * 2 ^ 59
def prefixEnd_4131457 : Nat := 4983230072969 + 3 ^ 40 * 4131457 * 2
def baseEnd_4131457 : Nat := 2121423244382547389187281

theorem tailTrace_4131457 : CollatzResearch.WordTrace tailWord_4131457 prefixEnd_4131457 2121423244382547389187281 := by
  unfold tailWord_4131457
  simp only [CollatzResearch.WordTrace]
  refine ⟨150686616193444360525288625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100457744128962907016859083 150686616193444360525288625)
  ·
    refine ⟨113014962145083270393966469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150686616193444360525288625 113014962145083270393966469)
    ·
      refine ⟨21190305402203113198868713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113014962145083270393966469 21190305402203113198868713)
      ·
        refine ⟨15892729051652334899151535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21190305402203113198868713 15892729051652334899151535)
        ·
          refine ⟨23839093577478502348727303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892729051652334899151535 23839093577478502348727303)
          ·
            refine ⟨35758640366217753523090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23839093577478502348727303 35758640366217753523090955)
            ·
              refine ⟨53637960549326630284636433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35758640366217753523090955 53637960549326630284636433)
              ·
                refine ⟨40228470411994972713477325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53637960549326630284636433 40228470411994972713477325)
                ·
                  refine ⟨15085676404498114767553997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40228470411994972713477325 15085676404498114767553997)
                  ·
                    refine ⟨5657128651686793037832749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15085676404498114767553997 5657128651686793037832749)
                    ·
                      refine ⟨2121423244382547389187281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657128651686793037832749 2121423244382547389187281)
                      ·
                        rfl

theorem cell23_4131457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4131457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131457 prefixEnd_4131457 := by exact prefixLift 4131457
  have htrace : WordTrace (prefixWord ++ tailWord_4131457) baseStart_4131457 baseEnd_4131457 := by
    simpa [prefixWord, tailWord_4131457, baseEnd_4131457] using wordTrace_append hprefix tailTrace_4131457
  have hstable : (prefixWord ++ tailWord_4131457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131457).length < 2 ^ (prefixWord ++ tailWord_4131457).sum := by decide
  have hdescent : baseEnd_4131457 < baseStart_4131457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131474 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4131474 : Nat := 118140960795 + 4131474 * 2 ^ 59
def prefixEnd_4131474 : Nat := 4983230072969 + 3 ^ 40 * 4131474 * 2
def baseEnd_4131474 : Nat := 2121431973553673822674703

theorem tailTrace_4131474 : CollatzResearch.WordTrace tailWord_4131474 prefixEnd_4131474 2121431973553673822674703 := by
  unfold tailWord_4131474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37671809058595693107164369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100458157489588514952438317 37671809058595693107164369)
  ·
    refine ⟨28253856793946769830373277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37671809058595693107164369 28253856793946769830373277)
    ·
      refine ⟨10595196297730038686389979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28253856793946769830373277 10595196297730038686389979)
      ·
        refine ⟨15892794446595058029584969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595196297730038686389979 15892794446595058029584969)
        ·
          refine ⟨11919595834946293522188727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15892794446595058029584969 11919595834946293522188727)
          ·
            refine ⟨17879393752419440283283091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919595834946293522188727 17879393752419440283283091)
            ·
              refine ⟨26819090628629160424924637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879393752419440283283091 26819090628629160424924637)
              ·
                refine ⟨10057158985735935159346739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26819090628629160424924637 10057158985735935159346739)
                ·
                  refine ⟨15085738478603902739020109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057158985735935159346739 15085738478603902739020109)
                  ·
                    refine ⟨5657151929476463527132541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15085738478603902739020109 5657151929476463527132541)
                    ·
                      refine ⟨2121431973553673822674703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657151929476463527132541 2121431973553673822674703)
                      ·
                        rfl

theorem cell23_4131474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4131474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131474 prefixEnd_4131474 := by exact prefixLift 4131474
  have htrace : WordTrace (prefixWord ++ tailWord_4131474) baseStart_4131474 baseEnd_4131474 := by
    simpa [prefixWord, tailWord_4131474, baseEnd_4131474] using wordTrace_append hprefix tailTrace_4131474
  have hstable : (prefixWord ++ tailWord_4131474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131474).length < 2 ^ (prefixWord ++ tailWord_4131474).sum := by decide
  have hdescent : baseEnd_4131474 < baseStart_4131474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131495 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4131495 : Nat := 118140960795 + 4131495 * 2 ^ 59
def prefixEnd_4131495 : Nat := 4983230072969 + 3 ^ 40 * 4131495 * 2
def baseEnd_4131495 : Nat := 2121442756647418240512107

theorem tailTrace_4131495 : CollatzResearch.WordTrace tailWord_4131495 prefixEnd_4131495 2121442756647418240512107 := by
  unfold tailWord_4131495
  simp only [CollatzResearch.WordTrace]
  refine ⟨150688002167306693015171939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100458668111537795343447959 150688002167306693015171939)
  ·
    refine ⟨226032003250960039522757909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150688002167306693015171939 226032003250960039522757909)
    ·
      refine ⟨10595250152388751852629277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226032003250960039522757909 10595250152388751852629277)
      ·
        refine ⟨3973218807145781944735979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10595250152388751852629277 3973218807145781944735979)
        ·
          refine ⟨5959828210718672917103969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973218807145781944735979 5959828210718672917103969)
          ·
            refine ⟨4469871158039004687827977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5959828210718672917103969 4469871158039004687827977)
            ·
              refine ⟨3352403368529253515870983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469871158039004687827977 3352403368529253515870983)
              ·
                refine ⟨5028605052793880273806475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352403368529253515870983 5028605052793880273806475)
                ·
                  refine ⟨7542907579190820410709713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028605052793880273806475 7542907579190820410709713)
                  ·
                    refine ⟨5657180684393115308032285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542907579190820410709713 5657180684393115308032285)
                    ·
                      refine ⟨2121442756647418240512107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657180684393115308032285 2121442756647418240512107)
                      ·
                        rfl

theorem cell23_4131495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4131495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131495 prefixEnd_4131495 := by exact prefixLift 4131495
  have htrace : WordTrace (prefixWord ++ tailWord_4131495) baseStart_4131495 baseEnd_4131495 := by
    simpa [prefixWord, tailWord_4131495, baseEnd_4131495] using wordTrace_append hprefix tailTrace_4131495
  have hstable : (prefixWord ++ tailWord_4131495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131495).length < 2 ^ (prefixWord ++ tailWord_4131495).sum := by decide
  have hdescent : baseEnd_4131495 < baseStart_4131495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131548 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4131548 : Nat := 118140960795 + 4131548 * 2 ^ 59
def prefixEnd_4131548 : Nat := 4983230072969 + 3 ^ 40 * 4131548 * 2
def baseEnd_4131548 : Nat := 2121469971122106533149363

theorem tailTrace_4131548 : CollatzResearch.WordTrace tailWord_4131548 prefixEnd_4131548 2121469971122106533149363 := by
  unfold tailWord_4131548
  simp only [CollatzResearch.WordTrace]
  refine ⟨75344967618057341533425649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100459956824076455377900865 75344967618057341533425649)
  ·
    refine ⟨56508725713543006150069237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75344967618057341533425649 56508725713543006150069237)
    ·
      refine ⟨5297693035644656826568991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56508725713543006150069237 5297693035644656826568991)
      ·
        refine ⟨7946539553466985239853487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297693035644656826568991 7946539553466985239853487)
        ·
          refine ⟨11919809330200477859780231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946539553466985239853487 11919809330200477859780231)
          ·
            refine ⟨17879713995300716789670347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919809330200477859780231 17879713995300716789670347)
            ·
              refine ⟨26819570992951075184505521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879713995300716789670347 26819570992951075184505521)
              ·
                refine ⟨20114678244713306388379141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26819570992951075184505521 20114678244713306388379141)
                ·
                  refine ⟨3771502170883744947821089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20114678244713306388379141 3771502170883744947821089)
                  ·
                    refine ⟨2828626628162808710865817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771502170883744947821089 2828626628162808710865817)
                    ·
                      refine ⟨2121469971122106533149363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828626628162808710865817 2121469971122106533149363)
                      ·
                        rfl

theorem cell23_4131548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4131548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131548 prefixEnd_4131548 := by exact prefixLift 4131548
  have htrace : WordTrace (prefixWord ++ tailWord_4131548) baseStart_4131548 baseEnd_4131548 := by
    simpa [prefixWord, tailWord_4131548, baseEnd_4131548] using wordTrace_append hprefix tailTrace_4131548
  have hstable : (prefixWord ++ tailWord_4131548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131548).length < 2 ^ (prefixWord ++ tailWord_4131548).sum := by decide
  have hdescent : baseEnd_4131548 < baseStart_4131548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131567 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 4, 5]
def baseStart_4131567 : Nat := 118140960795 + 4131567 * 2 ^ 59
def prefixEnd_4131567 : Nat := 4983230072969 + 3 ^ 40 * 4131567 * 2
def baseEnd_4131567 : Nat := 707159909084847319603925

theorem tailTrace_4131567 : CollatzResearch.WordTrace tailWord_4131567 prefixEnd_4131567 707159909084847319603925 := by
  unfold tailWord_4131567
  simp only [CollatzResearch.WordTrace]
  refine ⟨150690628223045849311792955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100460418815363899541195303 150690628223045849311792955)
  ·
    refine ⟨226035942334568773967689433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150690628223045849311792955 226035942334568773967689433)
    ·
      refine ⟨169526956750926580475767075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226035942334568773967689433 169526956750926580475767075)
      ·
        refine ⟨254290435126389870713650613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169526956750926580475767075 254290435126389870713650613)
        ·
          refine ⟨23839728293099050379404745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254290435126389870713650613 23839728293099050379404745)
          ·
            refine ⟨17879796219824287784553559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23839728293099050379404745 17879796219824287784553559)
            ·
              refine ⟨26819694329736431676830339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879796219824287784553559 26819694329736431676830339)
              ·
                refine ⟨40229541494604647515245509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26819694329736431676830339 40229541494604647515245509)
                ·
                  refine ⟨7543039030238371409108533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40229541494604647515245509 7543039030238371409108533)
                  ·
                    refine ⟨707159909084847319603925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7543039030238371409108533 707159909084847319603925)
                    ·
                      rfl

theorem cell23_4131567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_4131567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131567 prefixEnd_4131567 := by exact prefixLift 4131567
  have htrace : WordTrace (prefixWord ++ tailWord_4131567) baseStart_4131567 baseEnd_4131567 := by
    simpa [prefixWord, tailWord_4131567, baseEnd_4131567] using wordTrace_append hprefix tailTrace_4131567
  have hstable : (prefixWord ++ tailWord_4131567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131567).length < 2 ^ (prefixWord ++ tailWord_4131567).sum := by decide
  have hdescent : baseEnd_4131567 < baseStart_4131567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131582 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_4131582 : Nat := 118140960795 + 4131582 * 2 ^ 59
def prefixEnd_4131582 : Nat := 4983230072969 + 3 ^ 40 * 4131582 * 2
def baseEnd_4131582 : Nat := 2121487429464359400124207

theorem tailTrace_4131582 : CollatzResearch.WordTrace tailWord_4131582 prefixEnd_4131582 2121487429464359400124207 := by
  unfold tailWord_4131582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18836396914748938359198625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100460783545327671249059333 18836396914748938359198625)
  ·
    refine ⟨14127297686061703769398969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18836396914748938359198625 14127297686061703769398969)
    ·
      refine ⟨10595473264546277827049227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14127297686061703769398969 10595473264546277827049227)
      ·
        refine ⟨15893209896819416740573841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595473264546277827049227 15893209896819416740573841)
        ·
          refine ⟨11919907422614562555430381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15893209896819416740573841 11919907422614562555430381)
          ·
            refine ⟨4469965283480460958286393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11919907422614562555430381 4469965283480460958286393)
            ·
              refine ⟨3352473962610345718714795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469965283480460958286393 3352473962610345718714795)
              ·
                refine ⟨5028710943915518578072193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352473962610345718714795 5028710943915518578072193)
                ·
                  refine ⟨3771533207936638933554145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028710943915518578072193 3771533207936638933554145)
                  ·
                    refine ⟨2828649905952479200165609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771533207936638933554145 2828649905952479200165609)
                    ·
                      refine ⟨2121487429464359400124207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828649905952479200165609 2121487429464359400124207)
                      ·
                        rfl

theorem cell23_4131582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_4131582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131582 prefixEnd_4131582 := by exact prefixLift 4131582
  have htrace : WordTrace (prefixWord ++ tailWord_4131582) baseStart_4131582 baseEnd_4131582 := by
    simpa [prefixWord, tailWord_4131582, baseEnd_4131582] using wordTrace_append hprefix tailTrace_4131582
  have hstable : (prefixWord ++ tailWord_4131582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131582).length < 2 ^ (prefixWord ++ tailWord_4131582).sum := by decide
  have hdescent : baseEnd_4131582 < baseStart_4131582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131587 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4]
def baseStart_4131587 : Nat := 118140960795 + 4131587 * 2 ^ 59
def prefixEnd_4131587 : Nat := 4983230072969 + 3 ^ 40 * 4131587 * 2
def baseEnd_4131587 : Nat := 2121489996867631880561683

theorem tailTrace_4131587 : CollatzResearch.WordTrace tailWord_4131587 prefixEnd_4131587 2121489996867631880561683 := by
  unfold tailWord_4131587
  simp only [CollatzResearch.WordTrace]
  refine ⟨150691357682973392727521015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100460905121982261818347343 150691357682973392727521015)
  ·
    refine ⟨226037036524460089091281523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150691357682973392727521015 226037036524460089091281523)
    ·
      refine ⟨339055554786690133636922285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226037036524460089091281523 339055554786690133636922285)
      ·
        refine ⟨127145833045008800113845857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339055554786690133636922285 127145833045008800113845857)
        ·
          refine ⟨95359374783756600085384393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127145833045008800113845857 95359374783756600085384393)
          ·
            refine ⟨71519531087817450064038295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95359374783756600085384393 71519531087817450064038295)
            ·
              refine ⟨107279296631726175096057443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71519531087817450064038295 107279296631726175096057443)
              ·
                refine ⟨160918944947589262644086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107279296631726175096057443 160918944947589262644086165)
                ·
                  refine ⟨7543075544418246686441539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160918944947589262644086165 7543075544418246686441539)
                  ·
                    refine ⟨11314613316627370029662309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543075544418246686441539 11314613316627370029662309)
                    ·
                      refine ⟨2121489996867631880561683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11314613316627370029662309 2121489996867631880561683)
                      ·
                        rfl

theorem cell23_4131587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_4131587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131587 prefixEnd_4131587 := by exact prefixLift 4131587
  have htrace : WordTrace (prefixWord ++ tailWord_4131587) baseStart_4131587 baseEnd_4131587 := by
    simpa [prefixWord, tailWord_4131587, baseEnd_4131587] using wordTrace_append hprefix tailTrace_4131587
  have hstable : (prefixWord ++ tailWord_4131587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131587).length < 2 ^ (prefixWord ++ tailWord_4131587).sum := by decide
  have hdescent : baseEnd_4131587 < baseStart_4131587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131617 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4131617 : Nat := 118140960795 + 4131617 * 2 ^ 59
def prefixEnd_4131617 : Nat := 4983230072969 + 3 ^ 40 * 4131617 * 2
def baseEnd_4131617 : Nat := 2121505401287266763186545

theorem tailTrace_4131617 : CollatzResearch.WordTrace tailWord_4131617 prefixEnd_4131617 2121505401287266763186545 := by
  unfold tailWord_4131617
  simp only [CollatzResearch.WordTrace]
  refine ⟨150692451872864707851113105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100461634581909805234075403 150692451872864707851113105)
  ·
    refine ⟨113019338904648530888334829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150692451872864707851113105 113019338904648530888334829)
    ·
      refine ⟨42382252089243199083125561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113019338904648530888334829 42382252089243199083125561)
      ·
        refine ⟨31786689066932399312344171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42382252089243199083125561 31786689066932399312344171)
        ·
          refine ⟨47680033600398598968516257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31786689066932399312344171 47680033600398598968516257)
          ·
            refine ⟨35760025200298949226387193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47680033600398598968516257 35760025200298949226387193)
            ·
              refine ⟨26820018900224211919790395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35760025200298949226387193 26820018900224211919790395)
              ·
                refine ⟨40230028350336317879685593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26820018900224211919790395 40230028350336317879685593)
                ·
                  refine ⟨30172521262752238409764195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40230028350336317879685593 30172521262752238409764195)
                  ·
                    refine ⟨45258781894128357614646293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30172521262752238409764195 45258781894128357614646293)
                    ·
                      refine ⟨2121505401287266763186545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45258781894128357614646293 2121505401287266763186545)
                      ·
                        rfl

theorem cell23_4131617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4131617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131617 prefixEnd_4131617 := by exact prefixLift 4131617
  have htrace : WordTrace (prefixWord ++ tailWord_4131617) baseStart_4131617 baseEnd_4131617 := by
    simpa [prefixWord, tailWord_4131617, baseEnd_4131617] using wordTrace_append hprefix tailTrace_4131617
  have hstable : (prefixWord ++ tailWord_4131617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131617).length < 2 ^ (prefixWord ++ tailWord_4131617).sum := by decide
  have hdescent : baseEnd_4131617 < baseStart_4131617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131627 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 6]
def baseStart_4131627 : Nat := 118140960795 + 4131627 * 2 ^ 59
def prefixEnd_4131627 : Nat := 4983230072969 + 3 ^ 40 * 4131627 * 2
def baseEnd_4131627 : Nat := 235723392899312413784611

theorem tailTrace_4131627 : CollatzResearch.WordTrace tailWord_4131627 prefixEnd_4131627 235723392899312413784611 := by
  unfold tailWord_4131627
  simp only [CollatzResearch.WordTrace]
  refine ⟨150692816602828479558977135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100461877735218986372651423 150692816602828479558977135)
  ·
    refine ⟨226039224904242719338465703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150692816602828479558977135 226039224904242719338465703)
    ·
      refine ⟨339058837356364079007698555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226039224904242719338465703 339058837356364079007698555)
      ·
        refine ⟨508588256034546118511547833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339058837356364079007698555 508588256034546118511547833)
        ·
          refine ⟨381441192025909588883660875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508588256034546118511547833 381441192025909588883660875)
          ·
            refine ⟨572161788038864383325491313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381441192025909588883660875 572161788038864383325491313)
            ·
              refine ⟨429121341029148287494118485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572161788038864383325491313 429121341029148287494118485)
              ·
                refine ⟨5028765715185331494071701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 429121341029148287494118485 5028765715185331494071701)
                ·
                  refine ⟨235723392899312413784611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5028765715185331494071701 235723392899312413784611)
                  ·
                    rfl

theorem cell23_4131627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 6].length) (baseStart_4131627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131627 prefixEnd_4131627 := by exact prefixLift 4131627
  have htrace : WordTrace (prefixWord ++ tailWord_4131627) baseStart_4131627 baseEnd_4131627 := by
    simpa [prefixWord, tailWord_4131627, baseEnd_4131627] using wordTrace_append hprefix tailTrace_4131627
  have hstable : (prefixWord ++ tailWord_4131627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131627).length < 2 ^ (prefixWord ++ tailWord_4131627).sum := by decide
  have hdescent : baseEnd_4131627 < baseStart_4131627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131688 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4131688 : Nat := 118140960795 + 4131688 * 2 ^ 59
def prefixEnd_4131688 : Nat := 4983230072969 + 3 ^ 40 * 4131688 * 2
def baseEnd_4131688 : Nat := 2121541858413735985398719

theorem tailTrace_4131688 : CollatzResearch.WordTrace tailWord_4131688 prefixEnd_4131688 2121541858413735985398719 := by
  unfold tailWord_4131688
  simp only [CollatzResearch.WordTrace]
  refine ⟨75347520727803743488473859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100463360970404991317965145 75347520727803743488473859)
  ·
    refine ⟨113021281091705615232710789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75347520727803743488473859 113021281091705615232710789)
    ·
      refine ⟨21191490204694802856133273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113021281091705615232710789 21191490204694802856133273)
      ·
        refine ⟨15893617653521102142099955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21191490204694802856133273 15893617653521102142099955)
        ·
          refine ⟨23840426480281653213149933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15893617653521102142099955 23840426480281653213149933)
          ·
            refine ⟨8940159930105619954931225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23840426480281653213149933 8940159930105619954931225)
            ·
              refine ⟨6705119947579214966198419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940159930105619954931225 6705119947579214966198419)
              ·
                refine ⟨10057679921368822449297629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705119947579214966198419 10057679921368822449297629)
                ·
                  refine ⟨3771629970513308418486611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10057679921368822449297629 3771629970513308418486611)
                  ·
                    refine ⟨5657444955769962627729917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3771629970513308418486611 5657444955769962627729917)
                    ·
                      refine ⟨2121541858413735985398719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657444955769962627729917 2121541858413735985398719)
                      ·
                        rfl

theorem cell23_4131688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4131688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131688 prefixEnd_4131688 := by exact prefixLift 4131688
  have htrace : WordTrace (prefixWord ++ tailWord_4131688) baseStart_4131688 baseEnd_4131688 := by
    simpa [prefixWord, tailWord_4131688, baseEnd_4131688] using wordTrace_append hprefix tailTrace_4131688
  have hstable : (prefixWord ++ tailWord_4131688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131688).length < 2 ^ (prefixWord ++ tailWord_4131688).sum := by decide
  have hdescent : baseEnd_4131688 < baseStart_4131688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131722 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4131722 : Nat := 118140960795 + 4131722 * 2 ^ 59
def prefixEnd_4131722 : Nat := 4983230072969 + 3 ^ 40 * 4131722 * 2
def baseEnd_4131722 : Nat := 2121559316755988852373563

theorem tailTrace_4131722 : CollatzResearch.WordTrace tailWord_4131722 prefixEnd_4131722 2121559316755988852373563 := by
  unfold tailWord_4131722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37674070384371077695921355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100464187691656207189123613 37674070384371077695921355)
  ·
    refine ⟨56511105576556616543882033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37674070384371077695921355 56511105576556616543882033)
    ·
      refine ⟨42383329182417462407911525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56511105576556616543882033 42383329182417462407911525)
      ·
        refine ⟨7946874221703274201483411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42383329182417462407911525 7946874221703274201483411)
        ·
          refine ⟨11920311332554911302225117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946874221703274201483411 11920311332554911302225117)
          ·
            refine ⟨4470116749708091738334419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11920311332554911302225117 4470116749708091738334419)
            ·
              refine ⟨6705175124562137607501629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470116749708091738334419 6705175124562137607501629)
              ·
                refine ⟨2514440671710801602813111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6705175124562137607501629 2514440671710801602813111)
                ·
                  refine ⟨3771661007566202404219667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514440671710801602813111 3771661007566202404219667)
                  ·
                    refine ⟨5657491511349303606329501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3771661007566202404219667 5657491511349303606329501)
                    ·
                      refine ⟨2121559316755988852373563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657491511349303606329501 2121559316755988852373563)
                      ·
                        rfl

theorem cell23_4131722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4131722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131722 prefixEnd_4131722 := by exact prefixLift 4131722
  have htrace : WordTrace (prefixWord ++ tailWord_4131722) baseStart_4131722 baseEnd_4131722 := by
    simpa [prefixWord, tailWord_4131722, baseEnd_4131722] using wordTrace_append hprefix tailTrace_4131722
  have hstable : (prefixWord ++ tailWord_4131722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131722).length < 2 ^ (prefixWord ++ tailWord_4131722).sum := by decide
  have hdescent : baseEnd_4131722 < baseStart_4131722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131724 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_4131724 : Nat := 118140960795 + 4131724 * 2 ^ 59
def prefixEnd_4131724 : Nat := 4983230072969 + 3 ^ 40 * 4131724 * 2
def baseEnd_4131724 : Nat := 2121560343717297844548553

theorem tailTrace_4131724 : CollatzResearch.WordTrace tailWord_4131724 prefixEnd_4131724 2121560343717297844548553 := by
  unfold tailWord_4131724
  simp only [CollatzResearch.WordTrace]
  refine ⟨75348177241738532562629113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100464236322318043416838817 75348177241738532562629113)
  ·
    refine ⟨56511132931303899421971835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75348177241738532562629113 56511132931303899421971835)
    ·
      refine ⟨84766699396955849132957753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56511132931303899421971835 84766699396955849132957753)
      ·
        refine ⟨63575024547716886849718315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84766699396955849132957753 63575024547716886849718315)
        ·
          refine ⟨95362536821575330274577473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63575024547716886849718315 95362536821575330274577473)
          ·
            refine ⟨71521902616181497705933105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95362536821575330274577473 71521902616181497705933105)
            ·
              refine ⟨53641426962136123279449829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71521902616181497705933105 53641426962136123279449829)
              ·
                refine ⟨10057767555400523114896843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53641426962136123279449829 10057767555400523114896843)
                ·
                  refine ⟨15086651333100784672345265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057767555400523114896843 15086651333100784672345265)
                  ·
                    refine ⟨11314988499825588504258949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15086651333100784672345265 11314988499825588504258949)
                    ·
                      refine ⟨2121560343717297844548553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11314988499825588504258949 2121560343717297844548553)
                      ·
                        rfl

theorem cell23_4131724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_4131724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131724 prefixEnd_4131724 := by exact prefixLift 4131724
  have htrace : WordTrace (prefixWord ++ tailWord_4131724) baseStart_4131724 baseEnd_4131724 := by
    simpa [prefixWord, tailWord_4131724, baseEnd_4131724] using wordTrace_append hprefix tailTrace_4131724
  have hstable : (prefixWord ++ tailWord_4131724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131724).length < 2 ^ (prefixWord ++ tailWord_4131724).sum := by decide
  have hdescent : baseEnd_4131724 < baseStart_4131724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131745 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4131745 : Nat := 118140960795 + 4131745 * 2 ^ 59
def prefixEnd_4131745 : Nat := 4983230072969 + 3 ^ 40 * 4131745 * 2
def baseEnd_4131745 : Nat := 2121571126811042262385957

theorem tailTrace_4131745 : CollatzResearch.WordTrace tailWord_4131745 prefixEnd_4131745 2121571126811042262385957 := by
  unfold tailWord_4131745
  simp only [CollatzResearch.WordTrace]
  refine ⟨150697120416400985711772689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100464746944267323807848459 150697120416400985711772689)
  ·
    refine ⟨113022840312300739283829517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150697120416400985711772689 113022840312300739283829517)
    ·
      refine ⟨42383565117112777231436069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113022840312300739283829517 42383565117112777231436069)
      ·
        refine ⟨7946918459458645730894263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42383565117112777231436069 7946918459458645730894263)
        ·
          refine ⟨11920377689187968596341395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946918459458645730894263 11920377689187968596341395)
          ·
            refine ⟨17880566533781952894512093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920377689187968596341395 17880566533781952894512093)
            ·
              refine ⟨6705212450168232335442035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17880566533781952894512093 6705212450168232335442035)
              ·
                refine ⟨10057818675252348503163053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705212450168232335442035 10057818675252348503163053)
                ·
                  refine ⟨3771682003219630688686145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10057818675252348503163053 3771682003219630688686145)
                  ·
                    refine ⟨2828761502414723016514609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771682003219630688686145 2828761502414723016514609)
                    ·
                      refine ⟨2121571126811042262385957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828761502414723016514609 2121571126811042262385957)
                      ·
                        rfl

theorem cell23_4131745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4131745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131745 prefixEnd_4131745 := by exact prefixLift 4131745
  have htrace : WordTrace (prefixWord ++ tailWord_4131745) baseStart_4131745 baseEnd_4131745 := by
    simpa [prefixWord, tailWord_4131745, baseEnd_4131745] using wordTrace_append hprefix tailTrace_4131745
  have hstable : (prefixWord ++ tailWord_4131745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131745).length < 2 ^ (prefixWord ++ tailWord_4131745).sum := by decide
  have hdescent : baseEnd_4131745 < baseStart_4131745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131751 : List Nat := [1, 1, 6, 1, 3, 1, 2, 8]
def baseStart_4131751 : Nat := 118140960795 + 4131751 * 2 ^ 59
def prefixEnd_4131751 : Nat := 4983230072969 + 3 ^ 40 * 4131751 * 2
def baseEnd_4131751 : Nat := 78576822507221082922627

theorem tailTrace_4131751 : CollatzResearch.WordTrace tailWord_4131751 prefixEnd_4131751 78576822507221082922627 := by
  unfold tailWord_4131751
  simp only [CollatzResearch.WordTrace]
  refine ⟨150697339254379248736491107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100464892836252832490994071 150697339254379248736491107)
  ·
    refine ⟨226046008881568873104736661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150697339254379248736491107 226046008881568873104736661)
    ·
      refine ⟨10595906666323540926784531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226046008881568873104736661 10595906666323540926784531)
      ·
        refine ⟨15893859999485311390176797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595906666323540926784531 15893859999485311390176797)
        ·
          refine ⟨5960197499806991771316299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15893859999485311390176797 5960197499806991771316299)
          ·
            refine ⟨8940296249710487656974449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960197499806991771316299 8940296249710487656974449)
            ·
              refine ⟨6705222187282865742730837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940296249710487656974449 6705222187282865742730837)
              ·
                refine ⟨78576822507221082922627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6705222187282865742730837 78576822507221082922627)
                ·
                  rfl

theorem cell23_4131751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 8].length) (baseStart_4131751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131751 prefixEnd_4131751 := by exact prefixLift 4131751
  have htrace : WordTrace (prefixWord ++ tailWord_4131751) baseStart_4131751 baseEnd_4131751 := by
    simpa [prefixWord, tailWord_4131751, baseEnd_4131751] using wordTrace_append hprefix tailTrace_4131751
  have hstable : (prefixWord ++ tailWord_4131751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131751).length < 2 ^ (prefixWord ++ tailWord_4131751).sum := by decide
  have hdescent : baseEnd_4131751 < baseStart_4131751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131789 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4131789 : Nat := 118140960795 + 4131789 * 2 ^ 59
def prefixEnd_4131789 : Nat := 4983230072969 + 3 ^ 40 * 4131789 * 2
def baseEnd_4131789 : Nat := 707197906653280030078585

theorem tailTrace_4131789 : CollatzResearch.WordTrace tailWord_4131789 prefixEnd_4131789 707197906653280030078585 := by
  unfold tailWord_4131789
  simp only [CollatzResearch.WordTrace]
  refine ⟨150698725228241581226374421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100465816818827720817582947 150698725228241581226374421)
  ·
    refine ⟨7064002745073824119986301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150698725228241581226374421 7064002745073824119986301)
    ·
      refine ⟨2649001029402684044994863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7064002745073824119986301 2649001029402684044994863)
      ·
        refine ⟨3973501544104026067492295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649001029402684044994863 3973501544104026067492295)
        ·
          refine ⟨5960252316156039101238443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973501544104026067492295 5960252316156039101238443)
          ·
            refine ⟨8940378474234058651857665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960252316156039101238443 8940378474234058651857665)
            ·
              refine ⟨6705283855675543988893249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940378474234058651857665 6705283855675543988893249)
              ·
                refine ⟨5028962891756657991669937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705283855675543988893249 5028962891756657991669937)
                ·
                  refine ⟨3771722168817493493752453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028962891756657991669937 3771722168817493493752453)
                  ·
                    refine ⟨707197906653280030078585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771722168817493493752453 707197906653280030078585)
                    ·
                      rfl

theorem cell23_4131789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4131789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131789 prefixEnd_4131789 := by exact prefixLift 4131789
  have htrace : WordTrace (prefixWord ++ tailWord_4131789) baseStart_4131789 baseEnd_4131789 := by
    simpa [prefixWord, tailWord_4131789, baseEnd_4131789] using wordTrace_append hprefix tailTrace_4131789
  have hstable : (prefixWord ++ tailWord_4131789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131789).length < 2 ^ (prefixWord ++ tailWord_4131789).sum := by decide
  have hdescent : baseEnd_4131789 < baseStart_4131789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131818 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_4131818 : Nat := 118140960795 + 4131818 * 2 ^ 59
def prefixEnd_4131818 : Nat := 4983230072969 + 3 ^ 40 * 4131818 * 2
def baseEnd_4131818 : Nat := 2121608610898820476773121

theorem tailTrace_4131818 : CollatzResearch.WordTrace tailWord_4131818 prefixEnd_4131818 2121608610898820476773121 := by
  unfold tailWord_4131818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37674945736284129794795027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100466521963424346119453405 37674945736284129794795027)
  ·
    refine ⟨56512418604426194692192541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37674945736284129794795027 56512418604426194692192541)
    ·
      refine ⟨21192156976659823009572203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56512418604426194692192541 21192156976659823009572203)
      ·
        refine ⟨31788235464989734514358305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21192156976659823009572203 31788235464989734514358305)
        ·
          refine ⟨23841176598742300885768729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31788235464989734514358305 23841176598742300885768729)
          ·
            refine ⟨17880882449056725664326547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23841176598742300885768729 17880882449056725664326547)
            ·
              refine ⟨26821323673585088496489821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17880882449056725664326547 26821323673585088496489821)
              ·
                refine ⟨10057996377594408186183683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26821323673585088496489821 10057996377594408186183683)
                ·
                  refine ⟨15086994566391612279275525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057996377594408186183683 15086994566391612279275525)
                  ·
                    refine ⟨2828811481198427302364161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15086994566391612279275525 2828811481198427302364161)
                    ·
                      refine ⟨2121608610898820476773121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828811481198427302364161 2121608610898820476773121)
                      ·
                        rfl

theorem cell23_4131818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_4131818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131818 prefixEnd_4131818 := by exact prefixLift 4131818
  have htrace : WordTrace (prefixWord ++ tailWord_4131818) baseStart_4131818 baseEnd_4131818 := by
    simpa [prefixWord, tailWord_4131818, baseEnd_4131818] using wordTrace_append hprefix tailTrace_4131818
  have hstable : (prefixWord ++ tailWord_4131818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131818).length < 2 ^ (prefixWord ++ tailWord_4131818).sum := by decide
  have hdescent : baseEnd_4131818 < baseStart_4131818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131851 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3]
def baseStart_4131851 : Nat := 118140960795 + 4131851 * 2 ^ 59
def prefixEnd_4131851 : Nat := 4983230072969 + 3 ^ 40 * 4131851 * 2
def baseEnd_4131851 : Nat := 2121625555760418847660469

theorem tailTrace_4131851 : CollatzResearch.WordTrace tailWord_4131851 prefixEnd_4131851 2121625555760418847660469 := by
  unfold tailWord_4131851
  simp only [CollatzResearch.WordTrace]
  refine ⟨150700986554016965815131407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100467324369344643876754271 150700986554016965815131407)
  ·
    refine ⟨226051479831025448722697111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150700986554016965815131407 226051479831025448722697111)
    ·
      refine ⟨339077219746538173084045667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226051479831025448722697111 339077219746538173084045667)
      ·
        refine ⟨508615829619807259626068501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339077219746538173084045667 508615829619807259626068501)
        ·
          refine ⟨23841367013428465294971961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 508615829619807259626068501 23841367013428465294971961)
          ·
            refine ⟨17881025260071348971228971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23841367013428465294971961 17881025260071348971228971)
            ·
              refine ⟨26821537890107023456843457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17881025260071348971228971 26821537890107023456843457)
              ·
                refine ⟨20116153417580267592632593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26821537890107023456843457 20116153417580267592632593)
                ·
                  refine ⟨15087115063185200694474445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20116153417580267592632593 15087115063185200694474445)
                  ·
                    refine ⟨5657668148694450260427917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15087115063185200694474445 5657668148694450260427917)
                    ·
                      refine ⟨2121625555760418847660469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657668148694450260427917 2121625555760418847660469)
                      ·
                        rfl

theorem cell23_4131851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].length) (baseStart_4131851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131851 prefixEnd_4131851 := by exact prefixLift 4131851
  have htrace : WordTrace (prefixWord ++ tailWord_4131851) baseStart_4131851 baseEnd_4131851 := by
    simpa [prefixWord, tailWord_4131851, baseEnd_4131851] using wordTrace_append hprefix tailTrace_4131851
  have hstable : (prefixWord ++ tailWord_4131851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131851).length < 2 ^ (prefixWord ++ tailWord_4131851).sum := by decide
  have hdescent : baseEnd_4131851 < baseStart_4131851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131852 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_4131852 : Nat := 118140960795 + 4131852 * 2 ^ 59
def prefixEnd_4131852 : Nat := 4983230072969 + 3 ^ 40 * 4131852 * 2
def baseEnd_4131852 : Nat := 2121626069241073343747965

theorem tailTrace_4131852 : CollatzResearch.WordTrace tailWord_4131852 prefixEnd_4131852 2121626069241073343747965 := by
  unfold tailWord_4131852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75350511513506671492958905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100467348684675561990611873 75350511513506671492958905)
  ·
    refine ⟨56512883635130003619719179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75350511513506671492958905 56512883635130003619719179)
    ·
      refine ⟨84769325452695005429578769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56512883635130003619719179 84769325452695005429578769)
      ·
        refine ⟨63576994089521254072184077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84769325452695005429578769 63576994089521254072184077)
        ·
          refine ⟨23841372783570470277069029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63576994089521254072184077 23841372783570470277069029)
          ·
            refine ⟨4470257396919463176950443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23841372783570470277069029 4470257396919463176950443)
            ·
              refine ⟨6705386095379194765425665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470257396919463176950443 6705386095379194765425665)
              ·
                refine ⟨5029039571534396074069249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705386095379194765425665 5029039571534396074069249)
                ·
                  refine ⟨3771779678650797055551937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029039571534396074069249 3771779678650797055551937)
                  ·
                    refine ⟨2828834758988097791663953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771779678650797055551937 2828834758988097791663953)
                    ·
                      refine ⟨2121626069241073343747965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828834758988097791663953 2121626069241073343747965)
                      ·
                        rfl

theorem cell23_4131852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_4131852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131852 prefixEnd_4131852 := by exact prefixLift 4131852
  have htrace : WordTrace (prefixWord ++ tailWord_4131852) baseStart_4131852 baseEnd_4131852 := by
    simpa [prefixWord, tailWord_4131852, baseEnd_4131852] using wordTrace_append hprefix tailTrace_4131852
  have hstable : (prefixWord ++ tailWord_4131852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131852).length < 2 ^ (prefixWord ++ tailWord_4131852).sum := by decide
  have hdescent : baseEnd_4131852 < baseStart_4131852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131869 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4131869 : Nat := 118140960795 + 4131869 * 2 ^ 59
def prefixEnd_4131869 : Nat := 4983230072969 + 3 ^ 40 * 4131869 * 2
def baseEnd_4131869 : Nat := 2121634798412199777235387

theorem tailTrace_4131869 : CollatzResearch.WordTrace tailWord_4131869 prefixEnd_4131869 2121634798412199777235387 := by
  unfold tailWord_4131869
  simp only [CollatzResearch.WordTrace]
  refine ⟨150701643067951754889286661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100467762045301169926191107 150701643067951754889286661)
  ·
    refine ⟨28256558075240954041741249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150701643067951754889286661 28256558075240954041741249)
    ·
      refine ⟨21192418556430715531305937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28256558075240954041741249 21192418556430715531305937)
      ·
        refine ⟨15894313917323036648479453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21192418556430715531305937 15894313917323036648479453)
        ·
          refine ⟨5960367718996138743179795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15894313917323036648479453 5960367718996138743179795)
          ·
            refine ⟨8940551578494208114769693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960367718996138743179795 8940551578494208114769693)
            ·
              refine ⟨3352706841935328043038635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940551578494208114769693 3352706841935328043038635)
              ·
                refine ⟨5029060262902992064557953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352706841935328043038635 5029060262902992064557953)
                ·
                  refine ⟨3771795197177244048418465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029060262902992064557953 3771795197177244048418465)
                  ·
                    refine ⟨2828846397882933036313849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771795197177244048418465 2828846397882933036313849)
                    ·
                      refine ⟨2121634798412199777235387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828846397882933036313849 2121634798412199777235387)
                      ·
                        rfl

theorem cell23_4131869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4131869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131869 prefixEnd_4131869 := by exact prefixLift 4131869
  have htrace : WordTrace (prefixWord ++ tailWord_4131869) baseStart_4131869 baseEnd_4131869 := by
    simpa [prefixWord, tailWord_4131869, baseEnd_4131869] using wordTrace_append hprefix tailTrace_4131869
  have hstable : (prefixWord ++ tailWord_4131869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131869).length < 2 ^ (prefixWord ++ tailWord_4131869).sum := by decide
  have hdescent : baseEnd_4131869 < baseStart_4131869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131884 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_4131884 : Nat := 118140960795 + 4131884 * 2 ^ 59
def prefixEnd_4131884 : Nat := 4983230072969 + 3 ^ 40 * 4131884 * 2
def baseEnd_4131884 : Nat := 707214166874005739515939

theorem tailTrace_4131884 : CollatzResearch.WordTrace tailWord_4131884 prefixEnd_4131884 707214166874005739515939 := by
  unfold tailWord_4131884
  simp only [CollatzResearch.WordTrace]
  refine ⟨75351095081448706225541353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100468126775264941634055137 75351095081448706225541353)
  ·
    refine ⟨56513321311086529669156015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75351095081448706225541353 56513321311086529669156015)
    ·
      refine ⟨84769981966629794503734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56513321311086529669156015 84769981966629794503734023)
      ·
        refine ⟨127154972949944691755601035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84769981966629794503734023 127154972949944691755601035)
        ·
          refine ⟨190732459424917037633401553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127154972949944691755601035 190732459424917037633401553)
          ·
            refine ⟨143049344568687778225051165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190732459424917037633401553 143049344568687778225051165)
            ·
              refine ⟨53643504213257916834394187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143049344568687778225051165 53643504213257916834394187)
              ·
                refine ⟨80465256319886875251591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53643504213257916834394187 80465256319886875251591281)
                ·
                  refine ⟨60348942239915156438693461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80465256319886875251591281 60348942239915156438693461)
                  ·
                    refine ⟨707214166874005739515939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60348942239915156438693461 707214166874005739515939)
                    ·
                      rfl

theorem cell23_4131884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_4131884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131884 prefixEnd_4131884 := by exact prefixLift 4131884
  have htrace : WordTrace (prefixWord ++ tailWord_4131884) baseStart_4131884 baseEnd_4131884 := by
    simpa [prefixWord, tailWord_4131884, baseEnd_4131884] using wordTrace_append hprefix tailTrace_4131884
  have hstable : (prefixWord ++ tailWord_4131884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131884).length < 2 ^ (prefixWord ++ tailWord_4131884).sum := by decide
  have hdescent : baseEnd_4131884 < baseStart_4131884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131891 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4]
def baseStart_4131891 : Nat := 118140960795 + 4131891 * 2 ^ 59
def prefixEnd_4131891 : Nat := 4983230072969 + 3 ^ 40 * 4131891 * 2
def baseEnd_4131891 : Nat := 2121646094986598691160285

theorem tailTrace_4131891 : CollatzResearch.WordTrace tailWord_4131891 prefixEnd_4131891 2121646094986598691160285 := by
  unfold tailWord_4131891
  simp only [CollatzResearch.WordTrace]
  refine ⟨150702445473872052646587527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100468296982581368431058351 150702445473872052646587527)
  ·
    refine ⟨226053668210808078969881291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150702445473872052646587527 226053668210808078969881291)
    ·
      refine ⟨339080502316212118454821937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226053668210808078969881291 339080502316212118454821937)
      ·
        refine ⟨254310376737159088841116453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339080502316212118454821937 254310376737159088841116453)
        ·
          refine ⟨47683195638217329157709335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254310376737159088841116453 47683195638217329157709335)
          ·
            refine ⟨71524793457325993736564003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47683195638217329157709335 71524793457325993736564003)
            ·
              refine ⟨107287190185988990604846005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71524793457325993736564003 107287190185988990604846005)
              ·
                refine ⟨10058174079936467869204313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107287190185988990604846005 10058174079936467869204313)
                ·
                  refine ⟨7543630559952350901903235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10058174079936467869204313 7543630559952350901903235)
                  ·
                    refine ⟨11315445839928526352854853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543630559952350901903235 11315445839928526352854853)
                    ·
                      refine ⟨2121646094986598691160285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11315445839928526352854853 2121646094986598691160285)
                      ·
                        rfl

theorem cell23_4131891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_4131891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131891 prefixEnd_4131891 := by exact prefixLift 4131891
  have htrace : WordTrace (prefixWord ++ tailWord_4131891) baseStart_4131891 baseEnd_4131891 := by
    simpa [prefixWord, tailWord_4131891, baseEnd_4131891] using wordTrace_append hprefix tailTrace_4131891
  have hstable : (prefixWord ++ tailWord_4131891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131891).length < 2 ^ (prefixWord ++ tailWord_4131891).sum := by decide
  have hdescent : baseEnd_4131891 < baseStart_4131891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131892 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 5]
def baseStart_4131892 : Nat := 118140960795 + 4131892 * 2 ^ 59
def prefixEnd_4131892 : Nat := 4983230072969 + 3 ^ 40 * 4131892 * 2
def baseEnd_4131892 : Nat := 235738512051917020805309

theorem tailTrace_4131892 : CollatzResearch.WordTrace tailWord_4131892 prefixEnd_4131892 235738512051917020805309 := by
  unfold tailWord_4131892
  simp only [CollatzResearch.WordTrace]
  refine ⟨75351240973434214908686965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100468321297912286544915953 75351240973434214908686965)
  ·
    refine ⟨7064178841259457647689403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75351240973434214908686965 7064178841259457647689403)
    ·
      refine ⟨10596268261889186471534105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064178841259457647689403 10596268261889186471534105)
      ·
        refine ⟨7947201196416889853650579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10596268261889186471534105 7947201196416889853650579)
        ·
          refine ⟨11920801794625334780475869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947201196416889853650579 11920801794625334780475869)
          ·
            refine ⟨4470300672984500542678451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11920801794625334780475869 4470300672984500542678451)
            ·
              refine ⟨6705451009476750814017677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470300672984500542678451 6705451009476750814017677)
              ·
                refine ⟨2514544128553781555256629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6705451009476750814017677 2514544128553781555256629)
                ·
                  refine ⟨235738512051917020805309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514544128553781555256629 235738512051917020805309)
                  ·
                    rfl

theorem cell23_4131892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_4131892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131892 prefixEnd_4131892 := by exact prefixLift 4131892
  have htrace : WordTrace (prefixWord ++ tailWord_4131892) baseStart_4131892 baseEnd_4131892 := by
    simpa [prefixWord, tailWord_4131892, baseEnd_4131892] using wordTrace_append hprefix tailTrace_4131892
  have hstable : (prefixWord ++ tailWord_4131892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131892).length < 2 ^ (prefixWord ++ tailWord_4131892).sum := by decide
  have hdescent : baseEnd_4131892 < baseStart_4131892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131969 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4131969 : Nat := 118140960795 + 4131969 * 2 ^ 59
def prefixEnd_4131969 : Nat := 4983230072969 + 3 ^ 40 * 4131969 * 2
def baseEnd_4131969 : Nat := 707228715492549795328309

theorem tailTrace_4131969 : CollatzResearch.WordTrace tailWord_4131969 prefixEnd_4131969 707228715492549795328309 := by
  unfold tailWord_4131969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150705290367589471967926961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100470193578392981311951307 150705290367589471967926961)
  ·
    refine ⟨113028967775692103975945221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150705290367589471967926961 113028967775692103975945221)
    ·
      refine ⟨21192931457942269495489729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113028967775692103975945221 21192931457942269495489729)
      ·
        refine ⟨15894698593456702121617297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21192931457942269495489729 15894698593456702121617297)
        ·
          refine ⟨11921023945092526591212973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15894698593456702121617297 11921023945092526591212973)
          ·
            refine ⟨4470383979409697471704865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11921023945092526591212973 4470383979409697471704865)
            ·
              refine ⟨3352787984557273103778649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470383979409697471704865 3352787984557273103778649)
              ·
                refine ⟨2514590988417954827833987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352787984557273103778649 2514590988417954827833987)
                ·
                  refine ⟨3771886482626932241750981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514590988417954827833987 3771886482626932241750981)
                  ·
                    refine ⟨707228715492549795328309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771886482626932241750981 707228715492549795328309)
                    ·
                      rfl

theorem cell23_4131969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4131969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4131969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4131969 prefixEnd_4131969 := by exact prefixLift 4131969
  have htrace : WordTrace (prefixWord ++ tailWord_4131969) baseStart_4131969 baseEnd_4131969 := by
    simpa [prefixWord, tailWord_4131969, baseEnd_4131969] using wordTrace_append hprefix tailTrace_4131969
  have hstable : (prefixWord ++ tailWord_4131969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131969).length < 2 ^ (prefixWord ++ tailWord_4131969).sum := by decide
  have hdescent : baseEnd_4131969 < baseStart_4131969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132002 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4132002 : Nat := 118140960795 + 4132002 * 2 ^ 59
def prefixEnd_4132002 : Nat := 4983230072969 + 3 ^ 40 * 4132002 * 2
def baseEnd_4132002 : Nat := 2121703091339247756872275

theorem tailTrace_4132002 : CollatzResearch.WordTrace tailWord_4132002 prefixEnd_4132002 2121703091339247756872275 := by
  unfold tailWord_4132002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37676623494117479650969565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100470995984313279069252173 37676623494117479650969565)
  ·
    refine ⟨14128733810294054869113587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37676623494117479650969565 14128733810294054869113587)
    ·
      refine ⟨21193100715441082303670381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128733810294054869113587 21193100715441082303670381)
      ·
        refine ⟨7947412768290405863876393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21193100715441082303670381 7947412768290405863876393)
        ·
          refine ⟨5960559576217804397907295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7947412768290405863876393 5960559576217804397907295)
          ·
            refine ⟨8940839364326706596860943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960559576217804397907295 8940839364326706596860943)
            ·
              refine ⟨13411259046490059895291415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940839364326706596860943 13411259046490059895291415)
              ·
                refine ⟨20116888569735089842937123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13411259046490059895291415 20116888569735089842937123)
                ·
                  refine ⟨30175332854602634764405685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20116888569735089842937123 30175332854602634764405685)
                  ·
                    refine ⟨2828937455118997009163033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30175332854602634764405685 2828937455118997009163033)
                    ·
                      refine ⟨2121703091339247756872275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2828937455118997009163033 2121703091339247756872275)
                      ·
                        rfl

theorem cell23_4132002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4132002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132002 prefixEnd_4132002 := by exact prefixLift 4132002
  have htrace : WordTrace (prefixWord ++ tailWord_4132002) baseStart_4132002 baseEnd_4132002 := by
    simpa [prefixWord, tailWord_4132002, baseEnd_4132002] using wordTrace_append hprefix tailTrace_4132002
  have hstable : (prefixWord ++ tailWord_4132002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132002).length < 2 ^ (prefixWord ++ tailWord_4132002).sum := by decide
  have hdescent : baseEnd_4132002 < baseStart_4132002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132015 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 1, 1, 4]
def baseStart_4132015 : Nat := 118140960795 + 4132015 * 2 ^ 59
def prefixEnd_4132015 : Nat := 4983230072969 + 3 ^ 40 * 4132015 * 2
def baseEnd_4132015 : Nat := 2121709766587756206009715

theorem tailTrace_4132015 : CollatzResearch.WordTrace tailWord_4132015 prefixEnd_4132015 2121709766587756206009715 := by
  unfold tailWord_4132015
  simp only [CollatzResearch.WordTrace]
  refine ⟨150706968125422821824101499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100471312083615214549400999 150706968125422821824101499)
  ·
    refine ⟨226060452188134232736152249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150706968125422821824101499 226060452188134232736152249)
    ·
      refine ⟨169545339141100674552114187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226060452188134232736152249 169545339141100674552114187)
      ·
        refine ⟨254318008711651011828171281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169545339141100674552114187 254318008711651011828171281)
        ·
          refine ⟨190738506533738258871128461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254318008711651011828171281 190738506533738258871128461)
          ·
            refine ⟨71526939950151847076673173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190738506533738258871128461 71526939950151847076673173)
            ·
              refine ⟨3352825310163367831719055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71526939950151847076673173 3352825310163367831719055)
              ·
                refine ⟨5029237965245051747578583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352825310163367831719055 5029237965245051747578583)
                ·
                  refine ⟨7543856947867577621367875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029237965245051747578583 7543856947867577621367875)
                  ·
                    refine ⟨11315785421801366432051813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543856947867577621367875 11315785421801366432051813)
                    ·
                      refine ⟨2121709766587756206009715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11315785421801366432051813 2121709766587756206009715)
                      ·
                        rfl

theorem cell23_4132015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 1, 4].length) (baseStart_4132015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132015 prefixEnd_4132015 := by exact prefixLift 4132015
  have htrace : WordTrace (prefixWord ++ tailWord_4132015) baseStart_4132015 baseEnd_4132015 := by
    simpa [prefixWord, tailWord_4132015, baseEnd_4132015] using wordTrace_append hprefix tailTrace_4132015
  have hstable : (prefixWord ++ tailWord_4132015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132015).length < 2 ^ (prefixWord ++ tailWord_4132015).sum := by decide
  have hdescent : baseEnd_4132015 < baseStart_4132015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132025 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_4132025 : Nat := 118140960795 + 4132025 * 2 ^ 59
def prefixEnd_4132025 : Nat := 4983230072969 + 3 ^ 40 * 4132025 * 2
def baseEnd_4132025 : Nat := 707238300464767055628223

theorem tailTrace_4132025 : CollatzResearch.WordTrace tailWord_4132025 prefixEnd_4132025 707238300464767055628223 := by
  unfold tailWord_4132025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150707332855386593531965529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100471555236924395687977019 150707332855386593531965529)
  ·
    refine ⟨113030499641539945148974147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150707332855386593531965529 113030499641539945148974147)
    ·
      refine ⟨169545749462309917723461221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113030499641539945148974147 169545749462309917723461221)
      ·
        refine ⟨31789828024183109573148979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169545749462309917723461221 31789828024183109573148979)
        ·
          refine ⟨47684742036274664359723469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31789828024183109573148979 47684742036274664359723469)
          ·
            refine ⟨17881778263602999134896301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47684742036274664359723469 17881778263602999134896301)
            ·
              refine ⟨6705666848851124675586113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17881778263602999134896301 6705666848851124675586113)
              ·
                refine ⟨5029250136638343506689585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705666848851124675586113 5029250136638343506689585)
                ·
                  refine ⟨3771937602478757630017189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029250136638343506689585 3771937602478757630017189)
                  ·
                    refine ⟨707238300464767055628223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771937602478757630017189 707238300464767055628223)
                    ·
                      rfl

theorem cell23_4132025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_4132025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132025 prefixEnd_4132025 := by exact prefixLift 4132025
  have htrace : WordTrace (prefixWord ++ tailWord_4132025) baseStart_4132025 baseEnd_4132025 := by
    simpa [prefixWord, tailWord_4132025, baseEnd_4132025] using wordTrace_append hprefix tailTrace_4132025
  have hstable : (prefixWord ++ tailWord_4132025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132025).length < 2 ^ (prefixWord ++ tailWord_4132025).sum := by decide
  have hdescent : baseEnd_4132025 < baseStart_4132025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132042 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_4132042 : Nat := 118140960795 + 4132042 * 2 ^ 59
def prefixEnd_4132042 : Nat := 4983230072969 + 3 ^ 40 * 4132042 * 2
def baseEnd_4132042 : Nat := 707241210188475866790697

theorem tailTrace_4132042 : CollatzResearch.WordTrace tailWord_4132042 prefixEnd_4132042 707241210188475866790697 := by
  unfold tailWord_4132042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37676988224081251358833595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100471968597550003623556253 37676988224081251358833595)
  ·
    refine ⟨56515482336121877038250393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37676988224081251358833595 56515482336121877038250393)
    ·
      refine ⟨42386611752091407778687795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56515482336121877038250393 42386611752091407778687795)
      ·
        refine ⟨63579917628137111668031693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42386611752091407778687795 63579917628137111668031693)
        ·
          refine ⟨23842469110551416875511885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63579917628137111668031693 23842469110551416875511885)
          ·
            refine ⟨8940925916456781328316957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23842469110551416875511885 8940925916456781328316957)
            ·
              refine ⟨3352847218671292998118859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940925916456781328316957 3352847218671292998118859)
              ·
                refine ⟨5029270828006939497178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352847218671292998118859 5029270828006939497178289)
                ·
                  refine ⟨3771953121005204622883717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029270828006939497178289 3771953121005204622883717)
                  ·
                    refine ⟨707241210188475866790697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771953121005204622883717 707241210188475866790697)
                    ·
                      rfl

theorem cell23_4132042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_4132042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132042 prefixEnd_4132042 := by exact prefixLift 4132042
  have htrace : WordTrace (prefixWord ++ tailWord_4132042) baseStart_4132042 baseEnd_4132042 := by
    simpa [prefixWord, tailWord_4132042, baseEnd_4132042] using wordTrace_append hprefix tailTrace_4132042
  have hstable : (prefixWord ++ tailWord_4132042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132042).length < 2 ^ (prefixWord ++ tailWord_4132042).sum := by decide
  have hdescent : baseEnd_4132042 < baseStart_4132042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132065 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_4132065 : Nat := 118140960795 + 4132065 * 2 ^ 59
def prefixEnd_4132065 : Nat := 4983230072969 + 3 ^ 40 * 4132065 * 2
def baseEnd_4132065 : Nat := 2121735440620481010384485

theorem tailTrace_4132065 : CollatzResearch.WordTrace tailWord_4132065 prefixEnd_4132065 2121735440620481010384485 := by
  unfold tailWord_4132065
  simp only [CollatzResearch.WordTrace]
  refine ⟨150708791775241680363421649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100472527850161120242281099 150708791775241680363421649)
  ·
    refine ⟨113031593831431260272566237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150708791775241680363421649 113031593831431260272566237)
    ·
      refine ⟨42386847686786722602212339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113031593831431260272566237 42386847686786722602212339)
      ·
        refine ⟨63580271530180083903318509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42386847686786722602212339 63580271530180083903318509)
        ·
          refine ⟨23842601823817531463744441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63580271530180083903318509 23842601823817531463744441)
          ·
            refine ⟨17881951367863148597808331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23842601823817531463744441 17881951367863148597808331)
            ·
              refine ⟨26822927051794722896712497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17881951367863148597808331 26822927051794722896712497)
              ·
                refine ⟨20117195288846042172534373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26822927051794722896712497 20117195288846042172534373)
                ·
                  refine ⟨3771974116658632907350195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20117195288846042172534373 3771974116658632907350195)
                  ·
                    refine ⟨5657961174987949361025293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3771974116658632907350195 5657961174987949361025293)
                    ·
                      refine ⟨2121735440620481010384485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5657961174987949361025293 2121735440620481010384485)
                      ·
                        rfl

theorem cell23_4132065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_4132065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132065 prefixEnd_4132065 := by exact prefixLift 4132065
  have htrace : WordTrace (prefixWord ++ tailWord_4132065) baseStart_4132065 baseEnd_4132065 := by
    simpa [prefixWord, tailWord_4132065, baseEnd_4132065] using wordTrace_append hprefix tailTrace_4132065
  have hstable : (prefixWord ++ tailWord_4132065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132065).length < 2 ^ (prefixWord ++ tailWord_4132065).sum := by decide
  have hdescent : baseEnd_4132065 < baseStart_4132065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132099 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 2, 1, 3]
def baseStart_4132099 : Nat := 118140960795 + 4132099 * 2 ^ 59
def prefixEnd_4132099 : Nat := 4983230072969 + 3 ^ 40 * 4132099 * 2
def baseEnd_4132099 : Nat := 2121752898962733877359329

theorem tailTrace_4132099 : CollatzResearch.WordTrace tailWord_4132099 prefixEnd_4132099 2121752898962733877359329 := by
  unfold tailWord_4132099
  simp only [CollatzResearch.WordTrace]
  refine ⟨150710031857118504170159351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100473354571412336113439567 150710031857118504170159351)
  ·
    refine ⟨226065047785677756255239027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150710031857118504170159351 226065047785677756255239027)
    ·
      refine ⟨339097571678516634382858541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226065047785677756255239027 339097571678516634382858541)
      ·
        refine ⟨127161589379443737893571953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339097571678516634382858541 127161589379443737893571953)
        ·
          refine ⟨95371192034582803420178965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127161589379443737893571953 95371192034582803420178965)
          ·
            refine ⟨4470524626621068910320889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95371192034582803420178965 4470524626621068910320889)
            ·
              refine ⟨3352893469965801682740667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470524626621068910320889 3352893469965801682740667)
              ·
                refine ⟨5029340204948702524111001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352893469965801682740667 5029340204948702524111001)
                ·
                  refine ⟨3772005153711526893083251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029340204948702524111001 3772005153711526893083251)
                  ·
                    refine ⟨5658007730567290339624877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772005153711526893083251 5658007730567290339624877)
                    ·
                      refine ⟨2121752898962733877359329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658007730567290339624877 2121752898962733877359329)
                      ·
                        rfl

theorem cell23_4132099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_4132099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132099 prefixEnd_4132099 := by exact prefixLift 4132099
  have htrace : WordTrace (prefixWord ++ tailWord_4132099) baseStart_4132099 baseEnd_4132099 := by
    simpa [prefixWord, tailWord_4132099, baseEnd_4132099] using wordTrace_append hprefix tailTrace_4132099
  have hstable : (prefixWord ++ tailWord_4132099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132099).length < 2 ^ (prefixWord ++ tailWord_4132099).sum := by decide
  have hdescent : baseEnd_4132099 < baseStart_4132099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132105 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 4, 2]
def baseStart_4132105 : Nat := 118140960795 + 4132105 * 2 ^ 59
def prefixEnd_4132105 : Nat := 4983230072969 + 3 ^ 40 * 4132105 * 2
def baseEnd_4132105 : Nat := 2121755979846660853884301

theorem tailTrace_4132105 : CollatzResearch.WordTrace tailWord_4132105 prefixEnd_4132105 2121755979846660853884301 := by
  unfold tailWord_4132105
  simp only [CollatzResearch.WordTrace]
  refine ⟨150710250695096767194877769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100473500463397844796585179 150710250695096767194877769)
  ·
    refine ⟨113032688021322575396158327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150710250695096767194877769 113032688021322575396158327)
    ·
      refine ⟨169549032031983863094237491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113032688021322575396158327 169549032031983863094237491)
      ·
        refine ⟨254323548047975794641356237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169549032031983863094237491 254323548047975794641356237)
        ·
          refine ⟨95371330517990922990508589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254323548047975794641356237 95371330517990922990508589)
          ·
            refine ⟨35764248944246596121440721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95371330517990922990508589 35764248944246596121440721)
            ·
              refine ⟨26823186708184947091080541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35764248944246596121440721 26823186708184947091080541)
              ·
                refine ⟨10058695015569355159155203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26823186708184947091080541 10058695015569355159155203)
                ·
                  refine ⟨15088042523354032738732805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058695015569355159155203 15088042523354032738732805)
                  ·
                    refine ⟨2829007973128881138512401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15088042523354032738732805 2829007973128881138512401)
                    ·
                      refine ⟨2121755979846660853884301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829007973128881138512401 2121755979846660853884301)
                      ·
                        rfl

theorem cell23_4132105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4, 2].length) (baseStart_4132105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132105 prefixEnd_4132105 := by exact prefixLift 4132105
  have htrace : WordTrace (prefixWord ++ tailWord_4132105) baseStart_4132105 baseEnd_4132105 := by
    simpa [prefixWord, tailWord_4132105, baseEnd_4132105] using wordTrace_append hprefix tailTrace_4132105
  have hstable : (prefixWord ++ tailWord_4132105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132105).length < 2 ^ (prefixWord ++ tailWord_4132105).sum := by decide
  have hdescent : baseEnd_4132105 < baseStart_4132105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132108 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_4132108 : Nat := 118140960795 + 4132108 * 2 ^ 59
def prefixEnd_4132108 : Nat := 4983230072969 + 3 ^ 40 * 4132108 * 2
def baseEnd_4132108 : Nat := 2121757520288624342146787

theorem tailTrace_4132108 : CollatzResearch.WordTrace tailWord_4132108 prefixEnd_4132108 2121757520288624342146787 := by
  unfold tailWord_4132108
  simp only [CollatzResearch.WordTrace]
  refine ⟨75355180057042949353618489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100473573409390599138157985 75355180057042949353618489)
  ·
    refine ⟨56516385042782212015213867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75355180057042949353618489 56516385042782212015213867)
    ·
      refine ⟨84774577564173318022820801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56516385042782212015213867 84774577564173318022820801)
      ·
        refine ⟨63580933173129988517115601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84774577564173318022820801 63580933173129988517115601)
        ·
          refine ⟨47685699879847491387836701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63580933173129988517115601 47685699879847491387836701)
          ·
            refine ⟨17882137454942809270438763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47685699879847491387836701 17882137454942809270438763)
            ·
              refine ⟨26823206182414213905658145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882137454942809270438763 26823206182414213905658145)
              ·
                refine ⟨20117404636810660429243609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26823206182414213905658145 20117404636810660429243609)
                ·
                  refine ⟨15088053477607995321932707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20117404636810660429243609 15088053477607995321932707)
                  ·
                    refine ⟨22632080216411992982899061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15088053477607995321932707 22632080216411992982899061)
                    ·
                      refine ⟨2121757520288624342146787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22632080216411992982899061 2121757520288624342146787)
                      ·
                        rfl

theorem cell23_4132108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_4132108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132108 prefixEnd_4132108 := by exact prefixLift 4132108
  have htrace : WordTrace (prefixWord ++ tailWord_4132108) baseStart_4132108 baseEnd_4132108 := by
    simpa [prefixWord, tailWord_4132108, baseEnd_4132108] using wordTrace_append hprefix tailTrace_4132108
  have hstable : (prefixWord ++ tailWord_4132108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132108).length < 2 ^ (prefixWord ++ tailWord_4132108).sum := by decide
  have hdescent : baseEnd_4132108 < baseStart_4132108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132122 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_4132122 : Nat := 118140960795 + 4132122 * 2 ^ 59
def prefixEnd_4132122 : Nat := 4983230072969 + 3 ^ 40 * 4132122 * 2
def baseEnd_4132122 : Nat := 2121764709017787287371723

theorem tailTrace_4132122 : CollatzResearch.WordTrace tailWord_4132122 prefixEnd_4132122 2121764709017787287371723 := by
  unfold tailWord_4132122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37677717684008794774561655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100473913824023452732164413 37677717684008794774561655)
  ·
    refine ⟨56516576526013192161842483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37677717684008794774561655 56516576526013192161842483)
    ·
      refine ⟨84774864789019788242763725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56516576526013192161842483 84774864789019788242763725)
      ·
        refine ⟨31790574295882420591036397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84774864789019788242763725 31790574295882420591036397)
        ·
          refine ⟨11921465360955907721638649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31790574295882420591036397 11921465360955907721638649)
          ·
            refine ⟨8941099020716930791228987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11921465360955907721638649 8941099020716930791228987)
            ·
              refine ⟨13411648531075396186843481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941099020716930791228987 13411648531075396186843481)
              ·
                refine ⟨10058736398306547140132611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13411648531075396186843481 10058736398306547140132611)
                ·
                  refine ⟨15088104597459820710198917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058736398306547140132611 15088104597459820710198917)
                  ·
                    refine ⟨2829019612023716383162297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15088104597459820710198917 2829019612023716383162297)
                    ·
                      refine ⟨2121764709017787287371723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829019612023716383162297 2121764709017787287371723)
                      ·
                        rfl

theorem cell23_4132122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_4132122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132122 prefixEnd_4132122 := by exact prefixLift 4132122
  have htrace : WordTrace (prefixWord ++ tailWord_4132122) baseStart_4132122 baseEnd_4132122 := by
    simpa [prefixWord, tailWord_4132122, baseEnd_4132122] using wordTrace_append hprefix tailTrace_4132122
  have hstable : (prefixWord ++ tailWord_4132122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132122).length < 2 ^ (prefixWord ++ tailWord_4132122).sum := by decide
  have hdescent : baseEnd_4132122 < baseStart_4132122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132125 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4132125 : Nat := 118140960795 + 4132125 * 2 ^ 59
def prefixEnd_4132125 : Nat := 4983230072969 + 3 ^ 40 * 4132125 * 2
def baseEnd_4132125 : Nat := 2121766249459750775634209

theorem tailTrace_4132125 : CollatzResearch.WordTrace tailWord_4132125 prefixEnd_4132125 2121766249459750775634209 := by
  unfold tailWord_4132125
  simp only [CollatzResearch.WordTrace]
  refine ⟨150710980155024310610605829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100473986770016207073737219 150710980155024310610605829)
  ·
    refine ⟨28258308779067058239488593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150710980155024310610605829 28258308779067058239488593)
    ·
      refine ⟨21193731584300293679616445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28258308779067058239488593 21193731584300293679616445)
      ·
        refine ⟨7947649344112610129856167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21193731584300293679616445 7947649344112610129856167)
        ·
          refine ⟨11921474016168915194784251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947649344112610129856167 11921474016168915194784251)
          ·
            refine ⟨17882211024253372792176377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921474016168915194784251 17882211024253372792176377)
            ·
              refine ⟨13411658268190029594132283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17882211024253372792176377 13411658268190029594132283)
              ·
                refine ⟨20117487402285044391198425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13411658268190029594132283 20117487402285044391198425)
                ·
                  refine ⟨15088115551713783293398819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20117487402285044391198425 15088115551713783293398819)
                  ·
                    refine ⟨22632173327570674940098229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15088115551713783293398819 22632173327570674940098229)
                    ·
                      refine ⟨2121766249459750775634209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22632173327570674940098229 2121766249459750775634209)
                      ·
                        rfl

theorem cell23_4132125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4132125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132125 prefixEnd_4132125 := by exact prefixLift 4132125
  have htrace : WordTrace (prefixWord ++ tailWord_4132125) baseStart_4132125 baseEnd_4132125 := by
    simpa [prefixWord, tailWord_4132125, baseEnd_4132125] using wordTrace_append hprefix tailTrace_4132125
  have hstable : (prefixWord ++ tailWord_4132125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132125).length < 2 ^ (prefixWord ++ tailWord_4132125).sum := by decide
  have hdescent : baseEnd_4132125 < baseStart_4132125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132208 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_4132208 : Nat := 118140960795 + 4132208 * 2 ^ 59
def prefixEnd_4132208 : Nat := 4983230072969 + 3 ^ 40 * 4132208 * 2
def baseEnd_4132208 : Nat := 2121808868354073950896327

theorem tailTrace_4132208 : CollatzResearch.WordTrace tailWord_4132208 prefixEnd_4132208 2121808868354073950896327 := by
  unfold tailWord_4132208
  simp only [CollatzResearch.WordTrace]
  refine ⟨75357003706861807892938639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100476004942482410523918185 75357003706861807892938639)
  ·
    refine ⟨113035505560292711839407959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75357003706861807892938639 113035505560292711839407959)
    ·
      refine ⟨169553258340439067759111939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113035505560292711839407959 169553258340439067759111939)
      ·
        refine ⟨254329887510658601638667909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169553258340439067759111939 254329887510658601638667909)
        ·
          refine ⟨47686853908248487807250233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254329887510658601638667909 47686853908248487807250233)
          ·
            refine ⟨35765140431186365855437675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47686853908248487807250233 35765140431186365855437675)
            ·
              refine ⟨53647710646779548783156513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35765140431186365855437675 53647710646779548783156513)
              ·
                refine ⟨40235782985084661587367385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53647710646779548783156513 40235782985084661587367385)
                ·
                  refine ⟨30176837238813496190525539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40235782985084661587367385 30176837238813496190525539)
                  ·
                    refine ⟨45265255858220244285788309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30176837238813496190525539 45265255858220244285788309)
                    ·
                      refine ⟨2121808868354073950896327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45265255858220244285788309 2121808868354073950896327)
                      ·
                        rfl

theorem cell23_4132208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_4132208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132208 prefixEnd_4132208 := by exact prefixLift 4132208
  have htrace : WordTrace (prefixWord ++ tailWord_4132208) baseStart_4132208 baseEnd_4132208 := by
    simpa [prefixWord, tailWord_4132208, baseEnd_4132208] using wordTrace_append hprefix tailTrace_4132208
  have hstable : (prefixWord ++ tailWord_4132208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132208).length < 2 ^ (prefixWord ++ tailWord_4132208).sum := by decide
  have hdescent : baseEnd_4132208 < baseStart_4132208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132269 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 6]
def baseStart_4132269 : Nat := 118140960795 + 4132269 * 2 ^ 59
def prefixEnd_4132269 : Nat := 4983230072969 + 3 ^ 40 * 4132269 * 2
def baseEnd_4132269 : Nat := 235760021185999801359283

theorem tailTrace_4132269 : CollatzResearch.WordTrace tailWord_4132269 prefixEnd_4132269 235760021185999801359283 := by
  unfold tailWord_4132269
  simp only [CollatzResearch.WordTrace]
  refine ⟨150716232266502623203847861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100477488177668415469231907 150716232266502623203847861)
  ·
    refine ⟨14129646774984620925360737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150716232266502623203847861 14129646774984620925360737)
    ·
      refine ⟨10597235081238465694020553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14129646774984620925360737 10597235081238465694020553)
      ·
        refine ⟨7947926310928849270515415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10597235081238465694020553 7947926310928849270515415)
        ·
          refine ⟨11921889466393273905773123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947926310928849270515415 11921889466393273905773123)
          ·
            refine ⟨17882834199589910858659685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921889466393273905773123 17882834199589910858659685)
            ·
              refine ⟨3353031412423108285998691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17882834199589910858659685 3353031412423108285998691)
              ·
                refine ⟨5029547118634662428998037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353031412423108285998691 5029547118634662428998037)
                ·
                  refine ⟨235760021185999801359283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5029547118634662428998037 235760021185999801359283)
                  ·
                    rfl

theorem cell23_4132269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_4132269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132269 prefixEnd_4132269 := by exact prefixLift 4132269
  have htrace : WordTrace (prefixWord ++ tailWord_4132269) baseStart_4132269 baseEnd_4132269 := by
    simpa [prefixWord, tailWord_4132269, baseEnd_4132269] using wordTrace_append hprefix tailTrace_4132269
  have hstable : (prefixWord ++ tailWord_4132269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132269).length < 2 ^ (prefixWord ++ tailWord_4132269).sum := by decide
  have hdescent : baseEnd_4132269 < baseStart_4132269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132295 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 6]
def baseStart_4132295 : Nat := 118140960795 + 4132295 * 2 ^ 59
def prefixEnd_4132295 : Nat := 4983230072969 + 3 ^ 40 * 4132295 * 2
def baseEnd_4132295 : Nat := 707284513723671703502809

theorem tailTrace_4132295 : CollatzResearch.WordTrace tailWord_4132295 prefixEnd_4132295 707284513723671703502809 := by
  unfold tailWord_4132295
  simp only [CollatzResearch.WordTrace]
  refine ⟨150717180564408429644294339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100478120376272286429529559 150717180564408429644294339)
  ·
    refine ⟨226075770846612644466441509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150717180564408429644294339 226075770846612644466441509)
    ·
      refine ⟨42389207033739870837457783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226075770846612644466441509 42389207033739870837457783)
      ·
        refine ⟨63583810550609806256186675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42389207033739870837457783 63583810550609806256186675)
        ·
          refine ⟨95375715825914709384280013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63583810550609806256186675 95375715825914709384280013)
          ·
            refine ⟨35765893434718016019105005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95375715825914709384280013 35765893434718016019105005)
            ·
              refine ⟨13412210038019256007164377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35765893434718016019105005 13412210038019256007164377)
              ·
                refine ⟨10059157528514442005373283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13412210038019256007164377 10059157528514442005373283)
                ·
                  refine ⟨15088736292771663008059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059157528514442005373283 15088736292771663008059925)
                  ·
                    refine ⟨707284513723671703502809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15088736292771663008059925 707284513723671703502809)
                    ·
                      rfl

theorem cell23_4132295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_4132295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132295 prefixEnd_4132295 := by exact prefixLift 4132295
  have htrace : WordTrace (prefixWord ++ tailWord_4132295) baseStart_4132295 baseEnd_4132295 := by
    simpa [prefixWord, tailWord_4132295, baseEnd_4132295] using wordTrace_append hprefix tailTrace_4132295
  have hstable : (prefixWord ++ tailWord_4132295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132295).length < 2 ^ (prefixWord ++ tailWord_4132295).sum := by decide
  have hdescent : baseEnd_4132295 < baseStart_4132295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132302 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_4132302 : Nat := 118140960795 + 4132302 * 2 ^ 59
def prefixEnd_4132302 : Nat := 4983230072969 + 3 ^ 40 * 4132302 * 2
def baseEnd_4132302 : Nat := 2121857135535596583120895

theorem tailTrace_4132302 : CollatzResearch.WordTrace tailWord_4132302 prefixEnd_4132302 2121857135535596583120895 := by
  unfold tailWord_4132302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839679484422883729974895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100478290583588713226532773 18839679484422883729974895)
  ·
    refine ⟨28259519226634325594962343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18839679484422883729974895 28259519226634325594962343)
    ·
      refine ⟨42389278839951488392443515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28259519226634325594962343 42389278839951488392443515)
      ·
        refine ⟨63583918259927232588665273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42389278839951488392443515 63583918259927232588665273)
        ·
          refine ⟨47687938694945424441498955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63583918259927232588665273 47687938694945424441498955)
          ·
            refine ⟨71531908042418136662248433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47687938694945424441498955 71531908042418136662248433)
            ·
              refine ⟨53648931031813602496686325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71531908042418136662248433 53648931031813602496686325)
              ·
                refine ⟨5029587284232525234064343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53648931031813602496686325 5029587284232525234064343)
                ·
                  refine ⟨7544380926348787851096515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029587284232525234064343 7544380926348787851096515)
                  ·
                    refine ⟨11316571389523181776644773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544380926348787851096515 11316571389523181776644773)
                    ·
                      refine ⟨2121857135535596583120895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11316571389523181776644773 2121857135535596583120895)
                      ·
                        rfl

theorem cell23_4132302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_4132302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132302 prefixEnd_4132302 := by exact prefixLift 4132302
  have htrace : WordTrace (prefixWord ++ tailWord_4132302) baseStart_4132302 baseEnd_4132302 := by
    simpa [prefixWord, tailWord_4132302, baseEnd_4132302] using wordTrace_append hprefix tailTrace_4132302
  have hstable : (prefixWord ++ tailWord_4132302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132302).length < 2 ^ (prefixWord ++ tailWord_4132302).sum := by decide
  have hdescent : baseEnd_4132302 < baseStart_4132302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132312 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_4132312 : Nat := 118140960795 + 4132312 * 2 ^ 59
def prefixEnd_4132312 : Nat := 4983230072969 + 3 ^ 40 * 4132312 * 2
def baseEnd_4132312 : Nat := 707287423447380514665283

theorem tailTrace_4132312 : CollatzResearch.WordTrace tailWord_4132312 prefixEnd_4132312 707287423447380514665283 := by
  unfold tailWord_4132312
  simp only [CollatzResearch.WordTrace]
  refine ⟨75358900302673420773831595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100478533736897894365108793 75358900302673420773831595)
  ·
    refine ⟨113038350454010131160747393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75358900302673420773831595 113038350454010131160747393)
    ·
      refine ⟨84778762840507598370560545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113038350454010131160747393 84778762840507598370560545)
      ·
        refine ⟨63584072130380698777920409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84778762840507598370560545 63584072130380698777920409)
        ·
          refine ⟨47688054097785524083440307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63584072130380698777920409 47688054097785524083440307)
          ·
            refine ⟨71532081146678286125160461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47688054097785524083440307 71532081146678286125160461)
            ·
              refine ⟨26824530430004357296935173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71532081146678286125160461 26824530430004357296935173)
              ·
                refine ⟨5029599455625816993175345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26824530430004357296935173 5029599455625816993175345)
                ·
                  refine ⟨3772199591719362744881509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029599455625816993175345 3772199591719362744881509)
                  ·
                    refine ⟨707287423447380514665283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3772199591719362744881509 707287423447380514665283)
                    ·
                      rfl

theorem cell23_4132312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_4132312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132312 prefixEnd_4132312 := by exact prefixLift 4132312
  have htrace : WordTrace (prefixWord ++ tailWord_4132312) baseStart_4132312 baseEnd_4132312 := by
    simpa [prefixWord, tailWord_4132312, baseEnd_4132312] using wordTrace_append hprefix tailTrace_4132312
  have hstable : (prefixWord ++ tailWord_4132312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132312).length < 2 ^ (prefixWord ++ tailWord_4132312).sum := by decide
  have hdescent : baseEnd_4132312 < baseStart_4132312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132313 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 1, 1, 3]
def baseStart_4132313 : Nat := 118140960795 + 4132313 * 2 ^ 59
def prefixEnd_4132313 : Nat := 4983230072969 + 3 ^ 40 * 4132313 * 2
def baseEnd_4132313 : Nat := 2121862783822796040083345

theorem tailTrace_4132313 : CollatzResearch.WordTrace tailWord_4132313 prefixEnd_4132313 2121862783822796040083345 := by
  unfold tailWord_4132313
  simp only [CollatzResearch.WordTrace]
  refine ⟨150717837078343218718449593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100478558052228812478966395 150717837078343218718449593)
  ·
    refine ⟨113038377808757414038837195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150717837078343218718449593 113038377808757414038837195)
    ·
      refine ⟨169557566713136121058255793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113038377808757414038837195 169557566713136121058255793)
      ·
        refine ⟨127168175034852090793691845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169557566713136121058255793 127168175034852090793691845)
        ·
          refine ⟨23844032819034767023817221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127168175034852090793691845 23844032819034767023817221)
          ·
            refine ⟨4470756153569018816965729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23844032819034767023817221 4470756153569018816965729)
            ·
              refine ⟨3353067115176764112724297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470756153569018816965729 3353067115176764112724297)
              ·
                refine ⟨2514800336382573084543223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353067115176764112724297 2514800336382573084543223)
                ·
                  refine ⟨3772200504573859626814835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514800336382573084543223 3772200504573859626814835)
                  ·
                    refine ⟨5658300756860789440222253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772200504573859626814835 5658300756860789440222253)
                    ·
                      refine ⟨2121862783822796040083345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658300756860789440222253 2121862783822796040083345)
                      ·
                        rfl

theorem cell23_4132313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_4132313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132313 prefixEnd_4132313 := by exact prefixLift 4132313
  have htrace : WordTrace (prefixWord ++ tailWord_4132313) baseStart_4132313 baseEnd_4132313 := by
    simpa [prefixWord, tailWord_4132313, baseEnd_4132313] using wordTrace_append hprefix tailTrace_4132313
  have hstable : (prefixWord ++ tailWord_4132313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132313).length < 2 ^ (prefixWord ++ tailWord_4132313).sum := by decide
  have hdescent : baseEnd_4132313 < baseStart_4132313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132319 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 3, 2, 2]
def baseStart_4132319 : Nat := 118140960795 + 4132319 * 2 ^ 59
def prefixEnd_4132319 : Nat := 4983230072969 + 3 ^ 40 * 4132319 * 2
def baseEnd_4132319 : Nat := 2121865864706723016608317

theorem tailTrace_4132319 : CollatzResearch.WordTrace tailWord_4132319 prefixEnd_4132319 2121865864706723016608317 := by
  unfold tailWord_4132319
  simp only [CollatzResearch.WordTrace]
  refine ⟨150718055916321481743168011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100478703944214321162112007 150718055916321481743168011)
  ·
    refine ⟨226077083874482222614752017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150718055916321481743168011 226077083874482222614752017)
    ·
      refine ⟨169557812905861666961064013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226077083874482222614752017 169557812905861666961064013)
      ·
        refine ⟨63584179839698125110399005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169557812905861666961064013 63584179839698125110399005)
        ·
          refine ⟨23844067439886796916399627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63584179839698125110399005 23844067439886796916399627)
          ·
            refine ⟨35766101159830195374599441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23844067439886796916399627 35766101159830195374599441)
            ·
              refine ⟨26824575869872646530949581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35766101159830195374599441 26824575869872646530949581)
              ·
                refine ⟨10059215951202242449106093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26824575869872646530949581 10059215951202242449106093)
                ·
                  refine ⟨3772205981700840918414785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10059215951202242449106093 3772205981700840918414785)
                  ·
                    refine ⟨2829154486275630688811089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772205981700840918414785 2829154486275630688811089)
                    ·
                      refine ⟨2121865864706723016608317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829154486275630688811089 2121865864706723016608317)
                      ·
                        rfl

theorem cell23_4132319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_4132319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132319 prefixEnd_4132319 := by exact prefixLift 4132319
  have htrace : WordTrace (prefixWord ++ tailWord_4132319) baseStart_4132319 baseEnd_4132319 := by
    simpa [prefixWord, tailWord_4132319, baseEnd_4132319] using wordTrace_append hprefix tailTrace_4132319
  have hstable : (prefixWord ++ tailWord_4132319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132319).length < 2 ^ (prefixWord ++ tailWord_4132319).sum := by decide
  have hdescent : baseEnd_4132319 < baseStart_4132319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132350 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_4132350 : Nat := 118140960795 + 4132350 * 2 ^ 59
def prefixEnd_4132350 : Nat := 4983230072969 + 3 ^ 40 * 4132350 * 2
def baseEnd_4132350 : Nat := 707293927535670798440225

theorem tailTrace_4132350 : CollatzResearch.WordTrace tailWord_4132350 prefixEnd_4132350 707293927535670798440225 := by
  unfold tailWord_4132350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839898322401146754693313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100479457719472782691697669 18839898322401146754693313)
  ·
    refine ⟨14129923741800860066019985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18839898322401146754693313 14129923741800860066019985)
    ·
      refine ⟨10597442806350645049514989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14129923741800860066019985 10597442806350645049514989)
      ·
        refine ⟨3974041052381491893568121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10597442806350645049514989 3974041052381491893568121)
        ·
          refine ⟨2980530789286118920176091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974041052381491893568121 2980530789286118920176091)
          ·
            refine ⟨4470796183929178380264137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980530789286118920176091 4470796183929178380264137)
            ·
              refine ⟨3353097137946883785198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470796183929178380264137 3353097137946883785198103)
              ·
                refine ⟨5029645706920325677797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353097137946883785198103 5029645706920325677797155)
                ·
                  refine ⟨7544468560380488516695733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029645706920325677797155 7544468560380488516695733)
                  ·
                    refine ⟨707293927535670798440225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7544468560380488516695733 707293927535670798440225)
                    ·
                      rfl

theorem cell23_4132350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_4132350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132350 prefixEnd_4132350 := by exact prefixLift 4132350
  have htrace : WordTrace (prefixWord ++ tailWord_4132350) baseStart_4132350 baseEnd_4132350 := by
    simpa [prefixWord, tailWord_4132350, baseEnd_4132350] using wordTrace_append hprefix tailTrace_4132350
  have hstable : (prefixWord ++ tailWord_4132350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132350).length < 2 ^ (prefixWord ++ tailWord_4132350).sum := by decide
  have hdescent : baseEnd_4132350 < baseStart_4132350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132353 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4132353 : Nat := 118140960795 + 4132353 * 2 ^ 59
def prefixEnd_4132353 : Nat := 4983230072969 + 3 ^ 40 * 4132353 * 2
def baseEnd_4132353 : Nat := 2121883323048975883583161

theorem tailTrace_4132353 : CollatzResearch.WordTrace tailWord_4132353 prefixEnd_4132353 2121883323048975883583161 := by
  unfold tailWord_4132353
  simp only [CollatzResearch.WordTrace]
  refine ⟨150719295998198305549905713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100479530665465537033270475 150719295998198305549905713)
  ·
    refine ⟨113039471998648729162429285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150719295998198305549905713 113039471998648729162429285)
    ·
      refine ⟨21194900999746636717955491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113039471998648729162429285 21194900999746636717955491)
      ·
        refine ⟨31792351499619955076933237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21194900999746636717955491 31792351499619955076933237)
        ·
          refine ⟨2980532953089370788462491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31792351499619955076933237 2980532953089370788462491)
          ·
            refine ⟨4470799429634056182693737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980532953089370788462491 4470799429634056182693737)
            ·
              refine ⟨3353099572225542137020303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470799429634056182693737 3353099572225542137020303)
              ·
                refine ⟨5029649358338313205530455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353099572225542137020303 5029649358338313205530455)
                ·
                  refine ⟨7544474037507469808295683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029649358338313205530455 7544474037507469808295683)
                  ·
                    refine ⟨11316711056261204712443525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544474037507469808295683 11316711056261204712443525)
                    ·
                      refine ⟨2121883323048975883583161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11316711056261204712443525 2121883323048975883583161)
                      ·
                        rfl

theorem cell23_4132353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4132353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132353 prefixEnd_4132353 := by exact prefixLift 4132353
  have htrace : WordTrace (prefixWord ++ tailWord_4132353) baseStart_4132353 baseEnd_4132353 := by
    simpa [prefixWord, tailWord_4132353, baseEnd_4132353] using wordTrace_append hprefix tailTrace_4132353
  have hstable : (prefixWord ++ tailWord_4132353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132353).length < 2 ^ (prefixWord ++ tailWord_4132353).sum := by decide
  have hdescent : baseEnd_4132353 < baseStart_4132353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132356 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4132356 : Nat := 118140960795 + 4132356 * 2 ^ 59
def prefixEnd_4132356 : Nat := 4983230072969 + 3 ^ 40 * 4132356 * 2
def baseEnd_4132356 : Nat := 2121884863490939371845647

theorem tailTrace_4132356 : CollatzResearch.WordTrace tailWord_4132356 prefixEnd_4132356 2121884863490939371845647 := by
  unfold tailWord_4132356
  simp only [CollatzResearch.WordTrace]
  refine ⟨75359702708593718531132461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100479603611458291374843281 75359702708593718531132461)
  ·
    refine ⟨28259888515722644449174673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75359702708593718531132461 28259888515722644449174673)
    ·
      refine ⟨21194916386791983336881005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28259888515722644449174673 21194916386791983336881005)
      ·
        refine ⟨7948093645046993751330377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21194916386791983336881005 7948093645046993751330377)
        ·
          refine ⟨5961070233785245313497783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948093645046993751330377 5961070233785245313497783)
          ·
            refine ⟨8941605350677867970246675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961070233785245313497783 8941605350677867970246675)
            ·
              refine ⟨13412408026016801955370013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941605350677867970246675 13412408026016801955370013)
              ·
                refine ⟨5029653009756300733263755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13412408026016801955370013 5029653009756300733263755)
                ·
                  refine ⟨7544479514634451099895633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029653009756300733263755 7544479514634451099895633)
                  ·
                    refine ⟨5658359635975838324921725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7544479514634451099895633 5658359635975838324921725)
                    ·
                      refine ⟨2121884863490939371845647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658359635975838324921725 2121884863490939371845647)
                      ·
                        rfl

theorem cell23_4132356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4132356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132356 prefixEnd_4132356 := by exact prefixLift 4132356
  have htrace : WordTrace (prefixWord ++ tailWord_4132356) baseStart_4132356 baseEnd_4132356 := by
    simpa [prefixWord, tailWord_4132356, baseEnd_4132356] using wordTrace_append hprefix tailTrace_4132356
  have hstable : (prefixWord ++ tailWord_4132356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132356).length < 2 ^ (prefixWord ++ tailWord_4132356).sum := by decide
  have hdescent : baseEnd_4132356 < baseStart_4132356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132426 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_4132426 : Nat := 118140960795 + 4132426 * 2 ^ 59
def prefixEnd_4132426 : Nat := 4983230072969 + 3 ^ 40 * 4132426 * 2
def baseEnd_4132426 : Nat := 2121920807136754097970325

theorem tailTrace_4132426 : CollatzResearch.WordTrace tailWord_4132426 prefixEnd_4132426 2121920807136754097970325 := by
  unfold tailWord_4132426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680489631733459754328283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100481305684622559344875421 37680489631733459754328283)
  ·
    refine ⟨56520734447600189631492425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37680489631733459754328283 56520734447600189631492425)
    ·
      refine ⟨42390550835700142223619319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56520734447600189631492425 42390550835700142223619319)
      ·
        refine ⟨63585826253550213335428979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42390550835700142223619319 63585826253550213335428979)
        ·
          refine ⟨95378739380325320003143469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63585826253550213335428979 95378739380325320003143469)
          ·
            refine ⟨35767027267621995001178801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95378739380325320003143469 35767027267621995001178801)
            ·
              refine ⟨26825270450716496250884101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35767027267621995001178801 26825270450716496250884101)
              ·
                refine ⟨5029738209509343047040769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26825270450716496250884101 5029738209509343047040769)
                ·
                  refine ⟨3772303657132007285280577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029738209509343047040769 3772303657132007285280577)
                  ·
                    refine ⟨2829227742849005463960433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772303657132007285280577 2829227742849005463960433)
                    ·
                      refine ⟨2121920807136754097970325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829227742849005463960433 2121920807136754097970325)
                      ·
                        rfl

theorem cell23_4132426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_4132426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132426 prefixEnd_4132426 := by exact prefixLift 4132426
  have htrace : WordTrace (prefixWord ++ tailWord_4132426) baseStart_4132426 baseEnd_4132426 := by
    simpa [prefixWord, tailWord_4132426, baseEnd_4132426] using wordTrace_append hprefix tailTrace_4132426
  have hstable : (prefixWord ++ tailWord_4132426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132426).length < 2 ^ (prefixWord ++ tailWord_4132426).sum := by decide
  have hdescent : baseEnd_4132426 < baseStart_4132426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132442 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_4132442 : Nat := 118140960795 + 4132442 * 2 ^ 59
def prefixEnd_4132442 : Nat := 4983230072969 + 3 ^ 40 * 4132442 * 2
def baseEnd_4132442 : Nat := 2121929022827226035370251

theorem tailTrace_4132442 : CollatzResearch.WordTrace tailWord_4132442 prefixEnd_4132442 2121929022827226035370251 := by
  unfold tailWord_4132442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680635523718968437473895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100481694729917249166597053 37680635523718968437473895)
  ·
    refine ⟨56520953285578452656210843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37680635523718968437473895 56520953285578452656210843)
    ·
      refine ⟨84781429928367678984316265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56520953285578452656210843 84781429928367678984316265)
      ·
        refine ⟨63586072446275759238237199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84781429928367678984316265 63586072446275759238237199)
        ·
          refine ⟨95379108669413638857355799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63586072446275759238237199 95379108669413638857355799)
          ·
            refine ⟨143068663004120458286033699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95379108669413638857355799 143068663004120458286033699)
            ·
              refine ⟨214602994506180687429050549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143068663004120458286033699 214602994506180687429050549)
              ·
                refine ⟨20119030734954439446473489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214602994506180687429050549 20119030734954439446473489)
                ·
                  refine ⟨15089273051215829584855117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20119030734954439446473489 15089273051215829584855117)
                  ·
                    refine ⟨5658477394205936094320669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15089273051215829584855117 5658477394205936094320669)
                    ·
                      refine ⟨2121929022827226035370251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658477394205936094320669 2121929022827226035370251)
                      ·
                        rfl

theorem cell23_4132442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_4132442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132442 prefixEnd_4132442 := by exact prefixLift 4132442
  have htrace : WordTrace (prefixWord ++ tailWord_4132442) baseStart_4132442 baseEnd_4132442 := by
    simpa [prefixWord, tailWord_4132442, baseEnd_4132442] using wordTrace_append hprefix tailTrace_4132442
  have hstable : (prefixWord ++ tailWord_4132442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132442).length < 2 ^ (prefixWord ++ tailWord_4132442).sum := by decide
  have hdescent : baseEnd_4132442 < baseStart_4132442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132516 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_4132516 : Nat := 118140960795 + 4132516 * 2 ^ 59
def prefixEnd_4132516 : Nat := 4983230072969 + 3 ^ 40 * 4132516 * 2
def baseEnd_4132516 : Nat := 2121967020395658745844911

theorem tailTrace_4132516 : CollatzResearch.WordTrace tailWord_4132516 prefixEnd_4132516 2121967020395658745844911 := by
  unfold tailWord_4132516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75362620548303892194044701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100483494064405189592059601 75362620548303892194044701)
  ·
    refine ⟨28260982705613959572766763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75362620548303892194044701 28260982705613959572766763)
    ·
      refine ⟨42391474058420939359150145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28260982705613959572766763 42391474058420939359150145)
      ·
        refine ⟨31793605543815704519362609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42391474058420939359150145 31793605543815704519362609)
        ·
          refine ⟨23845204157861778389521957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31793605543815704519362609 23845204157861778389521957)
          ·
            refine ⟨4470975779599083448035367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23845204157861778389521957 4470975779599083448035367)
            ·
              refine ⟨6706463669398625172053051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470975779599083448035367 6706463669398625172053051)
              ·
                refine ⟨10059695504097937758079577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706463669398625172053051 10059695504097937758079577)
                ·
                  refine ⟨7544771628073453318559683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059695504097937758079577 7544771628073453318559683)
                  ·
                    refine ⟨11317157442110179977839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544771628073453318559683 11317157442110179977839525)
                    ·
                      refine ⟨2121967020395658745844911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11317157442110179977839525 2121967020395658745844911)
                      ·
                        rfl

theorem cell23_4132516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_4132516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132516 prefixEnd_4132516 := by exact prefixLift 4132516
  have htrace : WordTrace (prefixWord ++ tailWord_4132516) baseStart_4132516 baseEnd_4132516 := by
    simpa [prefixWord, tailWord_4132516, baseEnd_4132516] using wordTrace_append hprefix tailTrace_4132516
  have hstable : (prefixWord ++ tailWord_4132516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132516).length < 2 ^ (prefixWord ++ tailWord_4132516).sum := by decide
  have hdescent : baseEnd_4132516 < baseStart_4132516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132549 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_4132549 : Nat := 118140960795 + 4132549 * 2 ^ 59
def prefixEnd_4132549 : Nat := 4983230072969 + 3 ^ 40 * 4132549 * 2
def baseEnd_4132549 : Nat := 2121983965257257116732259

theorem tailTrace_4132549 : CollatzResearch.WordTrace tailWord_4132549 prefixEnd_4132549 2121983965257257116732259 := by
  unfold tailWord_4132549
  simp only [CollatzResearch.WordTrace]
  refine ⟨150726444705488231024040701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100484296470325487349360467 150726444705488231024040701)
  ·
    refine ⟨56522416764558086634015263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150726444705488231024040701 56522416764558086634015263)
    ·
      refine ⟨84783625146837129951022895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56522416764558086634015263 84783625146837129951022895)
      ·
        refine ⟨127175437720255694926534343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84783625146837129951022895 127175437720255694926534343)
        ·
          refine ⟨190763156580383542389801515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127175437720255694926534343 190763156580383542389801515)
          ·
            refine ⟨286144734870575313584702273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190763156580383542389801515 286144734870575313584702273)
            ·
              refine ⟨214608551152931485188526705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286144734870575313584702273 214608551152931485188526705)
              ·
                refine ⟨160956413364698613891395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214608551152931485188526705 160956413364698613891395029)
                ·
                  refine ⟨3772415938235123763079571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160956413364698613891395029 3772415938235123763079571)
                  ·
                    refine ⟨5658623907352685644619357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772415938235123763079571 5658623907352685644619357)
                    ·
                      refine ⟨2121983965257257116732259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658623907352685644619357 2121983965257257116732259)
                      ·
                        rfl

theorem cell23_4132549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_4132549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132549 prefixEnd_4132549 := by exact prefixLift 4132549
  have htrace : WordTrace (prefixWord ++ tailWord_4132549) baseStart_4132549 baseEnd_4132549 := by
    simpa [prefixWord, tailWord_4132549, baseEnd_4132549] using wordTrace_append hprefix tailTrace_4132549
  have hstable : (prefixWord ++ tailWord_4132549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132549).length < 2 ^ (prefixWord ++ tailWord_4132549).sum := by decide
  have hdescent : baseEnd_4132549 < baseStart_4132549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132550 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4132550 : Nat := 118140960795 + 4132550 * 2 ^ 59
def prefixEnd_4132550 : Nat := 4983230072969 + 3 ^ 40 * 4132550 * 2
def baseEnd_4132550 : Nat := 2121984478737911612819755

theorem tailTrace_4132550 : CollatzResearch.WordTrace tailWord_4132550 prefixEnd_4132550 2121984478737911612819755 := by
  unfold tailWord_4132550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710202536827644006088347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100484320785656405463218069 4710202536827644006088347)
  ·
    refine ⟨7065303805241466009132521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4710202536827644006088347 7065303805241466009132521)
    ·
      refine ⟨5298977853931099506849391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7065303805241466009132521 5298977853931099506849391)
      ·
        refine ⟨7948466780896649260274087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298977853931099506849391 7948466780896649260274087)
        ·
          refine ⟨11922700171344973890411131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948466780896649260274087 11922700171344973890411131)
          ·
            refine ⟨17884050257017460835616697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922700171344973890411131 17884050257017460835616697)
            ·
              refine ⟨13413037692763095626712523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17884050257017460835616697 13413037692763095626712523)
              ·
                refine ⟨20119556539144643440068785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413037692763095626712523 20119556539144643440068785)
                ·
                  refine ⟨15089667404358482580051589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20119556539144643440068785 15089667404358482580051589)
                  ·
                    refine ⟨2829312638317215483759673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15089667404358482580051589 2829312638317215483759673)
                    ·
                      refine ⟨2121984478737911612819755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829312638317215483759673 2121984478737911612819755)
                      ·
                        rfl

theorem cell23_4132550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4132550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132550 prefixEnd_4132550 := by exact prefixLift 4132550
  have htrace : WordTrace (prefixWord ++ tailWord_4132550) baseStart_4132550 baseEnd_4132550 := by
    simpa [prefixWord, tailWord_4132550, baseEnd_4132550] using wordTrace_append hprefix tailTrace_4132550
  have hstable : (prefixWord ++ tailWord_4132550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132550).length < 2 ^ (prefixWord ++ tailWord_4132550).sum := by decide
  have hdescent : baseEnd_4132550 < baseStart_4132550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132569 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_4132569 : Nat := 118140960795 + 4132569 * 2 ^ 59
def prefixEnd_4132569 : Nat := 4983230072969 + 3 ^ 40 * 4132569 * 2
def baseEnd_4132569 : Nat := 707331411623449012827389

theorem tailTrace_4132569 : CollatzResearch.WordTrace tailWord_4132569 prefixEnd_4132569 707331411623449012827389 := by
  unfold tailWord_4132569
  simp only [CollatzResearch.WordTrace]
  refine ⟨150727174165415774439768761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100484782776943849626512507 150727174165415774439768761)
  ·
    refine ⟨113045380624061830829826571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150727174165415774439768761 113045380624061830829826571)
    ·
      refine ⟨169568070936092746244739857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113045380624061830829826571 169568070936092746244739857)
      ·
        refine ⟨127176053202069559683554893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169568070936092746244739857 127176053202069559683554893)
        ·
          refine ⟨47691019950776084881333085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127176053202069559683554893 47691019950776084881333085)
          ·
            refine ⟨17884132481541031830499907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47691019950776084881333085 17884132481541031830499907)
            ·
              refine ⟨26826198722311547745749861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884132481541031830499907 26826198722311547745749861)
              ·
                refine ⟨5029912260433415202328099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26826198722311547745749861 5029912260433415202328099)
                ·
                  refine ⟨7544868390650122803492149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029912260433415202328099 7544868390650122803492149)
                  ·
                    refine ⟨707331411623449012827389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7544868390650122803492149 707331411623449012827389)
                    ·
                      rfl

theorem cell23_4132569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_4132569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132569 prefixEnd_4132569 := by exact prefixLift 4132569
  have htrace : WordTrace (prefixWord ++ tailWord_4132569) baseStart_4132569 baseEnd_4132569 := by
    simpa [prefixWord, tailWord_4132569, baseEnd_4132569] using wordTrace_append hprefix tailTrace_4132569
  have hstable : (prefixWord ++ tailWord_4132569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132569).length < 2 ^ (prefixWord ++ tailWord_4132569).sum := by decide
  have hdescent : baseEnd_4132569 < baseStart_4132569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132599 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 4, 4]
def baseStart_4132599 : Nat := 118140960795 + 4132599 * 2 ^ 59
def prefixEnd_4132599 : Nat := 4983230072969 + 3 ^ 40 * 4132599 * 2
def baseEnd_4132599 : Nat := 707336546429993973702343

theorem tailTrace_4132599 : CollatzResearch.WordTrace tailWord_4132599 prefixEnd_4132599 707336546429993973702343 := by
  unfold tailWord_4132599
  simp only [CollatzResearch.WordTrace]
  refine ⟨150728268355307089563360851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100485512236871393042240567 150728268355307089563360851)
  ·
    refine ⟨226092402532960634345041277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150728268355307089563360851 226092402532960634345041277)
    ·
      refine ⟨84784650949860237879390479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226092402532960634345041277 84784650949860237879390479)
      ·
        refine ⟨127176976424790356819085719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84784650949860237879390479 127176976424790356819085719)
        ·
          refine ⟨190765464637185535228628579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127176976424790356819085719 190765464637185535228628579)
          ·
            refine ⟨286148196955778302842942869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190765464637185535228628579 286148196955778302842942869)
            ·
              refine ⟨13413196732302107945762947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286148196955778302842942869 13413196732302107945762947)
              ·
                refine ⟨20119795098453161918644421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413196732302107945762947 20119795098453161918644421)
                ·
                  refine ⟨3772461580959967859745829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20119795098453161918644421 3772461580959967859745829)
                  ·
                    refine ⟨707336546429993973702343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3772461580959967859745829 707336546429993973702343)
                    ·
                      rfl

theorem cell23_4132599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_4132599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132599 prefixEnd_4132599 := by exact prefixLift 4132599
  have htrace : WordTrace (prefixWord ++ tailWord_4132599) baseStart_4132599 baseEnd_4132599 := by
    simpa [prefixWord, tailWord_4132599, baseEnd_4132599] using wordTrace_append hprefix tailTrace_4132599
  have hstable : (prefixWord ++ tailWord_4132599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132599).length < 2 ^ (prefixWord ++ tailWord_4132599).sum := by decide
  have hdescent : baseEnd_4132599 < baseStart_4132599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132609 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4132609 : Nat := 118140960795 + 4132609 * 2 ^ 59
def prefixEnd_4132609 : Nat := 4983230072969 + 3 ^ 40 * 4132609 * 2
def baseEnd_4132609 : Nat := 2122014774096526881981983

theorem tailTrace_4132609 : CollatzResearch.WordTrace tailWord_4132609 prefixEnd_4132609 2122014774096526881981983 := by
  unfold tailWord_4132609
  simp only [CollatzResearch.WordTrace]
  refine ⟨150728633085270861271224881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100485755390180574180816587 150728633085270861271224881)
  ·
    refine ⟨113046474813953145953418661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150728633085270861271224881 113046474813953145953418661)
    ·
      refine ⟨21196214027616214866265999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113046474813953145953418661 21196214027616214866265999)
      ·
        refine ⟨31794321041424322299398999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196214027616214866265999 31794321041424322299398999)
        ·
          refine ⟨47691481562136483449098499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31794321041424322299398999 47691481562136483449098499)
          ·
            refine ⟨71537222343204725173647749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47691481562136483449098499 71537222343204725173647749)
            ·
              refine ⟨13413229189350885970058953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71537222343204725173647749 13413229189350885970058953)
              ·
                refine ⟨10059921892013164477544215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13413229189350885970058953 10059921892013164477544215)
                ·
                  refine ⟨15089882838019746716316323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059921892013164477544215 15089882838019746716316323)
                  ·
                    refine ⟨22634824257029620074474485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15089882838019746716316323 22634824257029620074474485)
                    ·
                      refine ⟨2122014774096526881981983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22634824257029620074474485 2122014774096526881981983)
                      ·
                        rfl

theorem cell23_4132609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4132609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132609 prefixEnd_4132609 := by exact prefixLift 4132609
  have htrace : WordTrace (prefixWord ++ tailWord_4132609) baseStart_4132609 baseEnd_4132609 := by
    simpa [prefixWord, tailWord_4132609, baseEnd_4132609] using wordTrace_append hprefix tailTrace_4132609
  have hstable : (prefixWord ++ tailWord_4132609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132609).length < 2 ^ (prefixWord ++ tailWord_4132609).sum := by decide
  have hdescent : baseEnd_4132609 < baseStart_4132609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132616 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_4132616 : Nat := 118140960795 + 4132616 * 2 ^ 59
def prefixEnd_4132616 : Nat := 4983230072969 + 3 ^ 40 * 4132616 * 2
def baseEnd_4132616 : Nat := 707339456153702784864817

theorem tailTrace_4132616 : CollatzResearch.WordTrace tailWord_4132616 prefixEnd_4132616 707339456153702784864817 := by
  unfold tailWord_4132616
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364444198122750733364851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100485925597497000977819801 75364444198122750733364851)
  ·
    refine ⟨113046666297184126100047277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75364444198122750733364851 113046666297184126100047277)
    ·
      refine ⟨42392499861444047287517729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113046666297184126100047277 42392499861444047287517729)
      ·
        refine ⟨31794374896083035465638297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42392499861444047287517729 31794374896083035465638297)
        ·
          refine ⟨23845781172062276599228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31794374896083035465638297 23845781172062276599228723)
          ·
            refine ⟨35768671758093414898843085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23845781172062276599228723 35768671758093414898843085)
            ·
              refine ⟨13413251909285030587066157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35768671758093414898843085 13413251909285030587066157)
              ·
                refine ⟨5029969465981886470149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13413251909285030587066157 5029969465981886470149809)
                ·
                  refine ⟨3772477099486414852612357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029969465981886470149809 3772477099486414852612357)
                  ·
                    refine ⟨707339456153702784864817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3772477099486414852612357 707339456153702784864817)
                    ·
                      rfl

theorem cell23_4132616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_4132616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132616 prefixEnd_4132616 := by exact prefixLift 4132616
  have htrace : WordTrace (prefixWord ++ tailWord_4132616) baseStart_4132616 baseEnd_4132616 := by
    simpa [prefixWord, tailWord_4132616, baseEnd_4132616] using wordTrace_append hprefix tailTrace_4132616
  have hstable : (prefixWord ++ tailWord_4132616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132616).length < 2 ^ (prefixWord ++ tailWord_4132616).sum := by decide
  have hdescent : baseEnd_4132616 < baseStart_4132616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132640 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4132640 : Nat := 118140960795 + 4132640 * 2 ^ 59
def prefixEnd_4132640 : Nat := 4983230072969 + 3 ^ 40 * 4132640 * 2
def baseEnd_4132640 : Nat := 2122030691996816260694341

theorem tailTrace_4132640 : CollatzResearch.WordTrace tailWord_4132640 prefixEnd_4132640 2122030691996816260694341 := by
  unfold tailWord_4132640
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364881874079276782801687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100486509165439035710402249 75364881874079276782801687)
  ·
    refine ⟨113047322811118915174202531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75364881874079276782801687 113047322811118915174202531)
    ·
      refine ⟨169570984216678372761303797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113047322811118915174202531 169570984216678372761303797)
      ·
        refine ⟨15897279770313597446372231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169570984216678372761303797 15897279770313597446372231)
        ·
          refine ⟨23845919655470396169558347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15897279770313597446372231 23845919655470396169558347)
          ·
            refine ⟨35768879483205594254337521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23845919655470396169558347 35768879483205594254337521)
            ·
              refine ⟨26826659612404195690753141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35768879483205594254337521 26826659612404195690753141)
              ·
                refine ⟨2514999338662893346008107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26826659612404195690753141 2514999338662893346008107)
                ·
                  refine ⟨3772499007994340019012161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514999338662893346008107 3772499007994340019012161)
                  ·
                    refine ⟨2829374255995755014259121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772499007994340019012161 2829374255995755014259121)
                    ·
                      refine ⟨2122030691996816260694341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829374255995755014259121 2122030691996816260694341)
                      ·
                        rfl

theorem cell23_4132640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4132640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132640 prefixEnd_4132640 := by exact prefixLift 4132640
  have htrace : WordTrace (prefixWord ++ tailWord_4132640) baseStart_4132640 baseEnd_4132640 := by
    simpa [prefixWord, tailWord_4132640, baseEnd_4132640] using wordTrace_append hprefix tailTrace_4132640
  have hstable : (prefixWord ++ tailWord_4132640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132640).length < 2 ^ (prefixWord ++ tailWord_4132640).sum := by decide
  have hdescent : baseEnd_4132640 < baseStart_4132640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132657 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_4132657 : Nat := 118140960795 + 4132657 * 2 ^ 59
def prefixEnd_4132657 : Nat := 4983230072969 + 3 ^ 40 * 4132657 * 2
def baseEnd_4132657 : Nat := 2122039421167942694181763

theorem tailTrace_4132657 : CollatzResearch.WordTrace tailWord_4132657 prefixEnd_4132657 2122039421167942694181763 := by
  unfold tailWord_4132657
  simp only [CollatzResearch.WordTrace]
  refine ⟨150730383789096965468972225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100486922526064643645981483 150730383789096965468972225)
  ·
    refine ⟨113047787841822724101729169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150730383789096965468972225 113047787841822724101729169)
    ·
      refine ⟨84785840881367043076296877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113047787841822724101729169 84785840881367043076296877)
      ·
        refine ⟨31794690330512641153611329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84785840881367043076296877 31794690330512641153611329)
        ·
          refine ⟨23846017747884480865208497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31794690330512641153611329 23846017747884480865208497)
          ·
            refine ⟨17884513310913360648906373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23846017747884480865208497 17884513310913360648906373)
            ·
              refine ⟨3353346245796255121669945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17884513310913360648906373 3353346245796255121669945)
              ·
                refine ⟨2515009684347191341252459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353346245796255121669945 2515009684347191341252459)
                ·
                  refine ⟨3772514526520787011878689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515009684347191341252459 3772514526520787011878689)
                  ·
                    refine ⟨2829385894890590258909017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772514526520787011878689 2829385894890590258909017)
                    ·
                      refine ⟨2122039421167942694181763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829385894890590258909017 2122039421167942694181763)
                      ·
                        rfl

theorem cell23_4132657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_4132657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132657 prefixEnd_4132657 := by exact prefixLift 4132657
  have htrace : WordTrace (prefixWord ++ tailWord_4132657) baseStart_4132657 baseEnd_4132657 := by
    simpa [prefixWord, tailWord_4132657, baseEnd_4132657] using wordTrace_append hprefix tailTrace_4132657
  have hstable : (prefixWord ++ tailWord_4132657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132657).length < 2 ^ (prefixWord ++ tailWord_4132657).sum := by decide
  have hdescent : baseEnd_4132657 < baseStart_4132657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132706 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4132706 : Nat := 118140960795 + 4132706 * 2 ^ 59
def prefixEnd_4132706 : Nat := 4983230072969 + 3 ^ 40 * 4132706 * 2
def baseEnd_4132706 : Nat := 707354860573337667489679

theorem tailTrace_4132706 : CollatzResearch.WordTrace tailWord_4132706 prefixEnd_4132706 707354860573337667489679 := by
  unfold tailWord_4132706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683042741479861709376493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100488113977279631225003981 37683042741479861709376493)
  ·
    refine ⟨14131141028054948141016185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37683042741479861709376493 14131141028054948141016185)
    ·
      refine ⟨10598355771041211105762139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131141028054948141016185 10598355771041211105762139)
      ·
        refine ⟨15897533656561816658643209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598355771041211105762139 15897533656561816658643209)
        ·
          refine ⟨11923150242421362493982407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15897533656561816658643209 11923150242421362493982407)
          ·
            refine ⟨17884725363632043740973611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923150242421362493982407 17884725363632043740973611)
            ·
              refine ⟨26827088045448065611460417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884725363632043740973611 26827088045448065611460417)
              ·
                refine ⟨20120316034086049208595313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26827088045448065611460417 20120316034086049208595313)
                ·
                  refine ⟨15090237025564536906446485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20120316034086049208595313 15090237025564536906446485)
                  ·
                    refine ⟨707354860573337667489679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15090237025564536906446485 707354860573337667489679)
                    ·
                      rfl

theorem cell23_4132706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4132706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132706 prefixEnd_4132706 := by exact prefixLift 4132706
  have htrace : WordTrace (prefixWord ++ tailWord_4132706) baseStart_4132706 baseEnd_4132706 := by
    simpa [prefixWord, tailWord_4132706, baseEnd_4132706] using wordTrace_append hprefix tailTrace_4132706
  have hstable : (prefixWord ++ tailWord_4132706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132706).length < 2 ^ (prefixWord ++ tailWord_4132706).sum := by decide
  have hdescent : baseEnd_4132706 < baseStart_4132706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132707 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 2, 1, 3]
def baseStart_4132707 : Nat := 118140960795 + 4132707 * 2 ^ 59
def prefixEnd_4132707 : Nat := 4983230072969 + 3 ^ 40 * 4132707 * 2
def baseEnd_4132707 : Nat := 2122065095200667498556533

theorem tailTrace_4132707 : CollatzResearch.WordTrace tailWord_4132707 prefixEnd_4132707 2122065095200667498556533 := by
  unfold tailWord_4132707
  simp only [CollatzResearch.WordTrace]
  refine ⟨150732207438915824008292375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100488138292610549338861583 150732207438915824008292375)
  ·
    refine ⟨226098311158373736012438563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150732207438915824008292375 226098311158373736012438563)
    ·
      refine ⟨339147466737560604018657845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226098311158373736012438563 339147466737560604018657845)
      ·
        refine ⟨31795075006646306626749173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339147466737560604018657845 31795075006646306626749173)
        ·
          refine ⟨2980788281873091246257735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31795075006646306626749173 2980788281873091246257735)
          ·
            refine ⟨4471182422809636869386603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980788281873091246257735 4471182422809636869386603)
            ·
              refine ⟨6706773634214455304079905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471182422809636869386603 6706773634214455304079905)
              ·
                refine ⟨5030080225660841478059929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6706773634214455304079905 5030080225660841478059929)
                ·
                  refine ⟨3772560169245631108544947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030080225660841478059929 3772560169245631108544947)
                  ·
                    refine ⟨5658840253868446662817421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772560169245631108544947 5658840253868446662817421)
                    ·
                      refine ⟨2122065095200667498556533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5658840253868446662817421 2122065095200667498556533)
                      ·
                        rfl

theorem cell23_4132707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_4132707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132707 prefixEnd_4132707 := by exact prefixLift 4132707
  have htrace : WordTrace (prefixWord ++ tailWord_4132707) baseStart_4132707 baseEnd_4132707 := by
    simpa [prefixWord, tailWord_4132707, baseEnd_4132707] using wordTrace_append hprefix tailTrace_4132707
  have hstable : (prefixWord ++ tailWord_4132707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132707).length < 2 ^ (prefixWord ++ tailWord_4132707).sum := by decide
  have hdescent : baseEnd_4132707 < baseStart_4132707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132770 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_4132770 : Nat := 118140960795 + 4132770 * 2 ^ 59
def prefixEnd_4132770 : Nat := 4983230072969 + 3 ^ 40 * 4132770 * 2
def baseEnd_4132770 : Nat := 235788604942433416896527

theorem tailTrace_4132770 : CollatzResearch.WordTrace tailWord_4132770 prefixEnd_4132770 235788604942433416896527 := by
  unfold tailWord_4132770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683626309421896441958941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100489670158458390511890509 37683626309421896441958941)
  ·
    refine ⟨14131359866033211165734603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37683626309421896441958941 14131359866033211165734603)
    ·
      refine ⟨21197039799049816748601905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131359866033211165734603 21197039799049816748601905)
      ·
        refine ⟨15897779849287362561451429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21197039799049816748601905 15897779849287362561451429)
        ·
          refine ⟨2980833721741380480272143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15897779849287362561451429 2980833721741380480272143)
          ·
            refine ⟨4471250582612070720408215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980833721741380480272143 4471250582612070720408215)
            ·
              refine ⟨6706875873918106080612323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471250582612070720408215 6706875873918106080612323)
              ·
                refine ⟨10060313810877159120918485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706875873918106080612323 10060313810877159120918485)
                ·
                  refine ⟨235788604942433416896527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10060313810877159120918485 235788604942433416896527)
                  ·
                    rfl

theorem cell23_4132770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_4132770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132770 prefixEnd_4132770 := by exact prefixLift 4132770
  have htrace : WordTrace (prefixWord ++ tailWord_4132770) baseStart_4132770 baseEnd_4132770 := by
    simpa [prefixWord, tailWord_4132770, baseEnd_4132770] using wordTrace_append hprefix tailTrace_4132770
  have hstable : (prefixWord ++ tailWord_4132770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132770).length < 2 ^ (prefixWord ++ tailWord_4132770).sum := by decide
  have hdescent : baseEnd_4132770 < baseStart_4132770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132856 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_4132856 : Nat := 118140960795 + 4132856 * 2 ^ 59
def prefixEnd_4132856 : Nat := 4983230072969 + 3 ^ 40 * 4132856 * 2
def baseEnd_4132856 : Nat := 707380534606062471864449

theorem tailTrace_4132856 : CollatzResearch.WordTrace tailWord_4132856 prefixEnd_4132856 707380534606062471864449 := by
  unfold tailWord_4132856
  simp only [CollatzResearch.WordTrace]
  refine ⟨75368820957688011227733211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100491761276917348303644281 75368820957688011227733211)
  ·
    refine ⟨113053231436532016841599817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75368820957688011227733211 113053231436532016841599817)
    ·
      refine ⟨84789923577399012631199863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113053231436532016841599817 84789923577399012631199863)
      ·
        refine ⟨127184885366098518946799795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84789923577399012631199863 127184885366098518946799795)
        ·
          refine ⟨190777328049147778420199693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127184885366098518946799795 190777328049147778420199693)
          ·
            refine ⟨71541498018430416907574885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190777328049147778420199693 71541498018430416907574885)
            ·
              refine ⟨13414030878455703170170291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71541498018430416907574885 13414030878455703170170291)
              ·
                refine ⟨20121046317683554755255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13414030878455703170170291 20121046317683554755255437)
                ·
                  refine ⟨7545392369131333033220789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20121046317683554755255437 7545392369131333033220789)
                  ·
                    refine ⟨707380534606062471864449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7545392369131333033220789 707380534606062471864449)
                    ·
                      rfl

theorem cell23_4132856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_4132856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132856 prefixEnd_4132856 := by exact prefixLift 4132856
  have htrace : WordTrace (prefixWord ++ tailWord_4132856) baseStart_4132856 baseEnd_4132856 := by
    simpa [prefixWord, tailWord_4132856, baseEnd_4132856] using wordTrace_append hprefix tailTrace_4132856
  have hstable : (prefixWord ++ tailWord_4132856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132856).length < 2 ^ (prefixWord ++ tailWord_4132856).sum := by decide
  have hdescent : baseEnd_4132856 < baseStart_4132856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132877 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4132877 : Nat := 118140960795 + 4132877 * 2 ^ 59
def prefixEnd_4132877 : Nat := 4983230072969 + 3 ^ 40 * 4132877 * 2
def baseEnd_4132877 : Nat := 235794709656881314825639

theorem tailTrace_4132877 : CollatzResearch.WordTrace tailWord_4132877 prefixEnd_4132877 235794709656881314825639 := by
  unfold tailWord_4132877
  simp only [CollatzResearch.WordTrace]
  refine ⟨150738407848299943041980885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100492271898866628694653923 150738407848299943041980885)
  ·
    refine ⟨3532931433944529915046427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 150738407848299943041980885 3532931433944529915046427)
    ·
      refine ⟨5299397150916794872569641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532931433944529915046427 5299397150916794872569641)
      ·
        refine ⟨3974547863187596154427231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5299397150916794872569641 3974547863187596154427231)
        ·
          refine ⟨5961821794781394231640847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974547863187596154427231 5961821794781394231640847)
          ·
            refine ⟨8942732692172091347461271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961821794781394231640847 8942732692172091347461271)
            ·
              refine ⟨13414099038258137021191907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942732692172091347461271 13414099038258137021191907)
              ·
                refine ⟨20121148557387205531787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13414099038258137021191907 20121148557387205531787861)
                ·
                  refine ⟨235794709656881314825639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20121148557387205531787861 235794709656881314825639)
                  ·
                    rfl

theorem cell23_4132877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4132877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132877 prefixEnd_4132877 := by exact prefixLift 4132877
  have htrace : WordTrace (prefixWord ++ tailWord_4132877) baseStart_4132877 baseEnd_4132877 := by
    simpa [prefixWord, tailWord_4132877, baseEnd_4132877] using wordTrace_append hprefix tailTrace_4132877
  have hstable : (prefixWord ++ tailWord_4132877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132877).length < 2 ^ (prefixWord ++ tailWord_4132877).sum := by decide
  have hdescent : baseEnd_4132877 < baseStart_4132877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132887 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4132887 : Nat := 118140960795 + 4132887 * 2 ^ 59
def prefixEnd_4132887 : Nat := 4983230072969 + 3 ^ 40 * 4132887 * 2
def baseEnd_4132887 : Nat := 2122157521718476794305705

theorem tailTrace_4132887 : CollatzResearch.WordTrace tailWord_4132887 prefixEnd_4132887 2122157521718476794305705 := by
  unfold tailWord_4132887
  simp only [CollatzResearch.WordTrace]
  refine ⟨150738772578263714749844915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100492515052175809833229943 150738772578263714749844915)
  ·
    refine ⟨226108158867395572124767373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150738772578263714749844915 226108158867395572124767373)
    ·
      refine ⟨84790559575273339546787765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226108158867395572124767373 84790559575273339546787765)
      ·
        refine ⟨7949114960181875582511353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84790559575273339546787765 7949114960181875582511353)
        ·
          refine ⟨5961836220136406686883515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949114960181875582511353 5961836220136406686883515)
          ·
            refine ⟨8942754330204610030325273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961836220136406686883515 8942754330204610030325273)
            ·
              refine ⟨6707065747653457522743955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8942754330204610030325273 6707065747653457522743955)
              ·
                refine ⟨10060598621480186284115933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707065747653457522743955 10060598621480186284115933)
                ·
                  refine ⟨3772724483055069856543475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10060598621480186284115933 3772724483055069856543475)
                  ·
                    refine ⟨5659086724582604784815213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772724483055069856543475 5659086724582604784815213)
                    ·
                      refine ⟨2122157521718476794305705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659086724582604784815213 2122157521718476794305705)
                      ·
                        rfl

theorem cell23_4132887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4132887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132887 prefixEnd_4132887 := by exact prefixLift 4132887
  have htrace : WordTrace (prefixWord ++ tailWord_4132887) baseStart_4132887 baseEnd_4132887 := by
    simpa [prefixWord, tailWord_4132887, baseEnd_4132887] using wordTrace_append hprefix tailTrace_4132887
  have hstable : (prefixWord ++ tailWord_4132887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132887).length < 2 ^ (prefixWord ++ tailWord_4132887).sum := by decide
  have hdescent : baseEnd_4132887 < baseStart_4132887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132910 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4132910 : Nat := 118140960795 + 4132910 * 2 ^ 59
def prefixEnd_4132910 : Nat := 4983230072969 + 3 ^ 40 * 4132910 * 2
def baseEnd_4132910 : Nat := 2122169331773530204318099

theorem tailTrace_4132910 : CollatzResearch.WordTrace tailWord_4132910 prefixEnd_4132910 2122169331773530204318099 := by
  unfold tailWord_4132910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842451432147548709741523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100493074304786926451954789 18842451432147548709741523)
  ·
    refine ⟨28263677148221323064612285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18842451432147548709741523 28263677148221323064612285)
    ·
      refine ⟨10598878930582996149229607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28263677148221323064612285 10598878930582996149229607)
      ·
        refine ⟨15898318395874494223844411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598878930582996149229607 15898318395874494223844411)
        ·
          refine ⟨23847477593811741335766617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15898318395874494223844411 23847477593811741335766617)
          ·
            refine ⟨17885608195358806001824963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23847477593811741335766617 17885608195358806001824963)
            ·
              refine ⟨26828412293038209002737445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17885608195358806001824963 26828412293038209002737445)
              ·
                refine ⟨5030327304944664188013271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26828412293038209002737445 5030327304944664188013271)
                ·
                  refine ⟨7545490957416996282019907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030327304944664188013271 7545490957416996282019907)
                  ·
                    refine ⟨11318236436125494423029861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545490957416996282019907 11318236436125494423029861)
                    ·
                      refine ⟨2122169331773530204318099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11318236436125494423029861 2122169331773530204318099)
                      ·
                        rfl

theorem cell23_4132910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4132910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132910 prefixEnd_4132910 := by exact prefixLift 4132910
  have htrace : WordTrace (prefixWord ++ tailWord_4132910) baseStart_4132910 baseEnd_4132910 := by
    simpa [prefixWord, tailWord_4132910, baseEnd_4132910] using wordTrace_append hprefix tailTrace_4132910
  have hstable : (prefixWord ++ tailWord_4132910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132910).length < 2 ^ (prefixWord ++ tailWord_4132910).sum := by decide
  have hdescent : baseEnd_4132910 < baseStart_4132910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132921 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4132921 : Nat := 118140960795 + 4132921 * 2 ^ 59
def prefixEnd_4132921 : Nat := 4983230072969 + 3 ^ 40 * 4132921 * 2
def baseEnd_4132921 : Nat := 2122174980060729661280549

theorem tailTrace_4132921 : CollatzResearch.WordTrace tailWord_4132921 prefixEnd_4132921 2122174980060729661280549 := by
  unfold tailWord_4132921
  simp only [CollatzResearch.WordTrace]
  refine ⟨150740012660140538556582617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100493341773427025704388411 150740012660140538556582617)
  ·
    refine ⟨113055009495105403917436963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150740012660140538556582617 113055009495105403917436963)
    ·
      refine ⟨169582514242658105876155445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113055009495105403917436963 169582514242658105876155445)
      ·
        refine ⟨15898360710249197425889573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169582514242658105876155445 15898360710249197425889573)
        ·
          refine ⟨2980942633171724517354295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15898360710249197425889573 2980942633171724517354295)
          ·
            refine ⟨4471413949757586776031443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980942633171724517354295 4471413949757586776031443)
            ·
              refine ⟨6707120924636380164047165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471413949757586776031443 6707120924636380164047165)
              ·
                refine ⟨2515170346738642561517687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707120924636380164047165 2515170346738642561517687)
                ·
                  refine ⟨3772755520107963842276531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515170346738642561517687 3772755520107963842276531)
                  ·
                    refine ⟨5659133280161945763414797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772755520107963842276531 5659133280161945763414797)
                    ·
                      refine ⟨2122174980060729661280549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659133280161945763414797 2122174980060729661280549)
                      ·
                        rfl

theorem cell23_4132921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4132921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132921 prefixEnd_4132921 := by exact prefixLift 4132921
  have htrace : WordTrace (prefixWord ++ tailWord_4132921) baseStart_4132921 baseEnd_4132921 := by
    simpa [prefixWord, tailWord_4132921, baseEnd_4132921] using wordTrace_append hprefix tailTrace_4132921
  have hstable : (prefixWord ++ tailWord_4132921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132921).length < 2 ^ (prefixWord ++ tailWord_4132921).sum := by decide
  have hdescent : baseEnd_4132921 < baseStart_4132921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132950 : List Nat := [5, 2, 2, 1, 1, 1, 1, 10]
def baseStart_4132950 : Nat := 118140960795 + 4132950 * 2 ^ 59
def prefixEnd_4132950 : Nat := 4983230072969 + 3 ^ 40 * 4132950 * 2
def baseEnd_4132950 : Nat := 78599624851841112882145

theorem tailTrace_4132950 : CollatzResearch.WordTrace tailWord_4132950 prefixEnd_4132950 78599624851841112882145 := by
  unfold tailWord_4132950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421316898564717281836769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100494046918023651006258869 9421316898564717281836769)
  ·
    refine ⟨7065987673923537961377577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9421316898564717281836769 7065987673923537961377577)
    ·
      refine ⟨5299490755442653471033183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7065987673923537961377577 5299490755442653471033183)
      ·
        refine ⟨7949236133163980206549775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299490755442653471033183 7949236133163980206549775)
        ·
          refine ⟨11923854199745970309824663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949236133163980206549775 11923854199745970309824663)
          ·
            refine ⟨17885781299618955464736995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923854199745970309824663 17885781299618955464736995)
            ·
              refine ⟨26828671949428433197105493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17885781299618955464736995 26828671949428433197105493)
              ·
                refine ⟨78599624851841112882145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26828671949428433197105493 78599624851841112882145)
                ·
                  rfl

theorem cell23_4132950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_4132950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4132950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4132950 prefixEnd_4132950 := by exact prefixLift 4132950
  have htrace : WordTrace (prefixWord ++ tailWord_4132950) baseStart_4132950 baseEnd_4132950 := by
    simpa [prefixWord, tailWord_4132950, baseEnd_4132950] using wordTrace_append hprefix tailTrace_4132950
  have hstable : (prefixWord ++ tailWord_4132950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132950).length < 2 ^ (prefixWord ++ tailWord_4132950).sum := by decide
  have hdescent : baseEnd_4132950 < baseStart_4132950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133013 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4133013 : Nat := 118140960795 + 4133013 * 2 ^ 59
def prefixEnd_4133013 : Nat := 4983230072969 + 3 ^ 40 * 4133013 * 2
def baseEnd_4133013 : Nat := 2122222220280943301330125

theorem tailTrace_4133013 : CollatzResearch.WordTrace tailWord_4133013 prefixEnd_4133013 2122222220280943301330125 := by
  unfold tailWord_4133013
  simp only [CollatzResearch.WordTrace]
  refine ⟨150743368175807238268931693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100495578783871492179287795 150743368175807238268931693)
  ·
    refine ⟨56528763065927714350849385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150743368175807238268931693 56528763065927714350849385)
    ·
      refine ⟨42396572299445785763137039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56528763065927714350849385 42396572299445785763137039)
      ·
        refine ⟨63594858449168678644705559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42396572299445785763137039 63594858449168678644705559)
        ·
          refine ⟨95392287673753017967058339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63594858449168678644705559 95392287673753017967058339)
          ·
            refine ⟨143088431510629526950587509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95392287673753017967058339 143088431510629526950587509)
            ·
              refine ⟨13414540454121518151617579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143088431510629526950587509 13414540454121518151617579)
              ·
                refine ⟨20121810681182277227426369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13414540454121518151617579 20121810681182277227426369)
                ·
                  refine ⟨15091358010886707920569777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20121810681182277227426369 15091358010886707920569777)
                  ·
                    refine ⟨11318518508165030940427333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15091358010886707920569777 11318518508165030940427333)
                    ·
                      refine ⟨2122222220280943301330125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11318518508165030940427333 2122222220280943301330125)
                      ·
                        rfl

theorem cell23_4133013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4133013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133013 prefixEnd_4133013 := by exact prefixLift 4133013
  have htrace : WordTrace (prefixWord ++ tailWord_4133013) baseStart_4133013 baseEnd_4133013 := by
    simpa [prefixWord, tailWord_4133013, baseEnd_4133013] using wordTrace_append hprefix tailTrace_4133013
  have hstable : (prefixWord ++ tailWord_4133013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133013).length < 2 ^ (prefixWord ++ tailWord_4133013).sum := by decide
  have hdescent : baseEnd_4133013 < baseStart_4133013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133023 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 9]
def baseStart_4133023 : Nat := 118140960795 + 4133023 * 2 ^ 59
def prefixEnd_4133023 : Nat := 4983230072969 + 3 ^ 40 * 4133023 * 2
def baseEnd_4133023 : Nat := 235803039454165362467231

theorem tailTrace_4133023 : CollatzResearch.WordTrace tailWord_4133023 prefixEnd_4133023 235803039454165362467231 := by
  unfold tailWord_4133023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150743732905771009976795723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100495821937180673317863815 150743732905771009976795723)
  ·
    refine ⟨226115599358656514965193585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150743732905771009976795723 226115599358656514965193585)
    ·
      refine ⟨169586699518992386223895189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226115599358656514965193585 169586699518992386223895189)
      ·
        refine ⟨7949376539952768104245087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169586699518992386223895189 7949376539952768104245087)
        ·
          refine ⟨11924064809929152156367631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949376539952768104245087 11924064809929152156367631)
          ·
            refine ⟨17886097214893728234551447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924064809929152156367631 17886097214893728234551447)
            ·
              refine ⟨26829145822340592351827171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886097214893728234551447 26829145822340592351827171)
              ·
                refine ⟨40243718733510888527740757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26829145822340592351827171 40243718733510888527740757)
                ·
                  refine ⟨235803039454165362467231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40243718733510888527740757 235803039454165362467231)
                  ·
                    rfl

theorem cell23_4133023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 9].length) (baseStart_4133023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133023 prefixEnd_4133023 := by exact prefixLift 4133023
  have htrace : WordTrace (prefixWord ++ tailWord_4133023) baseStart_4133023 baseEnd_4133023 := by
    simpa [prefixWord, tailWord_4133023, baseEnd_4133023] using wordTrace_append hprefix tailTrace_4133023
  have hstable : (prefixWord ++ tailWord_4133023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133023).length < 2 ^ (prefixWord ++ tailWord_4133023).sum := by decide
  have hdescent : baseEnd_4133023 < baseStart_4133023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133053 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_4133053 : Nat := 118140960795 + 4133053 * 2 ^ 59
def prefixEnd_4133053 : Nat := 4983230072969 + 3 ^ 40 * 4133053 * 2
def baseEnd_4133053 : Nat := 707414253169041048276647

theorem tailTrace_4133053 : CollatzResearch.WordTrace tailWord_4133053 prefixEnd_4133053 707414253169041048276647 := by
  unfold tailWord_4133053
  simp only [CollatzResearch.WordTrace]
  refine ⟨150744827095662325100387813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100496551397108216733591875 150744827095662325100387813)
  ·
    refine ⟨28264655080436685956322715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150744827095662325100387813 28264655080436685956322715)
    ·
      refine ⟨42396982620655028934484073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28264655080436685956322715 42396982620655028934484073)
      ·
        refine ⟨31797736965491271700863055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42396982620655028934484073 31797736965491271700863055)
        ·
          refine ⟨47696605448236907551294583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31797736965491271700863055 47696605448236907551294583)
          ·
            refine ⟨71544908172355361326941875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47696605448236907551294583 71544908172355361326941875)
            ·
              refine ⟨107317362258533041990412813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71544908172355361326941875 107317362258533041990412813)
              ·
                refine ⟨40244010846949890746404805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107317362258533041990412813 40244010846949890746404805)
                ·
                  refine ⟨7545752033803104514950901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40244010846949890746404805 7545752033803104514950901)
                  ·
                    refine ⟨707414253169041048276647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7545752033803104514950901 707414253169041048276647)
                    ·
                      rfl

theorem cell23_4133053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_4133053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133053 prefixEnd_4133053 := by exact prefixLift 4133053
  have htrace : WordTrace (prefixWord ++ tailWord_4133053) baseStart_4133053 baseEnd_4133053 := by
    simpa [prefixWord, tailWord_4133053, baseEnd_4133053] using wordTrace_append hprefix tailTrace_4133053
  have hstable : (prefixWord ++ tailWord_4133053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133053).length < 2 ^ (prefixWord ++ tailWord_4133053).sum := by decide
  have hdescent : baseEnd_4133053 < baseStart_4133053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133057 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 7]
def baseStart_4133057 : Nat := 118140960795 + 4133057 * 2 ^ 59
def prefixEnd_4133057 : Nat := 4983230072969 + 3 ^ 40 * 4133057 * 2
def baseEnd_4133057 : Nat := 235804979269971236575547

theorem tailTrace_4133057 : CollatzResearch.WordTrace tailWord_4133057 prefixEnd_4133057 235804979269971236575547 := by
  unfold tailWord_4133057
  simp only [CollatzResearch.WordTrace]
  refine ⟨150744972987647833783533425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100496648658431889189022283 150744972987647833783533425)
  ·
    refine ⟨113058729740735875337650069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150744972987647833783533425 113058729740735875337650069)
    ·
      refine ⟨5299627956596994156452347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113058729740735875337650069 5299627956596994156452347)
      ·
        refine ⟨7949441934895491234678521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299627956596994156452347 7949441934895491234678521)
        ·
          refine ⟨5962081451171618426008891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949441934895491234678521 5962081451171618426008891)
          ·
            refine ⟨8943122176757427639013337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962081451171618426008891 8943122176757427639013337)
            ·
              refine ⟨6707341632568070729260003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943122176757427639013337 6707341632568070729260003)
              ·
                refine ⟨10061012448852106093890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707341632568070729260003 10061012448852106093890005)
                ·
                  refine ⟨235804979269971236575547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10061012448852106093890005 235804979269971236575547)
                  ·
                    rfl

theorem cell23_4133057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_4133057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133057 prefixEnd_4133057 := by exact prefixLift 4133057
  have htrace : WordTrace (prefixWord ++ tailWord_4133057) baseStart_4133057 baseEnd_4133057 := by
    simpa [prefixWord, tailWord_4133057, baseEnd_4133057] using wordTrace_append hprefix tailTrace_4133057
  have hstable : (prefixWord ++ tailWord_4133057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133057).length < 2 ^ (prefixWord ++ tailWord_4133057).sum := by decide
  have hdescent : baseEnd_4133057 < baseStart_4133057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133068 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4133068 : Nat := 118140960795 + 4133068 * 2 ^ 59
def prefixEnd_4133068 : Nat := 4983230072969 + 3 ^ 40 * 4133068 * 2
def baseEnd_4133068 : Nat := 2122250461716940586142373

theorem tailTrace_4133068 : CollatzResearch.WordTrace tailWord_4133068 prefixEnd_4133068 2122250461716940586142373 := by
  unfold tailWord_4133068
  simp only [CollatzResearch.WordTrace]
  refine ⟨75372687095303991331091929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100496916127071988441455905 75372687095303991331091929)
  ·
    refine ⟨56529515321477993498318947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75372687095303991331091929 56529515321477993498318947)
    ·
      refine ⟨84794272982216990247478421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56529515321477993498318947 84794272982216990247478421)
      ·
        refine ⟨3974731546041421417850551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84794272982216990247478421 3974731546041421417850551)
        ·
          refine ⟨5962097319062132126775827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974731546041421417850551 5962097319062132126775827)
          ·
            refine ⟨8943145978593198190163741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962097319062132126775827 8943145978593198190163741)
            ·
              refine ⟨3353679741972449321311403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8943145978593198190163741 3353679741972449321311403)
              ·
                refine ⟨5030519612958673981967105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353679741972449321311403 5030519612958673981967105)
                ·
                  refine ⟨3772889709719005486475329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030519612958673981967105 3772889709719005486475329)
                  ·
                    refine ⟨2829667282289254114856497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772889709719005486475329 2829667282289254114856497)
                    ·
                      refine ⟨2122250461716940586142373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829667282289254114856497 2122250461716940586142373)
                      ·
                        rfl

theorem cell23_4133068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4133068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133068 prefixEnd_4133068 := by exact prefixLift 4133068
  have htrace : WordTrace (prefixWord ++ tailWord_4133068) baseStart_4133068 baseEnd_4133068 := by
    simpa [prefixWord, tailWord_4133068, baseEnd_4133068] using wordTrace_append hprefix tailTrace_4133068
  have hstable : (prefixWord ++ tailWord_4133068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133068).length < 2 ^ (prefixWord ++ tailWord_4133068).sum := by decide
  have hdescent : baseEnd_4133068 < baseStart_4133068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133073 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_4133073 : Nat := 118140960795 + 4133073 * 2 ^ 59
def prefixEnd_4133073 : Nat := 4983230072969 + 3 ^ 40 * 4133073 * 2
def baseEnd_4133073 : Nat := 2122253029120213066579849

theorem tailTrace_4133073 : CollatzResearch.WordTrace tailWord_4133073 prefixEnd_4133073 2122253029120213066579849 := by
  unfold tailWord_4133073
  simp only [CollatzResearch.WordTrace]
  refine ⟨150745556555589868516115873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100497037703726579010743915 150745556555589868516115873)
  ·
    refine ⟨113059167416692401387086905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150745556555589868516115873 113059167416692401387086905)
    ·
      refine ⟨84794375562519301040315179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113059167416692401387086905 84794375562519301040315179)
      ·
        refine ⟨127191563343778951560472769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84794375562519301040315179 127191563343778951560472769)
        ·
          refine ⟨95393672507834213670354577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127191563343778951560472769 95393672507834213670354577)
          ·
            refine ⟨71545254380875660252765933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95393672507834213670354577 71545254380875660252765933)
            ·
              refine ⟨26829470392828372594787225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71545254380875660252765933 26829470392828372594787225)
              ·
                refine ⟨20122102794621279446090419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26829470392828372594787225 20122102794621279446090419)
                ·
                  refine ⟨30183154191931919169135629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20122102794621279446090419 30183154191931919169135629)
                  ·
                    refine ⟨11318682821974469688425861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30183154191931919169135629 11318682821974469688425861)
                    ·
                      refine ⟨2122253029120213066579849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11318682821974469688425861 2122253029120213066579849)
                      ·
                        rfl

theorem cell23_4133073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_4133073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133073 prefixEnd_4133073 := by exact prefixLift 4133073
  have htrace : WordTrace (prefixWord ++ tailWord_4133073) baseStart_4133073 baseEnd_4133073 := by
    simpa [prefixWord, tailWord_4133073, baseEnd_4133073] using wordTrace_append hprefix tailTrace_4133073
  have hstable : (prefixWord ++ tailWord_4133073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133073).length < 2 ^ (prefixWord ++ tailWord_4133073).sum := by decide
  have hdescent : baseEnd_4133073 < baseStart_4133073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
