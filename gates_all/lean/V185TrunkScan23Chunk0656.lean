import V185TrunkScan23Chunk0655

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3878647 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_3878647 : Nat := 118140960795 + 3878647 * 2 ^ 59
def prefixEnd_3878647 : Nat := 4983230072969 + 3 ^ 40 * 3878647 * 2
def baseEnd_3878647 : Nat := 1991610200119391509474933

theorem tailTrace_3878647 : CollatzResearch.WordTrace tailWord_3878647 prefixEnd_3878647 1991610200119391509474933 := by
  unfold tailWord_3878647
  simp only [CollatzResearch.WordTrace]
  refine ⟨141465877979331814014746195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94310585319554542676497463 141465877979331814014746195)
  ·
    refine ⟨212198816968997721022119293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141465877979331814014746195 212198816968997721022119293)
    ·
      refine ⟨79574556363374145383294735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212198816968997721022119293 79574556363374145383294735)
      ·
        refine ⟨119361834545061218074942103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79574556363374145383294735 119361834545061218074942103)
        ·
          refine ⟨179042751817591827112413155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119361834545061218074942103 179042751817591827112413155)
          ·
            refine ⟨268564127726387740668619733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179042751817591827112413155 268564127726387740668619733)
            ·
              refine ⟨6294471743587212671920775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268564127726387740668619733 6294471743587212671920775)
              ·
                refine ⟨9441707615380819007881163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294471743587212671920775 9441707615380819007881163)
                ·
                  refine ⟨14162561423071228511821745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441707615380819007881163 14162561423071228511821745)
                  ·
                    refine ⟨10621921067303421383866309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14162561423071228511821745 10621921067303421383866309)
                    ·
                      refine ⟨1991610200119391509474933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10621921067303421383866309 1991610200119391509474933)
                      ·
                        rfl

theorem cell23_3878647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_3878647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878647 prefixEnd_3878647 := by exact prefixLift 3878647
  have htrace : WordTrace (prefixWord ++ tailWord_3878647) baseStart_3878647 baseEnd_3878647 := by
    simpa [prefixWord, tailWord_3878647, baseEnd_3878647] using wordTrace_append hprefix tailTrace_3878647
  have hstable : (prefixWord ++ tailWord_3878647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878647).length < 2 ^ (prefixWord ++ tailWord_3878647).sum := by decide
  have hdescent : baseEnd_3878647 < baseStart_3878647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878657 : List Nat := [1, 2, 4, 1, 1, 1, 6, 7]
def baseStart_3878657 : Nat := 118140960795 + 3878657 * 2 ^ 59
def prefixEnd_3878657 : Nat := 4983230072969 + 3 ^ 40 * 3878657 * 2
def baseEnd_3878657 : Nat := 73763530923182832235181

theorem tailTrace_3878657 : CollatzResearch.WordTrace tailWord_3878657 prefixEnd_3878657 73763530923182832235181 := by
  unfold tailWord_3878657
  simp only [CollatzResearch.WordTrace]
  refine ⟨141466242709295585722610225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94310828472863723815073483 141466242709295585722610225)
  ·
    refine ⟨106099682031971689291957669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141466242709295585722610225 106099682031971689291957669)
    ·
      refine ⟨19893690380994691742242063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106099682031971689291957669 19893690380994691742242063)
      ·
        refine ⟨29840535571492037613363095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19893690380994691742242063 29840535571492037613363095)
        ·
          refine ⟨44760803357238056420044643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29840535571492037613363095 44760803357238056420044643)
          ·
            refine ⟨67141205035857084630066965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44760803357238056420044643 67141205035857084630066965)
            ·
              refine ⟨3147243986055800842034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67141205035857084630066965 3147243986055800842034389)
              ·
                refine ⟨73763530923182832235181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3147243986055800842034389 73763530923182832235181)
                ·
                  rfl

theorem cell23_3878657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 7].length) (baseStart_3878657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878657 prefixEnd_3878657 := by exact prefixLift 3878657
  have htrace : WordTrace (prefixWord ++ tailWord_3878657) baseStart_3878657 baseEnd_3878657 := by
    simpa [prefixWord, tailWord_3878657, baseEnd_3878657] using wordTrace_append hprefix tailTrace_3878657
  have hstable : (prefixWord ++ tailWord_3878657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878657).length < 2 ^ (prefixWord ++ tailWord_3878657).sum := by decide
  have hdescent : baseEnd_3878657 < baseStart_3878657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878667 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3]
def baseStart_3878667 : Nat := 118140960795 + 3878667 * 2 ^ 59
def prefixEnd_3878667 : Nat := 4983230072969 + 3 ^ 40 * 3878667 * 2
def baseEnd_3878667 : Nat := 1991620469732481431224841

theorem tailTrace_3878667 : CollatzResearch.WordTrace tailWord_3878667 prefixEnd_3878667 1991620469732481431224841 := by
  unfold tailWord_3878667
  simp only [CollatzResearch.WordTrace]
  refine ⟨141466607439259357430474255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94311071626172904953649503 141466607439259357430474255)
  ·
    refine ⟨212199911158889036145711383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141466607439259357430474255 212199911158889036145711383)
    ·
      refine ⟨318299866738333554218567075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212199911158889036145711383 318299866738333554218567075)
      ·
        refine ⟨477449800107500331327850613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318299866738333554218567075 477449800107500331327850613)
        ·
          refine ⟨44760918760078156061985995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 477449800107500331327850613 44760918760078156061985995)
          ·
            refine ⟨67141378140117234092978993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44760918760078156061985995 67141378140117234092978993)
            ·
              refine ⟨50356033605087925569734245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67141378140117234092978993 50356033605087925569734245)
              ·
                refine ⟨9441756300953986044325171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50356033605087925569734245 9441756300953986044325171)
                ·
                  refine ⟨14162634451430979066487757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441756300953986044325171 14162634451430979066487757)
                  ·
                    refine ⟨5310987919286617149932909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14162634451430979066487757 5310987919286617149932909)
                    ·
                      refine ⟨1991620469732481431224841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5310987919286617149932909 1991620469732481431224841)
                      ·
                        rfl

theorem cell23_3878667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].length) (baseStart_3878667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878667 prefixEnd_3878667 := by exact prefixLift 3878667
  have htrace : WordTrace (prefixWord ++ tailWord_3878667) baseStart_3878667 baseEnd_3878667 := by
    simpa [prefixWord, tailWord_3878667, baseEnd_3878667] using wordTrace_append hprefix tailTrace_3878667
  have hstable : (prefixWord ++ tailWord_3878667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878667).length < 2 ^ (prefixWord ++ tailWord_3878667).sum := by decide
  have hdescent : baseEnd_3878667 < baseStart_3878667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878668 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_3878668 : Nat := 118140960795 + 3878668 * 2 ^ 59
def prefixEnd_3878668 : Nat := 4983230072969 + 3 ^ 40 * 3878668 * 2
def baseEnd_3878668 : Nat := 1991620983213135927312337

theorem tailTrace_3878668 : CollatzResearch.WordTrace tailWord_3878668 prefixEnd_3878668 1991620983213135927312337 := by
  unfold tailWord_3878668
  simp only [CollatzResearch.WordTrace]
  refine ⟨70733321956127867300630329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94311095941503823067507105 70733321956127867300630329)
  ·
    refine ⟨53049991467095900475472747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70733321956127867300630329 53049991467095900475472747)
    ·
      refine ⟨79574987200643850713209121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53049991467095900475472747 79574987200643850713209121)
      ·
        refine ⟨59681240400482888034906841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79574987200643850713209121 59681240400482888034906841)
        ·
          refine ⟨44760930300362166026180131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59681240400482888034906841 44760930300362166026180131)
          ·
            refine ⟨67141395450543249039270197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44760930300362166026180131 67141395450543249039270197)
            ·
              refine ⟨6294505823488429597431581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67141395450543249039270197 6294505823488429597431581)
              ·
                refine ⟨2360439683808161099036843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6294505823488429597431581 2360439683808161099036843)
                ·
                  refine ⟨3540659525712241648555265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360439683808161099036843 3540659525712241648555265)
                  ·
                    refine ⟨2655494644284181236416449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540659525712241648555265 2655494644284181236416449)
                    ·
                      refine ⟨1991620983213135927312337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655494644284181236416449 1991620983213135927312337)
                      ·
                        rfl

theorem cell23_3878668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_3878668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878668 prefixEnd_3878668 := by exact prefixLift 3878668
  have htrace : WordTrace (prefixWord ++ tailWord_3878668) baseStart_3878668 baseEnd_3878668 := by
    simpa [prefixWord, tailWord_3878668, baseEnd_3878668] using wordTrace_append hprefix tailTrace_3878668
  have hstable : (prefixWord ++ tailWord_3878668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878668).length < 2 ^ (prefixWord ++ tailWord_3878668).sum := by decide
  have hdescent : baseEnd_3878668 < baseStart_3878668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878674 : List Nat := [3, 2, 4, 1, 1, 3, 9]
def baseStart_3878674 : Nat := 118140960795 + 3878674 * 2 ^ 59
def prefixEnd_3878674 : Nat := 4983230072969 + 3 ^ 40 * 3878674 * 2
def baseEnd_3878674 : Nat := 24587951408605714862189

theorem tailTrace_3878674 : CollatzResearch.WordTrace tailWord_3878674 prefixEnd_3878674 24587951408605714862189 := by
  unfold tailWord_3878674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35366715687558499406494769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94311241833489331750652717 35366715687558499406494769)
  ·
    refine ⟨26525036765668874554871077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35366715687558499406494769 26525036765668874554871077)
    ·
      refine ⟨4973444393562913979038327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26525036765668874554871077 4973444393562913979038327)
      ·
        refine ⟨7460166590344370968557491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973444393562913979038327 7460166590344370968557491)
        ·
          refine ⟨11190249885516556452836237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460166590344370968557491 11190249885516556452836237)
          ·
            refine ⟨4196343707068708669813589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11190249885516556452836237 4196343707068708669813589)
            ·
              refine ⟨24587951408605714862189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4196343707068708669813589 24587951408605714862189)
              ·
                rfl

theorem cell23_3878674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 9].length) (baseStart_3878674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878674 prefixEnd_3878674 := by exact prefixLift 3878674
  have htrace : WordTrace (prefixWord ++ tailWord_3878674) baseStart_3878674 baseEnd_3878674 := by
    simpa [prefixWord, tailWord_3878674, baseEnd_3878674] using wordTrace_append hprefix tailTrace_3878674
  have hstable : (prefixWord ++ tailWord_3878674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878674).length < 2 ^ (prefixWord ++ tailWord_3878674).sum := by decide
  have hdescent : baseEnd_3878674 < baseStart_3878674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878684 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3878684 : Nat := 118140960795 + 3878684 * 2 ^ 59
def prefixEnd_3878684 : Nat := 4983230072969 + 3 ^ 40 * 3878684 * 2
def baseEnd_3878684 : Nat := 1991629198903607864712263

theorem tailTrace_3878684 : CollatzResearch.WordTrace tailWord_3878684 prefixEnd_3878684 1991629198903607864712263 := by
  unfold tailWord_3878684
  simp only [CollatzResearch.WordTrace]
  refine ⟨70733613740098884666921553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94311484986798512889228737 70733613740098884666921553)
  ·
    refine ⟨53050210305074163500191165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70733613740098884666921553 53050210305074163500191165)
    ·
      refine ⟨19893828864402811312571687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53050210305074163500191165 19893828864402811312571687)
      ·
        refine ⟨29840743296604216968857531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19893828864402811312571687 29840743296604216968857531)
        ·
          refine ⟨44761114944906325453286297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29840743296604216968857531 44761114944906325453286297)
          ·
            refine ⟨33570836208679744089964723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44761114944906325453286297 33570836208679744089964723)
            ·
              refine ⟨50356254313019616134947085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33570836208679744089964723 50356254313019616134947085)
              ·
                refine ⟨18883595367382356050605157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50356254313019616134947085 18883595367382356050605157)
                ·
                  refine ⟨3540674131384191759488467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18883595367382356050605157 3540674131384191759488467)
                  ·
                    refine ⟨5311011197076287639232701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540674131384191759488467 5311011197076287639232701)
                    ·
                      refine ⟨1991629198903607864712263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311011197076287639232701 1991629198903607864712263)
                      ·
                        rfl

theorem cell23_3878684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3878684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878684 prefixEnd_3878684 := by exact prefixLift 3878684
  have htrace : WordTrace (prefixWord ++ tailWord_3878684) baseStart_3878684 baseEnd_3878684 := by
    simpa [prefixWord, tailWord_3878684, baseEnd_3878684] using wordTrace_append hprefix tailTrace_3878684
  have hstable : (prefixWord ++ tailWord_3878684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878684).length < 2 ^ (prefixWord ++ tailWord_3878684).sum := by decide
  have hdescent : baseEnd_3878684 < baseStart_3878684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878727 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3878727 : Nat := 118140960795 + 3878727 * 2 ^ 59
def prefixEnd_3878727 : Nat := 4983230072969 + 3 ^ 40 * 3878727 * 2
def baseEnd_3878727 : Nat := 1991651278571751196474565

theorem tailTrace_3878727 : CollatzResearch.WordTrace tailWord_3878727 prefixEnd_3878727 1991651278571751196474565 := by
  unfold tailWord_3878727
  simp only [CollatzResearch.WordTrace]
  refine ⟨141468795819041987677658435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94312530546027991785105623 141468795819041987677658435)
  ·
    refine ⟨212203193728562981516487653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141468795819041987677658435 212203193728562981516487653)
    ·
      refine ⟨39788098824105559034341435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212203193728562981516487653 39788098824105559034341435)
      ·
        refine ⟨59682148236158338551512153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39788098824105559034341435 59682148236158338551512153)
        ·
          refine ⟨44761611177118753913634115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59682148236158338551512153 44761611177118753913634115)
          ·
            refine ⟨67142416765678130870451173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44761611177118753913634115 67142416765678130870451173)
            ·
              refine ⟨12589203143564649538209595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67142416765678130870451173 12589203143564649538209595)
              ·
                refine ⟨18883804715346974307314393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12589203143564649538209595 18883804715346974307314393)
                ·
                  refine ⟨14162853536510230730485795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18883804715346974307314393 14162853536510230730485795)
                  ·
                    refine ⟨21244280304765346095728693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14162853536510230730485795 21244280304765346095728693)
                    ·
                      refine ⟨1991651278571751196474565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21244280304765346095728693 1991651278571751196474565)
                      ·
                        rfl

theorem cell23_3878727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3878727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878727 prefixEnd_3878727 := by exact prefixLift 3878727
  have htrace : WordTrace (prefixWord ++ tailWord_3878727) baseStart_3878727 baseEnd_3878727 := by
    simpa [prefixWord, tailWord_3878727, baseEnd_3878727] using wordTrace_append hprefix tailTrace_3878727
  have hstable : (prefixWord ++ tailWord_3878727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878727).length < 2 ^ (prefixWord ++ tailWord_3878727).sum := by decide
  have hdescent : baseEnd_3878727 < baseStart_3878727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878728 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_3878728 : Nat := 118140960795 + 3878728 * 2 ^ 59
def prefixEnd_3878728 : Nat := 4983230072969 + 3 ^ 40 * 3878728 * 2
def baseEnd_3878728 : Nat := 1991651792052405692562061

theorem tailTrace_3878728 : CollatzResearch.WordTrace tailWord_3878728 prefixEnd_3878728 1991651792052405692562061 := by
  unfold tailWord_3878728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70734416146019182424222419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94312554861358909898963225 70734416146019182424222419)
  ·
    refine ⟨106101624219028773636333629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70734416146019182424222419 106101624219028773636333629)
    ·
      refine ⟨39788109082135790113625111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106101624219028773636333629 39788109082135790113625111)
      ·
        refine ⟨59682163623203685170437667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39788109082135790113625111 59682163623203685170437667)
        ·
          refine ⟨89523245434805527755656501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59682163623203685170437667 89523245434805527755656501)
          ·
            refine ⟨8392804259513018227092797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89523245434805527755656501 8392804259513018227092797)
            ·
              refine ⟨3147301597317381835159799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8392804259513018227092797 3147301597317381835159799)
              ·
                refine ⟨4720952395976072752739699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147301597317381835159799 4720952395976072752739699)
                ·
                  refine ⟨7081428593964109129109549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720952395976072752739699 7081428593964109129109549)
                  ·
                    refine ⟨2655535722736540923416081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7081428593964109129109549 2655535722736540923416081)
                    ·
                      refine ⟨1991651792052405692562061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655535722736540923416081 1991651792052405692562061)
                      ·
                        rfl

theorem cell23_3878728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_3878728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878728 prefixEnd_3878728 := by exact prefixLift 3878728
  have htrace : WordTrace (prefixWord ++ tailWord_3878728) baseStart_3878728 baseEnd_3878728 := by
    simpa [prefixWord, tailWord_3878728, baseEnd_3878728] using wordTrace_append hprefix tailTrace_3878728
  have hstable : (prefixWord ++ tailWord_3878728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878728).length < 2 ^ (prefixWord ++ tailWord_3878728).sum := by decide
  have hdescent : baseEnd_3878728 < baseStart_3878728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878754 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3878754 : Nat := 118140960795 + 3878754 * 2 ^ 59
def prefixEnd_3878754 : Nat := 4983230072969 + 3 ^ 40 * 3878754 * 2
def baseEnd_3878754 : Nat := 1991665142549422590836941

theorem tailTrace_3878754 : CollatzResearch.WordTrace tailWord_3878754 prefixEnd_3878754 1991665142549422590836941 := by
  unfold tailWord_3878754
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367445147486042822222829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94313187059962780859260877 35367445147486042822222829)
  ·
    refine ⟨13262791930307266058333561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35367445147486042822222829 13262791930307266058333561)
    ·
      refine ⟨9947093947730449543750171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13262791930307266058333561 9947093947730449543750171)
      ·
        refine ⟨14920640921595674315625257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947093947730449543750171 14920640921595674315625257)
        ·
          refine ⟨11190480691196755736718943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14920640921595674315625257 11190480691196755736718943)
          ·
            refine ⟨16785721036795133605078415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190480691196755736718943 16785721036795133605078415)
            ·
              refine ⟨25178581555192700407617623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16785721036795133605078415 25178581555192700407617623)
              ·
                refine ⟨37767872332789050611426435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25178581555192700407617623 37767872332789050611426435)
                ·
                  refine ⟨56651808499183575917139653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37767872332789050611426435 56651808499183575917139653)
                  ·
                    refine ⟨10622214093596920484463685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56651808499183575917139653 10622214093596920484463685)
                    ·
                      refine ⟨1991665142549422590836941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10622214093596920484463685 1991665142549422590836941)
                      ·
                        rfl

theorem cell23_3878754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3878754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878754 prefixEnd_3878754 := by exact prefixLift 3878754
  have htrace : WordTrace (prefixWord ++ tailWord_3878754) baseStart_3878754 baseEnd_3878754 := by
    simpa [prefixWord, tailWord_3878754, baseEnd_3878754] using wordTrace_append hprefix tailTrace_3878754
  have hstable : (prefixWord ++ tailWord_3878754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878754).length < 2 ^ (prefixWord ++ tailWord_3878754).sum := by decide
  have hdescent : baseEnd_3878754 < baseStart_3878754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878777 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_3878777 : Nat := 118140960795 + 3878777 * 2 ^ 59
def prefixEnd_3878777 : Nat := 4983230072969 + 3 ^ 40 * 3878777 * 2
def baseEnd_3878777 : Nat := 663892317534825333616445

theorem tailTrace_3878777 : CollatzResearch.WordTrace tailWord_3878777 prefixEnd_3878777 663892317534825333616445 := by
  unfold tailWord_3878777
  simp only [CollatzResearch.WordTrace]
  refine ⟨141470619468860846216978585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94313746312573897477985723 141470619468860846216978585)
  ·
    refine ⟨106102964601645634662733939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141470619468860846216978585 106102964601645634662733939)
    ·
      refine ⟨159154446902468451994100909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106102964601645634662733939 159154446902468451994100909)
      ·
        refine ⟨59682917588425669497787841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159154446902468451994100909 59682917588425669497787841)
        ·
          refine ⟨44762188191319252123340881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59682917588425669497787841 44762188191319252123340881)
          ·
            refine ⟨33571641143489439092505661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44762188191319252123340881 33571641143489439092505661)
            ·
              refine ⟨12589365428808539659689623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33571641143489439092505661 12589365428808539659689623)
              ·
                refine ⟨18884048143212809489534435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12589365428808539659689623 18884048143212809489534435)
                ·
                  refine ⟨28326072214819214234301653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18884048143212809489534435 28326072214819214234301653)
                  ·
                    refine ⟨663892317534825333616445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28326072214819214234301653 663892317534825333616445)
                    ·
                      rfl

theorem cell23_3878777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_3878777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878777 prefixEnd_3878777 := by exact prefixLift 3878777
  have htrace : WordTrace (prefixWord ++ tailWord_3878777) baseStart_3878777 baseEnd_3878777 := by
    simpa [prefixWord, tailWord_3878777, baseEnd_3878777] using wordTrace_append hprefix tailTrace_3878777
  have hstable : (prefixWord ++ tailWord_3878777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878777).length < 2 ^ (prefixWord ++ tailWord_3878777).sum := by decide
  have hdescent : baseEnd_3878777 < baseStart_3878777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878792 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3878792 : Nat := 118140960795 + 3878792 * 2 ^ 59
def prefixEnd_3878792 : Nat := 4983230072969 + 3 ^ 40 * 3878792 * 2
def baseEnd_3878792 : Nat := 1991684654814293442161767

theorem tailTrace_3878792 : CollatzResearch.WordTrace tailWord_3878792 prefixEnd_3878792 1991684654814293442161767 := by
  unfold tailWord_3878792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70735583281903251889387315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94314111042537669185849753 70735583281903251889387315)
  ·
    refine ⟨106103374922854877834080973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70735583281903251889387315 106103374922854877834080973)
    ·
      refine ⟨39788765596070579187780365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106103374922854877834080973 39788765596070579187780365)
      ·
        refine ⟨14920787098526467195417637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39788765596070579187780365 14920787098526467195417637)
        ·
          refine ⟨2797647580973712599140807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14920787098526467195417637 2797647580973712599140807)
          ·
            refine ⟨4196471371460568898711211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797647580973712599140807 4196471371460568898711211)
            ·
              refine ⟨6294707057190853348066817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196471371460568898711211 6294707057190853348066817)
              ·
                refine ⟨4721030292893140011050113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294707057190853348066817 4721030292893140011050113)
                ·
                  refine ⟨3540772719669855008287585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721030292893140011050113 3540772719669855008287585)
                  ·
                    refine ⟨2655579539752391256215689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540772719669855008287585 2655579539752391256215689)
                    ·
                      refine ⟨1991684654814293442161767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655579539752391256215689 1991684654814293442161767)
                      ·
                        rfl

theorem cell23_3878792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3878792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878792 prefixEnd_3878792 := by exact prefixLift 3878792
  have htrace : WordTrace (prefixWord ++ tailWord_3878792) baseStart_3878792 baseEnd_3878792 := by
    simpa [prefixWord, tailWord_3878792, baseEnd_3878792] using wordTrace_append hprefix tailTrace_3878792
  have hstable : (prefixWord ++ tailWord_3878792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878792).length < 2 ^ (prefixWord ++ tailWord_3878792).sum := by decide
  have hdescent : baseEnd_3878792 < baseStart_3878792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878834 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3878834 : Nat := 118140960795 + 3878834 * 2 ^ 59
def prefixEnd_3878834 : Nat := 4983230072969 + 3 ^ 40 * 3878834 * 2
def baseEnd_3878834 : Nat := 1991706221001782277836573

theorem tailTrace_3878834 : CollatzResearch.WordTrace tailWord_3878834 prefixEnd_3878834 1991706221001782277836573 := by
  unfold tailWord_3878834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35368174607413586237950889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94315132286436229967869037 35368174607413586237950889)
  ·
    refine ⟨26526130955560189678463167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35368174607413586237950889 26526130955560189678463167)
    ·
      refine ⟨39789196433340284517694751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26526130955560189678463167 39789196433340284517694751)
      ·
        refine ⟨59683794650010426776542127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39789196433340284517694751 59683794650010426776542127)
        ·
          refine ⟨89525691975015640164813191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59683794650010426776542127 89525691975015640164813191)
          ·
            refine ⟨134288537962523460247219787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89525691975015640164813191 134288537962523460247219787)
            ·
              refine ⟨201432806943785190370829681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134288537962523460247219787 201432806943785190370829681)
              ·
                refine ⟨151074605207838892778122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201432806943785190370829681 151074605207838892778122261)
                ·
                  refine ⟨7081622119117448098974481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151074605207838892778122261 7081622119117448098974481)
                  ·
                    refine ⟨5311216589338086074230861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081622119117448098974481 5311216589338086074230861)
                    ·
                      refine ⟨1991706221001782277836573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311216589338086074230861 1991706221001782277836573)
                      ·
                        rfl

theorem cell23_3878834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3878834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878834 prefixEnd_3878834 := by exact prefixLift 3878834
  have htrace : WordTrace (prefixWord ++ tailWord_3878834) baseStart_3878834 baseEnd_3878834 := by
    simpa [prefixWord, tailWord_3878834, baseEnd_3878834] using wordTrace_append hprefix tailTrace_3878834
  have hstable : (prefixWord ++ tailWord_3878834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878834).length < 2 ^ (prefixWord ++ tailWord_3878834).sum := by decide
  have hdescent : baseEnd_3878834 < baseStart_3878834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878881 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3878881 : Nat := 118140960795 + 3878881 * 2 ^ 59
def prefixEnd_3878881 : Nat := 4983230072969 + 3 ^ 40 * 3878881 * 2
def baseEnd_3878881 : Nat := 1991730354592543593948857

theorem tailTrace_3878881 : CollatzResearch.WordTrace tailWord_3878881 prefixEnd_3878881 1991730354592543593948857 := by
  unfold tailWord_3878881
  simp only [CollatzResearch.WordTrace]
  refine ⟨141474412660484071978764497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94316275106989381319176331 141474412660484071978764497)
  ·
    refine ⟨106105809495363053984073373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141474412660484071978764497 106105809495363053984073373)
    ·
      refine ⟨39789678560761145244027515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106105809495363053984073373 39789678560761145244027515)
      ·
        refine ⟨59684517841141717866041273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39789678560761145244027515 59684517841141717866041273)
        ·
          refine ⟨44763388380856288399530955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59684517841141717866041273 44763388380856288399530955)
          ·
            refine ⟨67145082571284432599296433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44763388380856288399530955 67145082571284432599296433)
            ·
              refine ⟨50358811928463324449472325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67145082571284432599296433 50358811928463324449472325)
              ·
                refine ⟨9442277236586873334276061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50358811928463324449472325 9442277236586873334276061)
                ·
                  refine ⟨3540853963720077500353523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9442277236586873334276061 3540853963720077500353523)
                  ·
                    refine ⟨5311280945580116250530285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540853963720077500353523 5311280945580116250530285)
                    ·
                      refine ⟨1991730354592543593948857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311280945580116250530285 1991730354592543593948857)
                      ·
                        rfl

theorem cell23_3878881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3878881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878881 prefixEnd_3878881 := by exact prefixLift 3878881
  have htrace : WordTrace (prefixWord ++ tailWord_3878881) baseStart_3878881 baseEnd_3878881 := by
    simpa [prefixWord, tailWord_3878881, baseEnd_3878881] using wordTrace_append hprefix tailTrace_3878881
  have hstable : (prefixWord ++ tailWord_3878881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878881).length < 2 ^ (prefixWord ++ tailWord_3878881).sum := by decide
  have hdescent : baseEnd_3878881 < baseStart_3878881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878884 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3878884 : Nat := 118140960795 + 3878884 * 2 ^ 59
def prefixEnd_3878884 : Nat := 4983230072969 + 3 ^ 40 * 3878884 * 2
def baseEnd_3878884 : Nat := 663910631678169027403781

theorem tailTrace_3878884 : CollatzResearch.WordTrace tailWord_3878884 prefixEnd_3878884 663910631678169027403781 := by
  unfold tailWord_3878884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70737261039736601745561853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94316348052982135660749137 70737261039736601745561853)
  ·
    refine ⟨26526472889901225654585695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70737261039736601745561853 26526472889901225654585695)
    ·
      refine ⟨39789709334851838481878543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26526472889901225654585695 39789709334851838481878543)
      ·
        refine ⟨59684564002277757722817815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39789709334851838481878543 59684564002277757722817815)
        ·
          refine ⟨89526846003416636584226723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59684564002277757722817815 89526846003416636584226723)
          ·
            refine ⟨134290269005124954876340085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89526846003416636584226723 134290269005124954876340085)
            ·
              refine ⟨12589712719230464519656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134290269005124954876340085 12589712719230464519656883)
              ·
                refine ⟨18884569078845696779485325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12589712719230464519656883 18884569078845696779485325)
                ·
                  refine ⟨7081713404567136292306997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18884569078845696779485325 7081713404567136292306997)
                  ·
                    refine ⟨663910631678169027403781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7081713404567136292306997 663910631678169027403781)
                    ·
                      rfl

theorem cell23_3878884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3878884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878884 prefixEnd_3878884 := by exact prefixLift 3878884
  have htrace : WordTrace (prefixWord ++ tailWord_3878884) baseStart_3878884 baseEnd_3878884 := by
    simpa [prefixWord, tailWord_3878884, baseEnd_3878884] using wordTrace_append hprefix tailTrace_3878884
  have hstable : (prefixWord ++ tailWord_3878884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878884).length < 2 ^ (prefixWord ++ tailWord_3878884).sum := by decide
  have hdescent : baseEnd_3878884 < baseStart_3878884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878924 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3878924 : Nat := 118140960795 + 3878924 * 2 ^ 59
def prefixEnd_3878924 : Nat := 4983230072969 + 3 ^ 40 * 3878924 * 2
def baseEnd_3878924 : Nat := 1991752434260686925711159

theorem tailTrace_3878924 : CollatzResearch.WordTrace tailWord_3878924 prefixEnd_3878924 1991752434260686925711159 := by
  unfold tailWord_3878924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70737990499664145161289913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94317320666218860215053217 70737990499664145161289913)
  ·
    refine ⟨53053492874748108870967435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70737990499664145161289913 53053492874748108870967435)
    ·
      refine ⟨79580239312122163306451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53053492874748108870967435 79580239312122163306451153)
      ·
        refine ⟨59685179484091622479838365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79580239312122163306451153 59685179484091622479838365)
        ·
          refine ⟨22381942306534358429939387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59685179484091622479838365 22381942306534358429939387)
          ·
            refine ⟨33572913459801537644909081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22381942306534358429939387 33572913459801537644909081)
            ·
              refine ⟨25179685094851153233681811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33572913459801537644909081 25179685094851153233681811)
              ·
                refine ⟨37769527642276729850522717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25179685094851153233681811 37769527642276729850522717)
                ·
                  refine ⟨14163572865853773693946019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37769527642276729850522717 14163572865853773693946019)
                  ·
                    refine ⟨21245359298780660540919029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14163572865853773693946019 21245359298780660540919029)
                    ·
                      refine ⟨1991752434260686925711159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21245359298780660540919029 1991752434260686925711159)
                      ·
                        rfl

theorem cell23_3878924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3878924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878924 prefixEnd_3878924 := by exact prefixLift 3878924
  have htrace : WordTrace (prefixWord ++ tailWord_3878924) baseStart_3878924 baseEnd_3878924 := by
    simpa [prefixWord, tailWord_3878924, baseEnd_3878924] using wordTrace_append hprefix tailTrace_3878924
  have hstable : (prefixWord ++ tailWord_3878924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878924).length < 2 ^ (prefixWord ++ tailWord_3878924).sum := by decide
  have hdescent : baseEnd_3878924 < baseStart_3878924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878931 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 2, 4]
def baseStart_3878931 : Nat := 118140960795 + 3878931 * 2 ^ 59
def prefixEnd_3878931 : Nat := 4983230072969 + 3 ^ 40 * 3878931 * 2
def baseEnd_3878931 : Nat := 663918676208422799441209

theorem tailTrace_3878931 : CollatzResearch.WordTrace tailWord_3878931 prefixEnd_3878931 663918676208422799441209 := by
  unfold tailWord_3878931
  simp only [CollatzResearch.WordTrace]
  refine ⟨141476236310302930518084647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94317490873535287012056431 141476236310302930518084647)
  ·
    refine ⟨212214354465454395777126971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141476236310302930518084647 212214354465454395777126971)
    ·
      refine ⟨318321531698181593665690457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212214354465454395777126971 318321531698181593665690457)
      ·
        refine ⟨238741148773636195249267843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318321531698181593665690457 238741148773636195249267843)
        ·
          refine ⟨358111723160454292873901765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238741148773636195249267843 358111723160454292873901765)
          ·
            refine ⟨67145948092585179913856581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358111723160454292873901765 67145948092585179913856581)
            ·
              refine ⟨12589865267359721233848109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67145948092585179913856581 12589865267359721233848109)
              ·
                refine ⟨4721199475259895462693041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12589865267359721233848109 4721199475259895462693041)
                ·
                  refine ⟨3540899606444921597019781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721199475259895462693041 3540899606444921597019781)
                  ·
                    refine ⟨663918676208422799441209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3540899606444921597019781 663918676208422799441209)
                    ·
                      rfl

theorem cell23_3878931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 4].length) (baseStart_3878931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878931 prefixEnd_3878931 := by exact prefixLift 3878931
  have htrace : WordTrace (prefixWord ++ tailWord_3878931) baseStart_3878931 baseEnd_3878931 := by
    simpa [prefixWord, tailWord_3878931, baseEnd_3878931] using wordTrace_append hprefix tailTrace_3878931
  have hstable : (prefixWord ++ tailWord_3878931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878931).length < 2 ^ (prefixWord ++ tailWord_3878931).sum := by decide
  have hdescent : baseEnd_3878931 < baseStart_3878931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878932 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3878932 : Nat := 118140960795 + 3878932 * 2 ^ 59
def prefixEnd_3878932 : Nat := 4983230072969 + 3 ^ 40 * 3878932 * 2
def baseEnd_3878932 : Nat := 1991756542105922894411123

theorem tailTrace_3878932 : CollatzResearch.WordTrace tailWord_3878932 prefixEnd_3878932 1991756542105922894411123 := by
  unfold tailWord_3878932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70738136391649653844435525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94317515188866205125914033 70738136391649653844435525)
  ·
    refine ⟨13263400573434310095831661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70738136391649653844435525 13263400573434310095831661)
    ·
      refine ⟨4973775215037866285936873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13263400573434310095831661 4973775215037866285936873)
      ·
        refine ⟨3730331411278399714452655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973775215037866285936873 3730331411278399714452655)
        ·
          refine ⟨5595497116917599571678983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730331411278399714452655 5595497116917599571678983)
          ·
            refine ⟨8393245675376399357518475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595497116917599571678983 8393245675376399357518475)
            ·
              refine ⟨12589868513064599036277713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393245675376399357518475 12589868513064599036277713)
              ·
                refine ⟨9442401384798449277208285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12589868513064599036277713 9442401384798449277208285)
                ·
                  refine ⟨3540900519299418478953107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9442401384798449277208285 3540900519299418478953107)
                  ·
                    refine ⟨5311350778949127718429661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540900519299418478953107 5311350778949127718429661)
                    ·
                      refine ⟨1991756542105922894411123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311350778949127718429661 1991756542105922894411123)
                      ·
                        rfl

theorem cell23_3878932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3878932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878932 prefixEnd_3878932 := by exact prefixLift 3878932
  have htrace : WordTrace (prefixWord ++ tailWord_3878932) baseStart_3878932 baseEnd_3878932 := by
    simpa [prefixWord, tailWord_3878932, baseEnd_3878932] using wordTrace_append hprefix tailTrace_3878932
  have hstable : (prefixWord ++ tailWord_3878932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878932).length < 2 ^ (prefixWord ++ tailWord_3878932).sum := by decide
  have hdescent : baseEnd_3878932 < baseStart_3878932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878938 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_3878938 : Nat := 118140960795 + 3878938 * 2 ^ 59
def prefixEnd_3878938 : Nat := 4983230072969 + 3 ^ 40 * 3878938 * 2
def baseEnd_3878938 : Nat := 1991759622989849870936095

theorem tailTrace_3878938 : CollatzResearch.WordTrace tailWord_3878938 prefixEnd_3878938 1991759622989849870936095 := by
  unfold tailWord_3878938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35369122905319392678397367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94317661080851713809059645 35369122905319392678397367)
  ·
    refine ⟨53053684357979089017596051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35369122905319392678397367 53053684357979089017596051)
    ·
      refine ⟨79580526536968633526394077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53053684357979089017596051 79580526536968633526394077)
      ·
        refine ⟨29842697451363237572397779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79580526536968633526394077 29842697451363237572397779)
        ·
          refine ⟨44764046177044856358596669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29842697451363237572397779 44764046177044856358596669)
          ·
            refine ⟨16786517316391821134473751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44764046177044856358596669 16786517316391821134473751)
            ·
              refine ⟨25179775974587731701710627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16786517316391821134473751 25179775974587731701710627)
              ·
                refine ⟨37769663961881597552565941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25179775974587731701710627 37769663961881597552565941)
                ·
                  refine ⟨3540905996426399770553057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37769663961881597552565941 3540905996426399770553057)
                  ·
                    refine ⟨2655679497319799827914793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540905996426399770553057 2655679497319799827914793)
                    ·
                      refine ⟨1991759622989849870936095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655679497319799827914793 1991759622989849870936095)
                      ·
                        rfl

theorem cell23_3878938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_3878938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878938 prefixEnd_3878938 := by exact prefixLift 3878938
  have htrace : WordTrace (prefixWord ++ tailWord_3878938) baseStart_3878938 baseEnd_3878938 := by
    simpa [prefixWord, tailWord_3878938, baseEnd_3878938] using wordTrace_append hprefix tailTrace_3878938
  have hstable : (prefixWord ++ tailWord_3878938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878938).length < 2 ^ (prefixWord ++ tailWord_3878938).sum := by decide
  have hdescent : baseEnd_3878938 < baseStart_3878938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878952 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3878952 : Nat := 118140960795 + 3878952 * 2 ^ 59
def prefixEnd_3878952 : Nat := 4983230072969 + 3 ^ 40 * 3878952 * 2
def baseEnd_3878952 : Nat := 663922270573004272053677

theorem tailTrace_3878952 : CollatzResearch.WordTrace tailWord_3878952 prefixEnd_3878952 663922270573004272053677 := by
  unfold tailWord_3878952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70738501121613425552299555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94318001495484567403066073 70738501121613425552299555)
  ·
    refine ⟨106107751682420138328449333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70738501121613425552299555 106107751682420138328449333)
    ·
      refine ⟨9947601720226887968292125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106107751682420138328449333 9947601720226887968292125)
      ·
        refine ⟨3730350645085082988109547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9947601720226887968292125 3730350645085082988109547)
        ·
          refine ⟨5595525967627624482164321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730350645085082988109547 5595525967627624482164321)
          ·
            refine ⟨4196644475720718361623241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5595525967627624482164321 4196644475720718361623241)
            ·
              refine ⟨3147483356790538771217431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196644475720718361623241 3147483356790538771217431)
              ·
                refine ⟨4721225035185808156826147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147483356790538771217431 4721225035185808156826147)
                ·
                  refine ⟨7081837552778712235239221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721225035185808156826147 7081837552778712235239221)
                  ·
                    refine ⟨663922270573004272053677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7081837552778712235239221 663922270573004272053677)
                    ·
                      rfl

theorem cell23_3878952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3878952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878952 prefixEnd_3878952 := by exact prefixLift 3878952
  have htrace : WordTrace (prefixWord ++ tailWord_3878952) baseStart_3878952 baseEnd_3878952 := by
    simpa [prefixWord, tailWord_3878952, baseEnd_3878952] using wordTrace_append hprefix tailTrace_3878952
  have hstable : (prefixWord ++ tailWord_3878952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878952).length < 2 ^ (prefixWord ++ tailWord_3878952).sum := by decide
  have hdescent : baseEnd_3878952 < baseStart_3878952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 3]
def baseStart_3878971 : Nat := 118140960795 + 3878971 * 2 ^ 59
def prefixEnd_3878971 : Nat := 4983230072969 + 3 ^ 40 * 3878971 * 2
def baseEnd_3878971 : Nat := 1991776567851448241823443

theorem tailTrace_3878971 : CollatzResearch.WordTrace tailWord_3878971 prefixEnd_3878971 1991776567851448241823443 := by
  unfold tailWord_3878971
  simp only [CollatzResearch.WordTrace]
  refine ⟨141477695230158017349540767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94318463486772011566360511 141477695230158017349540767)
  ·
    refine ⟨212216542845237026024311151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141477695230158017349540767 212216542845237026024311151)
    ·
      refine ⟨318324814267855539036466727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212216542845237026024311151 318324814267855539036466727)
      ·
        refine ⟨477487221401783308554700091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318324814267855539036466727 477487221401783308554700091)
        ·
          refine ⟨716230832102674962832050137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477487221401783308554700091 716230832102674962832050137)
          ·
            refine ⟨537173124077006222124037603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716230832102674962832050137 537173124077006222124037603)
            ·
              refine ⟨805759686115509333186056405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537173124077006222124037603 805759686115509333186056405)
              ·
                refine ⟨18884992643332249996548197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 805759686115509333186056405 18884992643332249996548197)
                ·
                  refine ⟨3540936120624796874352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18884992643332249996548197 3540936120624796874352787)
                  ·
                    refine ⟨5311404180937195311529181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540936120624796874352787 5311404180937195311529181)
                    ·
                      refine ⟨1991776567851448241823443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311404180937195311529181 1991776567851448241823443)
                      ·
                        rfl

theorem cell23_3878971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 3].length) (baseStart_3878971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878971 prefixEnd_3878971 := by exact prefixLift 3878971
  have htrace : WordTrace (prefixWord ++ tailWord_3878971) baseStart_3878971 baseEnd_3878971 := by
    simpa [prefixWord, tailWord_3878971, baseEnd_3878971] using wordTrace_append hprefix tailTrace_3878971
  have hstable : (prefixWord ++ tailWord_3878971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878971).length < 2 ^ (prefixWord ++ tailWord_3878971).sum := by decide
  have hdescent : baseEnd_3878971 < baseStart_3878971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878982 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3878982 : Nat := 118140960795 + 3878982 * 2 ^ 59
def prefixEnd_3878982 : Nat := 4983230072969 + 3 ^ 40 * 3878982 * 2
def baseEnd_3878982 : Nat := 663927405379549232928631

theorem tailTrace_3878982 : CollatzResearch.WordTrace tailWord_3878982 prefixEnd_3878982 663927405379549232928631 := by
  unfold tailWord_3878982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421190513534942694630975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94318730955412110818794133 4421190513534942694630975)
  ·
    refine ⟨6631785770302414041946463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421190513534942694630975 6631785770302414041946463)
    ·
      refine ⟨9947678655453621062919695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631785770302414041946463 9947678655453621062919695)
      ·
        refine ⟨14921517983180431594379543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947678655453621062919695 14921517983180431594379543)
        ·
          refine ⟨22382276974770647391569315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14921517983180431594379543 22382276974770647391569315)
          ·
            refine ⟨33573415462155971087353973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22382276974770647391569315 33573415462155971087353973)
            ·
              refine ⟨3147507699577122289439435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33573415462155971087353973 3147507699577122289439435)
              ·
                refine ⟨4721261549365683434159153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147507699577122289439435 4721261549365683434159153)
                ·
                  refine ⟨3540946162024262575619365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721261549365683434159153 3540946162024262575619365)
                  ·
                    refine ⟨663927405379549232928631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3540946162024262575619365 663927405379549232928631)
                    ·
                      rfl

theorem cell23_3878982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3878982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878982 prefixEnd_3878982 := by exact prefixLift 3878982
  have htrace : WordTrace (prefixWord ++ tailWord_3878982) baseStart_3878982 baseEnd_3878982 := by
    simpa [prefixWord, tailWord_3878982, baseEnd_3878982] using wordTrace_append hprefix tailTrace_3878982
  have hstable : (prefixWord ++ tailWord_3878982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878982).length < 2 ^ (prefixWord ++ tailWord_3878982).sum := by decide
  have hdescent : baseEnd_3878982 < baseStart_3878982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878988 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3878988 : Nat := 118140960795 + 3878988 * 2 ^ 59
def prefixEnd_3878988 : Nat := 4983230072969 + 3 ^ 40 * 3878988 * 2
def baseEnd_3878988 : Nat := 1991785297022574675310865

theorem tailTrace_3878988 : CollatzResearch.WordTrace tailWord_3878988 prefixEnd_3878988 1991785297022574675310865 := by
  unfold tailWord_3878988
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739157635548214626454809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94318876847397619501939745 70739157635548214626454809)
  ·
    refine ⟨53054368226661160969841107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70739157635548214626454809 53054368226661160969841107)
    ·
      refine ⟨79581552339991741454761661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53054368226661160969841107 79581552339991741454761661)
      ·
        refine ⟨29843082127496903045535623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79581552339991741454761661 29843082127496903045535623)
        ·
          refine ⟨44764623191245354568303435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843082127496903045535623 44764623191245354568303435)
          ·
            refine ⟨67146934786868031852455153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44764623191245354568303435 67146934786868031852455153)
            ·
              refine ⟨50360201090151023889341365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67146934786868031852455153 50360201090151023889341365)
              ·
                refine ⟨4721268852201658489625753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50360201090151023889341365 4721268852201658489625753)
                ·
                  refine ⟨3540951639151243867219315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721268852201658489625753 3540951639151243867219315)
                  ·
                    refine ⟨5311427458726865800828973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540951639151243867219315 5311427458726865800828973)
                    ·
                      refine ⟨1991785297022574675310865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311427458726865800828973 1991785297022574675310865)
                      ·
                        rfl

theorem cell23_3878988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3878988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878988 prefixEnd_3878988 := by exact prefixLift 3878988
  have htrace : WordTrace (prefixWord ++ tailWord_3878988) baseStart_3878988 baseEnd_3878988 := by
    simpa [prefixWord, tailWord_3878988, baseEnd_3878988] using wordTrace_append hprefix tailTrace_3878988
  have hstable : (prefixWord ++ tailWord_3878988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878988).length < 2 ^ (prefixWord ++ tailWord_3878988).sum := by decide
  have hdescent : baseEnd_3878988 < baseStart_3878988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879005 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3879005 : Nat := 118140960795 + 3879005 * 2 ^ 59
def prefixEnd_3879005 : Nat := 4983230072969 + 3 ^ 40 * 3879005 * 2
def baseEnd_3879005 : Nat := 1991794026193701108798287

theorem tailTrace_3879005 : CollatzResearch.WordTrace tailWord_3879005 prefixEnd_3879005 1991794026193701108798287 := by
  unfold tailWord_3879005
  simp only [CollatzResearch.WordTrace]
  refine ⟨141478935312034841156278469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94319290208023227437518979 141478935312034841156278469)
  ·
    refine ⟨26527300371006532716802213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141478935312034841156278469 26527300371006532716802213)
    ·
      refine ⟨4973868819563724884400415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26527300371006532716802213 4973868819563724884400415)
      ·
        refine ⟨7460803229345587326600623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973868819563724884400415 7460803229345587326600623)
        ·
          refine ⟨11191204844018380989900935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460803229345587326600623 11191204844018380989900935)
          ·
            refine ⟨16786807266027571484851403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191204844018380989900935 16786807266027571484851403)
            ·
              refine ⟨25180210899041357227277105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16786807266027571484851403 25180210899041357227277105)
              ·
                refine ⟨18885158174281017920457829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25180210899041357227277105 18885158174281017920457829)
                ·
                  refine ⟨3540967157677690860085843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18885158174281017920457829 3540967157677690860085843)
                  ·
                    refine ⟨5311450736516536290128765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540967157677690860085843 5311450736516536290128765)
                    ·
                      refine ⟨1991794026193701108798287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311450736516536290128765 1991794026193701108798287)
                      ·
                        rfl

theorem cell23_3879005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3879005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879005 prefixEnd_3879005 := by exact prefixLift 3879005
  have htrace : WordTrace (prefixWord ++ tailWord_3879005) baseStart_3879005 baseEnd_3879005 := by
    simpa [prefixWord, tailWord_3879005, baseEnd_3879005] using wordTrace_append hprefix tailTrace_3879005
  have hstable : (prefixWord ++ tailWord_3879005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879005).length < 2 ^ (prefixWord ++ tailWord_3879005).sum := by decide
  have hdescent : baseEnd_3879005 < baseStart_3879005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879068 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 5]
def baseStart_3879068 : Nat := 118140960795 + 3879068 * 2 ^ 59
def prefixEnd_3879068 : Nat := 4983230072969 + 3 ^ 40 * 3879068 * 2
def baseEnd_3879068 : Nat := 221314041719437151367833

theorem tailTrace_3879068 : CollatzResearch.WordTrace tailWord_3879068 prefixEnd_3879068 221314041719437151367833 := by
  unfold tailWord_3879068
  simp only [CollatzResearch.WordTrace]
  refine ⟨70740616555403301457910929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94320822073871068610547905 70740616555403301457910929)
  ·
    refine ⟨53055462416552476093433197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70740616555403301457910929 53055462416552476093433197)
    ·
      refine ⟨19895798406207178535037449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53055462416552476093433197 19895798406207178535037449)
      ·
        refine ⟨14921848804655383901278087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19895798406207178535037449 14921848804655383901278087)
        ·
          refine ⟨22382773206983075851917131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14921848804655383901278087 22382773206983075851917131)
          ·
            refine ⟨33574159810474613777875697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22382773206983075851917131 33574159810474613777875697)
            ·
              refine ⟨25180619857855960333406773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33574159810474613777875697 25180619857855960333406773)
              ·
                refine ⟨2360683111673996281256885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25180619857855960333406773 2360683111673996281256885)
                ·
                  refine ⟨221314041719437151367833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360683111673996281256885 221314041719437151367833)
                  ·
                    rfl

theorem cell23_3879068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_3879068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879068 prefixEnd_3879068 := by exact prefixLift 3879068
  have htrace : WordTrace (prefixWord ++ tailWord_3879068) baseStart_3879068 baseEnd_3879068 := by
    simpa [prefixWord, tailWord_3879068, baseEnd_3879068] using wordTrace_append hprefix tailTrace_3879068
  have hstable : (prefixWord ++ tailWord_3879068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879068).length < 2 ^ (prefixWord ++ tailWord_3879068).sum := by decide
  have hdescent : baseEnd_3879068 < baseStart_3879068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879079 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3879079 : Nat := 118140960795 + 3879079 * 2 ^ 59
def prefixEnd_3879079 : Nat := 4983230072969 + 3 ^ 40 * 3879079 * 2
def baseEnd_3879079 : Nat := 1991832023762133819272947

theorem tailTrace_3879079 : CollatzResearch.WordTrace tailWord_3879079 prefixEnd_3879079 1991832023762133819272947 := by
  unfold tailWord_3879079
  simp only [CollatzResearch.WordTrace]
  refine ⟨141481634313766751794472291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94321089542511167862981527 141481634313766751794472291)
  ·
    refine ⟨212222451470650127691708437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141481634313766751794472291 212222451470650127691708437)
    ·
      refine ⟨9947927412686724735548833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212222451470650127691708437 9947927412686724735548833)
      ·
        refine ⟨7460945559515043551661625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9947927412686724735548833 7460945559515043551661625)
        ·
          refine ⟨5595709169636282663746219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460945559515043551661625 5595709169636282663746219)
          ·
            refine ⟨8393563754454423995619329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595709169636282663746219 8393563754454423995619329)
            ·
              refine ⟨6295172815840817996714497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393563754454423995619329 6295172815840817996714497)
              ·
                refine ⟨4721379611880613497535873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295172815840817996714497 4721379611880613497535873)
                ·
                  refine ⟨3541034708910460123151905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721379611880613497535873 3541034708910460123151905)
                  ·
                    refine ⟨2655776031682845092363929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541034708910460123151905 2655776031682845092363929)
                    ·
                      refine ⟨1991832023762133819272947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655776031682845092363929 1991832023762133819272947)
                      ·
                        rfl

theorem cell23_3879079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3879079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879079 prefixEnd_3879079 := by exact prefixLift 3879079
  have htrace : WordTrace (prefixWord ++ tailWord_3879079) baseStart_3879079 baseEnd_3879079 := by
    simpa [prefixWord, tailWord_3879079, baseEnd_3879079] using wordTrace_append hprefix tailTrace_3879079
  have hstable : (prefixWord ++ tailWord_3879079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879079).length < 2 ^ (prefixWord ++ tailWord_3879079).sum := by decide
  have hdescent : baseEnd_3879079 < baseStart_3879079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879085 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 5]
def baseStart_3879085 : Nat := 118140960795 + 3879085 * 2 ^ 59
def prefixEnd_3879085 : Nat := 4983230072969 + 3 ^ 40 * 3879085 * 2
def baseEnd_3879085 : Nat := 221315011627340088421991

theorem tailTrace_3879085 : CollatzResearch.WordTrace tailWord_3879085 prefixEnd_3879085 221315011627340088421991 := by
  unfold tailWord_3879085
  simp only [CollatzResearch.WordTrace]
  refine ⟨141481853151745014819190709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94321235434496676546127139 141481853151745014819190709)
  ·
    refine ⟨13263923732976095139299129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141481853151745014819190709 13263923732976095139299129)
    ·
      refine ⟨9947942799732071354474347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13263923732976095139299129 9947942799732071354474347)
      ·
        refine ⟨14921914199598107031711521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947942799732071354474347 14921914199598107031711521)
        ·
          refine ⟨11191435649698580273783641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14921914199598107031711521 11191435649698580273783641)
          ·
            refine ⟨8393576737273935205337731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11191435649698580273783641 8393576737273935205337731)
            ·
              refine ⟨12590365105910902808006597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393576737273935205337731 12590365105910902808006597)
              ·
                refine ⟨2360693457358294276501237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12590365105910902808006597 2360693457358294276501237)
                ·
                  refine ⟨221315011627340088421991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360693457358294276501237 221315011627340088421991)
                  ·
                    rfl

theorem cell23_3879085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_3879085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879085 prefixEnd_3879085 := by exact prefixLift 3879085
  have htrace : WordTrace (prefixWord ++ tailWord_3879085) baseStart_3879085 baseEnd_3879085 := by
    simpa [prefixWord, tailWord_3879085, baseEnd_3879085] using wordTrace_append hprefix tailTrace_3879085
  have hstable : (prefixWord ++ tailWord_3879085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879085).length < 2 ^ (prefixWord ++ tailWord_3879085).sum := by decide
  have hdescent : baseEnd_3879085 < baseStart_3879085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879101 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3879101 : Nat := 118140960795 + 3879101 * 2 ^ 59
def prefixEnd_3879101 : Nat := 4983230072969 + 3 ^ 40 * 3879101 * 2
def baseEnd_3879101 : Nat := 1991843320336532733197845

theorem tailTrace_3879101 : CollatzResearch.WordTrace tailWord_3879101 prefixEnd_3879101 1991843320336532733197845 := by
  unfold tailWord_3879101
  simp only [CollatzResearch.WordTrace]
  refine ⟨141482436719687049551773157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94321624479791366367848771 141482436719687049551773157)
  ·
    refine ⟨26527956884941321790957467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141482436719687049551773157 26527956884941321790957467)
    ·
      refine ⟨39791935327411982686436201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26527956884941321790957467 39791935327411982686436201)
      ·
        refine ⟨29843951495558987014827151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39791935327411982686436201 29843951495558987014827151)
        ·
          refine ⟨44765927243338480522240727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843951495558987014827151 44765927243338480522240727)
          ·
            refine ⟨67148890865007720783361091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44765927243338480522240727 67148890865007720783361091)
            ·
              refine ⟨100723336297511581175041637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67148890865007720783361091 100723336297511581175041637)
              ·
                refine ⟨18885625555783421470320307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100723336297511581175041637 18885625555783421470320307)
                ·
                  refine ⟨28328438333675132205480461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18885625555783421470320307 28328438333675132205480461)
                  ·
                    refine ⟨10623164375128174577055173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28328438333675132205480461 10623164375128174577055173)
                    ·
                      refine ⟨1991843320336532733197845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10623164375128174577055173 1991843320336532733197845)
                      ·
                        rfl

theorem cell23_3879101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3879101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879101 prefixEnd_3879101 := by exact prefixLift 3879101
  have htrace : WordTrace (prefixWord ++ tailWord_3879101) baseStart_3879101 baseEnd_3879101 := by
    simpa [prefixWord, tailWord_3879101, baseEnd_3879101] using wordTrace_append hprefix tailTrace_3879101
  have hstable : (prefixWord ++ tailWord_3879101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879101).length < 2 ^ (prefixWord ++ tailWord_3879101).sum := by decide
  have hdescent : baseEnd_3879101 < baseStart_3879101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879118 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3879118 : Nat := 118140960795 + 3879118 * 2 ^ 59
def prefixEnd_3879118 : Nat := 4983230072969 + 3 ^ 40 * 3879118 * 2
def baseEnd_3879118 : Nat := 1991852049507659166685267

theorem tailTrace_3879118 : CollatzResearch.WordTrace tailWord_3879118 prefixEnd_3879118 1991852049507659166685267 := by
  unfold tailWord_3879118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685382095078182681892751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94322037840416974303428005 17685382095078182681892751)
  ·
    refine ⟨26528073142617274022839127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17685382095078182681892751 26528073142617274022839127)
    ·
      refine ⟨39792109713925911034258691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26528073142617274022839127 39792109713925911034258691)
      ·
        refine ⟨59688164570888866551388037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39792109713925911034258691 59688164570888866551388037)
        ·
          refine ⟨11191530857041662478385257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59688164570888866551388037 11191530857041662478385257)
          ·
            refine ⟨8393648142781246858788943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11191530857041662478385257 8393648142781246858788943)
            ·
              refine ⟨12590472214171870288183415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393648142781246858788943 12590472214171870288183415)
              ·
                refine ⟨18885708321257805432275123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12590472214171870288183415 18885708321257805432275123)
                ·
                  refine ⟨28328562481886708148412685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18885708321257805432275123 28328562481886708148412685)
                  ·
                    refine ⟨10623210930707515555654757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28328562481886708148412685 10623210930707515555654757)
                    ·
                      refine ⟨1991852049507659166685267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10623210930707515555654757 1991852049507659166685267)
                      ·
                        rfl

theorem cell23_3879118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3879118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879118 prefixEnd_3879118 := by exact prefixLift 3879118
  have htrace : WordTrace (prefixWord ++ tailWord_3879118) baseStart_3879118 baseEnd_3879118 := by
    simpa [prefixWord, tailWord_3879118, baseEnd_3879118] using wordTrace_append hprefix tailTrace_3879118
  have hstable : (prefixWord ++ tailWord_3879118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879118).length < 2 ^ (prefixWord ++ tailWord_3879118).sum := by decide
  have hdescent : baseEnd_3879118 < baseStart_3879118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879158 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_3879158 : Nat := 118140960795 + 3879158 * 2 ^ 59
def prefixEnd_3879158 : Nat := 4983230072969 + 3 ^ 40 * 3879158 * 2
def baseEnd_3879158 : Nat := 221319176525982112242787

theorem tailTrace_3879158 : CollatzResearch.WordTrace tailWord_3879158 prefixEnd_3879158 221319176525982112242787 := by
  unfold tailWord_3879158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842782230030034267912383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94323010453653698857732085 8842782230030034267912383)
  ·
    refine ⟨13264173345045051401868575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8842782230030034267912383 13264173345045051401868575)
    ·
      refine ⟨19896260017567577102802863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264173345045051401868575 19896260017567577102802863)
      ·
        refine ⟨29844390026351365654204295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896260017567577102802863 29844390026351365654204295)
        ·
          refine ⟨44766585039527048481306443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29844390026351365654204295 44766585039527048481306443)
          ·
            refine ⟨67149877559290572721959665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44766585039527048481306443 67149877559290572721959665)
            ·
              refine ⟨50362408169467929541469749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67149877559290572721959665 50362408169467929541469749)
              ·
                refine ⟨4721475765887618394512789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50362408169467929541469749 4721475765887618394512789)
                ·
                  refine ⟨221319176525982112242787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4721475765887618394512789 221319176525982112242787)
                  ·
                    rfl

theorem cell23_3879158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_3879158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879158 prefixEnd_3879158 := by exact prefixLift 3879158
  have htrace : WordTrace (prefixWord ++ tailWord_3879158) baseStart_3879158 baseEnd_3879158 := by
    simpa [prefixWord, tailWord_3879158, baseEnd_3879158] using wordTrace_append hprefix tailTrace_3879158
  have hstable : (prefixWord ++ tailWord_3879158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879158).length < 2 ^ (prefixWord ++ tailWord_3879158).sum := by decide
  have hdescent : baseEnd_3879158 < baseStart_3879158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879202 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3879202 : Nat := 118140960795 + 3879202 * 2 ^ 59
def prefixEnd_3879202 : Nat := 4983230072969 + 3 ^ 40 * 3879202 * 2
def baseEnd_3879202 : Nat := 1991895181882636838034881

theorem tailTrace_3879202 : CollatzResearch.WordTrace tailWord_3879202 prefixEnd_3879202 1991895181882636838034881 := by
  unfold tailWord_3879202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35371530123080285950299965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94324080328214095867466573 35371530123080285950299965)
  ·
    refine ⟨13264323796155107231362487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35371530123080285950299965 13264323796155107231362487)
    ·
      refine ⟨19896485694232660847043731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264323796155107231362487 19896485694232660847043731)
      ·
        refine ⟨29844728541348991270565597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896485694232660847043731 29844728541348991270565597)
        ·
          refine ⟨11191773203005871726462099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29844728541348991270565597 11191773203005871726462099)
          ·
            refine ⟨16787659804508807589693149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191773203005871726462099 16787659804508807589693149)
            ·
              refine ⟨6295372426690802846134931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16787659804508807589693149 6295372426690802846134931)
              ·
                refine ⟨9443058640036204269202397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295372426690802846134931 9443058640036204269202397)
                ·
                  refine ⟨3541146990013576600950899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9443058640036204269202397 3541146990013576600950899)
                  ·
                    refine ⟨5311720485020364901426349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541146990013576600950899 5311720485020364901426349)
                    ·
                      refine ⟨1991895181882636838034881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311720485020364901426349 1991895181882636838034881)
                      ·
                        rfl

theorem cell23_3879202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3879202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879202 prefixEnd_3879202 := by exact prefixLift 3879202
  have htrace : WordTrace (prefixWord ++ tailWord_3879202) baseStart_3879202 baseEnd_3879202 := by
    simpa [prefixWord, tailWord_3879202, baseEnd_3879202] using wordTrace_append hprefix tailTrace_3879202
  have hstable : (prefixWord ++ tailWord_3879202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879202).length < 2 ^ (prefixWord ++ tailWord_3879202).sum := by decide
  have hdescent : baseEnd_3879202 < baseStart_3879202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879225 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3879225 : Nat := 118140960795 + 3879225 * 2 ^ 59
def prefixEnd_3879225 : Nat := 4983230072969 + 3 ^ 40 * 3879225 * 2
def baseEnd_3879225 : Nat := 1991906991937690248047275

theorem tailTrace_3879225 : CollatzResearch.WordTrace tailWord_3879225 prefixEnd_3879225 1991906991937690248047275 := by
  unfold tailWord_3879225
  simp only [CollatzResearch.WordTrace]
  refine ⟨141486959371237818729287129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94324639580825212486191419 141486959371237818729287129)
  ·
    refine ⟨106115219528428364046965347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141486959371237818729287129 106115219528428364046965347)
    ·
      refine ⟨159172829292642546070448021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106115219528428364046965347 159172829292642546070448021)
      ·
        refine ⟨7461226373092619347052251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159172829292642546070448021 7461226373092619347052251)
        ·
          refine ⟨11191839559638929020578377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461226373092619347052251 11191839559638929020578377)
          ·
            refine ⟨8393879669729196765433783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11191839559638929020578377 8393879669729196765433783)
            ·
              refine ⟨12590819504593795148150675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393879669729196765433783 12590819504593795148150675)
              ·
                refine ⟨18886229256890692722226013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12590819504593795148150675 18886229256890692722226013)
                ·
                  refine ⟨7082335971334009770834755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18886229256890692722226013 7082335971334009770834755)
                  ·
                    refine ⟨10623503957001014656252133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082335971334009770834755 10623503957001014656252133)
                    ·
                      refine ⟨1991906991937690248047275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10623503957001014656252133 1991906991937690248047275)
                      ·
                        rfl

theorem cell23_3879225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3879225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879225 prefixEnd_3879225 := by exact prefixLift 3879225
  have htrace : WordTrace (prefixWord ++ tailWord_3879225) baseStart_3879225 baseEnd_3879225 := by
    simpa [prefixWord, tailWord_3879225, baseEnd_3879225] using wordTrace_append hprefix tailTrace_3879225
  have hstable : (prefixWord ++ tailWord_3879225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879225).length < 2 ^ (prefixWord ++ tailWord_3879225).sum := by decide
  have hdescent : baseEnd_3879225 < baseStart_3879225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879231 : List Nat := [1, 1, 2, 2, 4, 1, 1, 11]
def baseStart_3879231 : Nat := 118140960795 + 3879231 * 2 ^ 59
def prefixEnd_3879231 : Nat := 4983230072969 + 3 ^ 40 * 3879231 * 2
def baseEnd_3879231 : Nat := 73774447141541378687861

theorem tailTrace_3879231 : CollatzResearch.WordTrace tailWord_3879231 prefixEnd_3879231 73774447141541378687861 := by
  unfold tailWord_3879231
  simp only [CollatzResearch.WordTrace]
  refine ⟨141487178209216081754005547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94324785472810721169337031 141487178209216081754005547)
  ·
    refine ⟨212230767313824122631008321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141487178209216081754005547 212230767313824122631008321)
    ·
      refine ⟨159173075485368091973256241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212230767313824122631008321 159173075485368091973256241)
      ·
        refine ⟨119379806614026068979942181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159173075485368091973256241 119379806614026068979942181)
        ·
          refine ⟨22383713740129887933739159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119379806614026068979942181 22383713740129887933739159)
          ·
            refine ⟨33575570610194831900608739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22383713740129887933739159 33575570610194831900608739)
            ·
              refine ⟨50363355915292247850913109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33575570610194831900608739 50363355915292247850913109)
              ·
                refine ⟨73774447141541378687861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50363355915292247850913109 73774447141541378687861)
                ·
                  rfl

theorem cell23_3879231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 11].length) (baseStart_3879231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879231 prefixEnd_3879231 := by exact prefixLift 3879231
  have htrace : WordTrace (prefixWord ++ tailWord_3879231) baseStart_3879231 baseEnd_3879231 := by
    simpa [prefixWord, tailWord_3879231, baseEnd_3879231] using wordTrace_append hprefix tailTrace_3879231
  have hstable : (prefixWord ++ tailWord_3879231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879231).length < 2 ^ (prefixWord ++ tailWord_3879231).sum := by decide
  have hdescent : baseEnd_3879231 < baseStart_3879231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879251 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_3879251 : Nat := 118140960795 + 3879251 * 2 ^ 59
def prefixEnd_3879251 : Nat := 4983230072969 + 3 ^ 40 * 3879251 * 2
def baseEnd_3879251 : Nat := 1991920342434707146322155

theorem tailTrace_3879251 : CollatzResearch.WordTrace tailWord_3879251 prefixEnd_3879251 1991920342434707146322155 := by
  unfold tailWord_3879251
  simp only [CollatzResearch.WordTrace]
  refine ⟨141487907669143625169733607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94325271779429083446489071 141487907669143625169733607)
  ·
    refine ⟨212231861503715437754600411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141487907669143625169733607 212231861503715437754600411)
    ·
      refine ⟨318347792255573156631900617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212231861503715437754600411 318347792255573156631900617)
      ·
        refine ⟨238760844191679867473925463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318347792255573156631900617 238760844191679867473925463)
        ·
          refine ⟨358141266287519801210888195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238760844191679867473925463 358141266287519801210888195)
          ·
            refine ⟨537211899431279701816332293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358141266287519801210888195 537211899431279701816332293)
            ·
              refine ⟨100727231143364944090562305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 537211899431279701816332293 100727231143364944090562305)
              ·
                refine ⟨75545423357523708067921729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100727231143364944090562305 75545423357523708067921729)
                ·
                  refine ⟨56659067518142781050941297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75545423357523708067921729 56659067518142781050941297)
                  ·
                    refine ⟨42494300638607085788205973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56659067518142781050941297 42494300638607085788205973)
                    ·
                      refine ⟨1991920342434707146322155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42494300638607085788205973 1991920342434707146322155)
                      ·
                        rfl

theorem cell23_3879251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_3879251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879251 prefixEnd_3879251 := by exact prefixLift 3879251
  have htrace : WordTrace (prefixWord ++ tailWord_3879251) baseStart_3879251 baseEnd_3879251 := by
    simpa [prefixWord, tailWord_3879251, baseEnd_3879251] using wordTrace_append hprefix tailTrace_3879251
  have hstable : (prefixWord ++ tailWord_3879251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879251).length < 2 ^ (prefixWord ++ tailWord_3879251).sum := by decide
  have hdescent : baseEnd_3879251 < baseStart_3879251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879252 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3879252 : Nat := 118140960795 + 3879252 * 2 ^ 59
def prefixEnd_3879252 : Nat := 4983230072969 + 3 ^ 40 * 3879252 * 2
def baseEnd_3879252 : Nat := 663973618638453880803217

theorem tailTrace_3879252 : CollatzResearch.WordTrace tailWord_3879252 prefixEnd_3879252 663973618638453880803217 := by
  unfold tailWord_3879252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70743972071070001170260005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94325296094760001560346673 70743972071070001170260005)
  ·
    refine ⟨13264494763325625219423751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70743972071070001170260005 13264494763325625219423751)
    ·
      refine ⟨19896742144988437829135627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264494763325625219423751 19896742144988437829135627)
      ·
        refine ⟨29845113217482656743703441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896742144988437829135627 29845113217482656743703441)
        ·
          refine ⟨22383834913111992557777581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29845113217482656743703441 22383834913111992557777581)
          ·
            refine ⟨8393938092416997209166593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22383834913111992557777581 8393938092416997209166593)
            ·
              refine ⟨6295453569312747906874945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393938092416997209166593 6295453569312747906874945)
              ·
                refine ⟨4721590176984560930156209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295453569312747906874945 4721590176984560930156209)
                ·
                  refine ⟨3541192632738420697617157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721590176984560930156209 3541192632738420697617157)
                  ·
                    refine ⟨663973618638453880803217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541192632738420697617157 663973618638453880803217)
                    ·
                      rfl

theorem cell23_3879252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3879252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879252 prefixEnd_3879252 := by exact prefixLift 3879252
  have htrace : WordTrace (prefixWord ++ tailWord_3879252) baseStart_3879252 baseEnd_3879252 := by
    simpa [prefixWord, tailWord_3879252, baseEnd_3879252] using wordTrace_append hprefix tailTrace_3879252
  have hstable : (prefixWord ++ tailWord_3879252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879252).length < 2 ^ (prefixWord ++ tailWord_3879252).sum := by decide
  have hdescent : baseEnd_3879252 < baseStart_3879252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879253 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3879253 : Nat := 118140960795 + 3879253 * 2 ^ 59
def prefixEnd_3879253 : Nat := 4983230072969 + 3 ^ 40 * 3879253 * 2
def baseEnd_3879253 : Nat := 1991921369396016138497147

theorem tailTrace_3879253 : CollatzResearch.WordTrace tailWord_3879253 prefixEnd_3879253 1991921369396016138497147 := by
  unfold tailWord_3879253
  simp only [CollatzResearch.WordTrace]
  refine ⟨141487980615136379511306413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94325320410090919674204275 141487980615136379511306413)
  ·
    refine ⟨53057992730676142316739905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141487980615136379511306413 53057992730676142316739905)
    ·
      refine ⟨39793494548007106737554929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53057992730676142316739905 39793494548007106737554929)
      ·
        refine ⟨29845120911005330053166197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39793494548007106737554929 29845120911005330053166197)
        ·
          refine ⟨2797980085406749692484331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29845120911005330053166197 2797980085406749692484331)
          ·
            refine ⟨4196970128110124538726497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797980085406749692484331 4196970128110124538726497)
            ·
              refine ⟨3147727596082593404044873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196970128110124538726497 3147727596082593404044873)
              ·
                refine ⟨2360795697061945053033655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147727596082593404044873 2360795697061945053033655)
                ·
                  refine ⟨3541193545592917579550483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360795697061945053033655 3541193545592917579550483)
                  ·
                    refine ⟨5311790318389376369325725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541193545592917579550483 5311790318389376369325725)
                    ·
                      refine ⟨1991921369396016138497147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311790318389376369325725 1991921369396016138497147)
                      ·
                        rfl

theorem cell23_3879253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3879253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879253 prefixEnd_3879253 := by exact prefixLift 3879253
  have htrace : WordTrace (prefixWord ++ tailWord_3879253) baseStart_3879253 baseEnd_3879253 := by
    simpa [prefixWord, tailWord_3879253, baseEnd_3879253] using wordTrace_append hprefix tailTrace_3879253
  have hstable : (prefixWord ++ tailWord_3879253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879253).length < 2 ^ (prefixWord ++ tailWord_3879253).sum := by decide
  have hdescent : baseEnd_3879253 < baseStart_3879253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879258 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_3879258 : Nat := 118140960795 + 3879258 * 2 ^ 59
def prefixEnd_3879258 : Nat := 4983230072969 + 3 ^ 40 * 3879258 * 2
def baseEnd_3879258 : Nat := 1991923936799288618934623

theorem tailTrace_3879258 : CollatzResearch.WordTrace tailWord_3879258 prefixEnd_3879258 1991923936799288618934623 := by
  unfold tailWord_3879258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35372040745029566341309607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94325441986745510243492285 35372040745029566341309607)
  ·
    refine ⟨53058061117544349511964411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35372040745029566341309607 53058061117544349511964411)
    ·
      refine ⟨79587091676316524267946617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53058061117544349511964411 79587091676316524267946617)
      ·
        refine ⟨59690318757237393200959963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79587091676316524267946617 59690318757237393200959963)
        ·
          refine ⟨89535478135856089801439945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59690318757237393200959963 89535478135856089801439945)
          ·
            refine ⟨67151608601892067351079959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89535478135856089801439945 67151608601892067351079959)
            ·
              refine ⟨100727412902838101026619939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67151608601892067351079959 100727412902838101026619939)
              ·
                refine ⟨151091119354257151539929909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100727412902838101026619939 151091119354257151539929909)
                ·
                  refine ⟨14164792439461607956868429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151091119354257151539929909 14164792439461607956868429)
                  ·
                    refine ⟨5311797164798102983825661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14164792439461607956868429 5311797164798102983825661)
                    ·
                      refine ⟨1991923936799288618934623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311797164798102983825661 1991923936799288618934623)
                      ·
                        rfl

theorem cell23_3879258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_3879258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879258 prefixEnd_3879258 := by exact prefixLift 3879258
  have htrace : WordTrace (prefixWord ++ tailWord_3879258) baseStart_3879258 baseEnd_3879258 := by
    simpa [prefixWord, tailWord_3879258, baseEnd_3879258] using wordTrace_append hprefix tailTrace_3879258
  have hstable : (prefixWord ++ tailWord_3879258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879258).length < 2 ^ (prefixWord ++ tailWord_3879258).sum := by decide
  have hdescent : baseEnd_3879258 < baseStart_3879258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879308 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_3879308 : Nat := 118140960795 + 3879308 * 2 ^ 59
def prefixEnd_3879308 : Nat := 4983230072969 + 3 ^ 40 * 3879308 * 2
def baseEnd_3879308 : Nat := 663983203610671141103131

theorem tailTrace_3879308 : CollatzResearch.WordTrace tailWord_3879308 prefixEnd_3879308 663983203610671141103131 := by
  unfold tailWord_3879308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70744993314968561952279289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94326657753291415936372385 70744993314968561952279289)
  ·
    refine ⟨53058744986226421464209467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70744993314968561952279289 53058744986226421464209467)
    ·
      refine ⟨79588117479339632196314201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53058744986226421464209467 79588117479339632196314201)
      ·
        refine ⟨59691088109504724147235651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79588117479339632196314201 59691088109504724147235651)
        ·
          refine ⟨89536632164257086220853477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59691088109504724147235651 89536632164257086220853477)
          ·
            refine ⟨16788118530798203666410027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89536632164257086220853477 16788118530798203666410027)
            ·
              refine ⟨25182177796197305499615041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16788118530798203666410027 25182177796197305499615041)
              ·
                refine ⟨18886633347147979124711281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25182177796197305499615041 18886633347147979124711281)
                ·
                  refine ⟨14164975010360984343533461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18886633347147979124711281 14164975010360984343533461)
                  ·
                    refine ⟨663983203610671141103131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14164975010360984343533461 663983203610671141103131)
                    ·
                      rfl

theorem cell23_3879308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_3879308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879308 prefixEnd_3879308 := by exact prefixLift 3879308
  have htrace : WordTrace (prefixWord ++ tailWord_3879308) baseStart_3879308 baseEnd_3879308 := by
    simpa [prefixWord, tailWord_3879308, baseEnd_3879308] using wordTrace_append hprefix tailTrace_3879308
  have hstable : (prefixWord ++ tailWord_3879308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879308).length < 2 ^ (prefixWord ++ tailWord_3879308).sum := by decide
  have hdescent : baseEnd_3879308 < baseStart_3879308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879332 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_3879332 : Nat := 118140960795 + 3879332 * 2 ^ 59
def prefixEnd_3879332 : Nat := 4983230072969 + 3 ^ 40 * 3879332 * 2
def baseEnd_3879332 : Nat := 1991961934367721329409283

theorem tailTrace_3879332 : CollatzResearch.WordTrace tailWord_3879332 prefixEnd_3879332 1991961934367721329409283 := by
  unfold tailWord_3879332
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745430990925088001716125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94327241321233450668954833 70745430990925088001716125)
  ·
    refine ⟨26529536621596908000643547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70745430990925088001716125 26529536621596908000643547)
    ·
      refine ⟨39794304932395362000965321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529536621596908000643547 39794304932395362000965321)
      ·
        refine ⟨29845728699296521500723991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39794304932395362000965321 29845728699296521500723991)
        ·
          refine ⟨44768593048944782251085987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29845728699296521500723991 44768593048944782251085987)
          ·
            refine ⟨67152889573417173376628981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44768593048944782251085987 67152889573417173376628981)
            ·
              refine ⟨6295583397507860004058967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67152889573417173376628981 6295583397507860004058967)
              ·
                refine ⟨9443375096261790006088451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295583397507860004058967 9443375096261790006088451)
                ·
                  refine ⟨14165062644392685009132677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443375096261790006088451 14165062644392685009132677)
                  ·
                    refine ⟨2655949245823628439212377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14165062644392685009132677 2655949245823628439212377)
                    ·
                      refine ⟨1991961934367721329409283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655949245823628439212377 1991961934367721329409283)
                      ·
                        rfl

theorem cell23_3879332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_3879332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879332 prefixEnd_3879332 := by exact prefixLift 3879332
  have htrace : WordTrace (prefixWord ++ tailWord_3879332) baseStart_3879332 baseEnd_3879332 := by
    simpa [prefixWord, tailWord_3879332, baseEnd_3879332] using wordTrace_append hprefix tailTrace_3879332
  have hstable : (prefixWord ++ tailWord_3879332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879332).length < 2 ^ (prefixWord ++ tailWord_3879332).sum := by decide
  have hdescent : baseEnd_3879332 < baseStart_3879332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879336 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3879336 : Nat := 118140960795 + 3879336 * 2 ^ 59
def prefixEnd_3879336 : Nat := 4983230072969 + 3 ^ 40 * 3879336 * 2
def baseEnd_3879336 : Nat := 1991963988290339313759265

theorem tailTrace_3879336 : CollatzResearch.WordTrace tailWord_3879336 prefixEnd_3879336 1991963988290339313759265 := by
  unfold tailWord_3879336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745503936917842343288931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94327338582557123124385241 70745503936917842343288931)
  ·
    refine ⟨106118255905376763514933397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70745503936917842343288931 106118255905376763514933397)
    ·
      refine ⟨4974293245564535789762503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106118255905376763514933397 4974293245564535789762503)
      ·
        refine ⟨7461439868346803684643755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974293245564535789762503 7461439868346803684643755)
        ·
          refine ⟨11192159802520205526965633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461439868346803684643755 11192159802520205526965633)
          ·
            refine ⟨8394119851890154145224225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192159802520205526965633 8394119851890154145224225)
            ·
              refine ⟨6295589888917615608918169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8394119851890154145224225 6295589888917615608918169)
              ·
                refine ⟨4721692416688211706688627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295589888917615608918169 4721692416688211706688627)
                ·
                  refine ⟨7082538625032317560032941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721692416688211706688627 7082538625032317560032941)
                  ·
                    refine ⟨2655951984387119085012353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7082538625032317560032941 2655951984387119085012353)
                    ·
                      refine ⟨1991963988290339313759265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655951984387119085012353 1991963988290339313759265)
                      ·
                        rfl

theorem cell23_3879336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3879336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879336 prefixEnd_3879336 := by exact prefixLift 3879336
  have htrace : WordTrace (prefixWord ++ tailWord_3879336) baseStart_3879336 baseEnd_3879336 := by
    simpa [prefixWord, tailWord_3879336, baseEnd_3879336] using wordTrace_append hprefix tailTrace_3879336
  have hstable : (prefixWord ++ tailWord_3879336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879336).length < 2 ^ (prefixWord ++ tailWord_3879336).sum := by decide
  have hdescent : baseEnd_3879336 < baseStart_3879336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879372 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 7]
def baseStart_3879372 : Nat := 118140960795 + 3879372 * 2 ^ 59
def prefixEnd_3879372 : Nat := 4983230072969 + 3 ^ 40 * 3879372 * 2
def baseEnd_3879372 : Nat := 221331385954877908101011

theorem tailTrace_3879372 : CollatzResearch.WordTrace tailWord_3879372 prefixEnd_3879372 221331385954877908101011 := by
  unfold tailWord_3879372
  simp only [CollatzResearch.WordTrace]
  refine ⟨70746160450852631417444185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94328213934470175223258913 70746160450852631417444185)
  ·
    refine ⟨53059620338139473563083139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70746160450852631417444185 53059620338139473563083139)
    ·
      refine ⟨79589430507209210344624709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53059620338139473563083139 79589430507209210344624709)
      ·
        refine ⟨14923018220101726939617133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79589430507209210344624709 14923018220101726939617133)
        ·
          refine ⟨5596131832538147602356425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14923018220101726939617133 5596131832538147602356425)
          ·
            refine ⟨4197098874403610701767319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5596131832538147602356425 4197098874403610701767319)
            ·
              refine ⟨6295648311605416052650979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197098874403610701767319 6295648311605416052650979)
              ·
                refine ⟨9443472467408124078976469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295648311605416052650979 9443472467408124078976469)
                ·
                  refine ⟨221331385954877908101011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9443472467408124078976469 221331385954877908101011)
                  ·
                    rfl

theorem cell23_3879372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_3879372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879372 prefixEnd_3879372 := by exact prefixLift 3879372
  have htrace : WordTrace (prefixWord ++ tailWord_3879372) baseStart_3879372 baseEnd_3879372 := by
    simpa [prefixWord, tailWord_3879372, baseEnd_3879372] using wordTrace_append hprefix tailTrace_3879372
  have hstable : (prefixWord ++ tailWord_3879372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879372).length < 2 ^ (prefixWord ++ tailWord_3879372).sum := by decide
  have hdescent : baseEnd_3879372 < baseStart_3879372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879375 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 5, 2]
def baseStart_3879375 : Nat := 118140960795 + 3879375 * 2 ^ 59
def prefixEnd_3879375 : Nat := 4983230072969 + 3 ^ 40 * 3879375 * 2
def baseEnd_3879375 : Nat := 1991984014035864661171585

theorem tailTrace_3879375 : CollatzResearch.WordTrace tailWord_3879375 prefixEnd_3879375 1991984014035864661171585 := by
  unfold tailWord_3879375
  simp only [CollatzResearch.WordTrace]
  refine ⟨141492430320694394347247579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94328286880462929564831719 141492430320694394347247579)
  ·
    refine ⟨212238645481041591520871369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141492430320694394347247579 212238645481041591520871369)
    ·
      refine ⟨159178984110781193640653527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212238645481041591520871369 159178984110781193640653527)
      ·
        refine ⟨238768476166171790460980291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159178984110781193640653527 238768476166171790460980291)
        ·
          refine ⟨358152714249257685691470437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238768476166171790460980291 358152714249257685691470437)
          ·
            refine ⟨67153633921735816067150707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358152714249257685691470437 67153633921735816067150707)
            ·
              refine ⟨100730450882603724100726061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67153633921735816067150707 100730450882603724100726061)
              ·
                refine ⟨37773919080976396537772273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100730450882603724100726061 37773919080976396537772273)
                ·
                  refine ⟨28330439310732297403329205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37773919080976396537772273 28330439310732297403329205)
                  ·
                    refine ⟨2655978685381152881562113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28330439310732297403329205 2655978685381152881562113)
                    ·
                      refine ⟨1991984014035864661171585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655978685381152881562113 1991984014035864661171585)
                      ·
                        rfl

theorem cell23_3879375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5, 2].length) (baseStart_3879375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879375 prefixEnd_3879375 := by exact prefixLift 3879375
  have htrace : WordTrace (prefixWord ++ tailWord_3879375) baseStart_3879375 baseEnd_3879375 := by
    simpa [prefixWord, tailWord_3879375, baseEnd_3879375] using wordTrace_append hprefix tailTrace_3879375
  have hstable : (prefixWord ++ tailWord_3879375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879375).length < 2 ^ (prefixWord ++ tailWord_3879375).sum := by decide
  have hdescent : baseEnd_3879375 < baseStart_3879375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879382 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3879382 : Nat := 118140960795 + 3879382 * 2 ^ 59
def prefixEnd_3879382 : Nat := 4983230072969 + 3 ^ 40 * 3879382 * 2
def baseEnd_3879382 : Nat := 1991987608400446133784053

theorem tailTrace_3879382 : CollatzResearch.WordTrace tailWord_3879382 prefixEnd_3879382 1991987608400446133784053 := by
  unfold tailWord_3879382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843292851979314658922025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94328457087779356361834933 8843292851979314658922025)
  ·
    refine ⟨6632469638984485994191519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8843292851979314658922025 6632469638984485994191519)
    ·
      refine ⟨9948704458476728991287279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632469638984485994191519 9948704458476728991287279)
      ·
        refine ⟨14923056687715093486930919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948704458476728991287279 14923056687715093486930919)
        ·
          refine ⟨22384585031572640230396379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923056687715093486930919 22384585031572640230396379)
          ·
            refine ⟨33576877547358960345594569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22384585031572640230396379 33576877547358960345594569)
            ·
              refine ⟨25182658160519220259195927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33576877547358960345594569 25182658160519220259195927)
              ·
                refine ⟨37773987240778830388793891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25182658160519220259195927 37773987240778830388793891)
                ·
                  refine ⟨56660980861168245583190837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37773987240778830388793891 56660980861168245583190837)
                  ·
                    refine ⟨5311966955734523023424141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56660980861168245583190837 5311966955734523023424141)
                    ·
                      refine ⟨1991987608400446133784053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5311966955734523023424141 1991987608400446133784053)
                      ·
                        rfl

theorem cell23_3879382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3879382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879382 prefixEnd_3879382 := by exact prefixLift 3879382
  have htrace : WordTrace (prefixWord ++ tailWord_3879382) baseStart_3879382 baseEnd_3879382 := by
    simpa [prefixWord, tailWord_3879382, baseEnd_3879382] using wordTrace_append hprefix tailTrace_3879382
  have hstable : (prefixWord ++ tailWord_3879382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879382).length < 2 ^ (prefixWord ++ tailWord_3879382).sum := by decide
  have hdescent : baseEnd_3879382 < baseStart_3879382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879402 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3879402 : Nat := 118140960795 + 3879402 * 2 ^ 59
def prefixEnd_3879402 : Nat := 4983230072969 + 3 ^ 40 * 3879402 * 2
def baseEnd_3879402 : Nat := 663999292671178685177987

theorem tailTrace_3879402 : CollatzResearch.WordTrace tailWord_3879402 prefixEnd_3879402 663999292671178685177987 := by
  unfold tailWord_3879402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373353772899144489620115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94328943394397718638986973 35373353772899144489620115)
  ·
    refine ⟨53060030659348716734430173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35373353772899144489620115 53060030659348716734430173)
    ·
      refine ⟨19897511497255768775411315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53060030659348716734430173 19897511497255768775411315)
      ·
        refine ⟨29846267245883653163116973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19897511497255768775411315 29846267245883653163116973)
        ·
          refine ⟨11192350217206369936168865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29846267245883653163116973 11192350217206369936168865)
          ·
            refine ⟨8394262662904777452126649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192350217206369936168865 8394262662904777452126649)
            ·
              refine ⟨6295696997178583089094987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8394262662904777452126649 6295696997178583089094987)
              ·
                refine ⟨9443545495767874633642481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295696997178583089094987 9443545495767874633642481)
                ·
                  refine ⟨7082659121825905975231861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443545495767874633642481 7082659121825905975231861)
                  ·
                    refine ⟨663999292671178685177987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7082659121825905975231861 663999292671178685177987)
                    ·
                      rfl

theorem cell23_3879402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3879402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879402 prefixEnd_3879402 := by exact prefixLift 3879402
  have htrace : WordTrace (prefixWord ++ tailWord_3879402) baseStart_3879402 baseEnd_3879402 := by
    simpa [prefixWord, tailWord_3879402, baseEnd_3879402] using wordTrace_append hprefix tailTrace_3879402
  have hstable : (prefixWord ++ tailWord_3879402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879402).length < 2 ^ (prefixWord ++ tailWord_3879402).sum := by decide
  have hdescent : baseEnd_3879402 < baseStart_3879402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879445 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 6]
def baseStart_3879445 : Nat := 118140960795 + 3879445 * 2 ^ 59
def prefixEnd_3879445 : Nat := 4983230072969 + 3 ^ 40 * 3879445 * 2
def baseEnd_3879445 : Nat := 221335550853519931921807

theorem tailTrace_3879445 : CollatzResearch.WordTrace tailWord_3879445 prefixEnd_3879445 221335550853519931921807 := by
  unfold tailWord_3879445
  simp only [CollatzResearch.WordTrace]
  refine ⟨141494983430440796302295789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94329988953627197534863859 141494983430440796302295789)
  ·
    refine ⟨53060618786415298613360921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141494983430440796302295789 53060618786415298613360921)
    ·
      refine ⟨39795464089811473960020691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53060618786415298613360921 39795464089811473960020691)
      ·
        refine ⟨59693196134717210940031037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39795464089811473960020691 59693196134717210940031037)
        ·
          refine ⟨22384948550518954102511639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59693196134717210940031037 22384948550518954102511639)
          ·
            refine ⟨33577422825778431153767459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22384948550518954102511639 33577422825778431153767459)
            ·
              refine ⟨50366134238667646730651189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33577422825778431153767459 50366134238667646730651189)
              ·
                refine ⟨4721825084875091880998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50366134238667646730651189 4721825084875091880998549)
                ·
                  refine ⟨221335550853519931921807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4721825084875091880998549 221335550853519931921807)
                  ·
                    rfl

theorem cell23_3879445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_3879445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879445 prefixEnd_3879445 := by exact prefixLift 3879445
  have htrace : WordTrace (prefixWord ++ tailWord_3879445) baseStart_3879445 baseEnd_3879445 := by
    simpa [prefixWord, tailWord_3879445, baseEnd_3879445] using wordTrace_append hprefix tailTrace_3879445
  have hstable : (prefixWord ++ tailWord_3879445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879445).length < 2 ^ (prefixWord ++ tailWord_3879445).sum := by decide
  have hdescent : baseEnd_3879445 < baseStart_3879445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879456 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3879456 : Nat := 118140960795 + 3879456 * 2 ^ 59
def prefixEnd_3879456 : Nat := 4983230072969 + 3 ^ 40 * 3879456 * 2
def baseEnd_3879456 : Nat := 1992025605968878844258713

theorem tailTrace_3879456 : CollatzResearch.WordTrace tailWord_3879456 prefixEnd_3879456 1992025605968878844258713 := by
  unfold tailWord_3879456
  simp only [CollatzResearch.WordTrace]
  refine ⟨70747692316700472590473111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94330256422267296787297481 70747692316700472590473111)
  ·
    refine ⟨106121538475050708885709667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70747692316700472590473111 106121538475050708885709667)
    ·
      refine ⟨159182307712576063328564501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106121538475050708885709667 159182307712576063328564501)
      ·
        refine ⟨7461670674027002968526461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159182307712576063328564501 7461670674027002968526461)
        ·
          refine ⟨2798126502760126113197423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7461670674027002968526461 2798126502760126113197423)
          ·
            refine ⟨4197189754140189169796135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798126502760126113197423 4197189754140189169796135)
            ·
              refine ⟨6295784631210283754694203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197189754140189169796135 6295784631210283754694203)
              ·
                refine ⟨9443676946815425632041305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295784631210283754694203 9443676946815425632041305)
                ·
                  refine ⟨7082757710111569224030979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443676946815425632041305 7082757710111569224030979)
                  ·
                    refine ⟨10624136565167353836046469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082757710111569224030979 10624136565167353836046469)
                    ·
                      refine ⟨1992025605968878844258713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10624136565167353836046469 1992025605968878844258713)
                      ·
                        rfl

theorem cell23_3879456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3879456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879456 prefixEnd_3879456 := by exact prefixLift 3879456
  have htrace : WordTrace (prefixWord ++ tailWord_3879456) baseStart_3879456 baseEnd_3879456 := by
    simpa [prefixWord, tailWord_3879456, baseEnd_3879456] using wordTrace_append hprefix tailTrace_3879456
  have hstable : (prefixWord ++ tailWord_3879456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879456).length < 2 ^ (prefixWord ++ tailWord_3879456).sum := by decide
  have hdescent : baseEnd_3879456 < baseStart_3879456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879459 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 3]
def baseStart_3879459 : Nat := 118140960795 + 3879459 * 2 ^ 59
def prefixEnd_3879459 : Nat := 4983230072969 + 3 ^ 40 * 3879459 * 2
def baseEnd_3879459 : Nat := 1992027146410842332521199

theorem tailTrace_3879459 : CollatzResearch.WordTrace tailWord_3879459 prefixEnd_3879459 1992027146410842332521199 := by
  unfold tailWord_3879459
  simp only [CollatzResearch.WordTrace]
  refine ⟨141495494052390076693305431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94330329368260051128870287 141495494052390076693305431)
  ·
    refine ⟨212243241078585115039958147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141495494052390076693305431 212243241078585115039958147)
    ·
      refine ⟨318364861617877672559937221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212243241078585115039958147 318364861617877672559937221)
      ·
        refine ⟨59693411553352063604988229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318364861617877672559937221 59693411553352063604988229)
        ·
          refine ⟨11192514666253511925935293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59693411553352063604988229 11192514666253511925935293)
          ·
            refine ⟨4197192999845066972225735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11192514666253511925935293 4197192999845066972225735)
            ·
              refine ⟨6295789499767600458338603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197192999845066972225735 6295789499767600458338603)
              ·
                refine ⟨9443684249651400687507905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295789499767600458338603 9443684249651400687507905)
                ·
                  refine ⟨7082763187238550515630929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443684249651400687507905 7082763187238550515630929)
                  ·
                    refine ⟨5312072390428912886723197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082763187238550515630929 5312072390428912886723197)
                    ·
                      refine ⟨1992027146410842332521199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312072390428912886723197 1992027146410842332521199)
                      ·
                        rfl

theorem cell23_3879459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_3879459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879459 prefixEnd_3879459 := by exact prefixLift 3879459
  have htrace : WordTrace (prefixWord ++ tailWord_3879459) baseStart_3879459 baseEnd_3879459 := by
    simpa [prefixWord, tailWord_3879459, baseEnd_3879459] using wordTrace_append hprefix tailTrace_3879459
  have hstable : (prefixWord ++ tailWord_3879459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879459).length < 2 ^ (prefixWord ++ tailWord_3879459).sum := by decide
  have hdescent : baseEnd_3879459 < baseStart_3879459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879466 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3879466 : Nat := 118140960795 + 3879466 * 2 ^ 59
def prefixEnd_3879466 : Nat := 4983230072969 + 3 ^ 40 * 3879466 * 2
def baseEnd_3879466 : Nat := 664010246925141268377889

theorem tailTrace_3879466 : CollatzResearch.WordTrace tailWord_3879466 prefixEnd_3879466 664010246925141268377889 := by
  unfold tailWord_3879466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373937340841179222202563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94330499575576477925873501 35373937340841179222202563)
  ·
    refine ⟨53060906011261768833303845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35373937340841179222202563 53060906011261768833303845)
    ·
      refine ⟨9948919877111581656244471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53060906011261768833303845 9948919877111581656244471)
      ·
        refine ⟨14923379815667372484366707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948919877111581656244471 14923379815667372484366707)
        ·
          refine ⟨22385069723501058726550061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923379815667372484366707 22385069723501058726550061)
          ·
            refine ⟨8394401146312897022456273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22385069723501058726550061 8394401146312897022456273)
            ·
              refine ⟨6295800859734672766842205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8394401146312897022456273 6295800859734672766842205)
              ·
                refine ⟨2360925322400502287565827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6295800859734672766842205 2360925322400502287565827)
                ·
                  refine ⟨3541387983600753431348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360925322400502287565827 3541387983600753431348741)
                  ·
                    refine ⟨664010246925141268377889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541387983600753431348741 664010246925141268377889)
                    ·
                      rfl

theorem cell23_3879466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3879466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879466 prefixEnd_3879466 := by exact prefixLift 3879466
  have htrace : WordTrace (prefixWord ++ tailWord_3879466) baseStart_3879466 baseEnd_3879466 := by
    simpa [prefixWord, tailWord_3879466, baseEnd_3879466] using wordTrace_append hprefix tailTrace_3879466
  have hstable : (prefixWord ++ tailWord_3879466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879466).length < 2 ^ (prefixWord ++ tailWord_3879466).sum := by decide
  have hdescent : baseEnd_3879466 < baseStart_3879466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879489 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3879489 : Nat := 118140960795 + 3879489 * 2 ^ 59
def prefixEnd_3879489 : Nat := 4983230072969 + 3 ^ 40 * 3879489 * 2
def baseEnd_3879489 : Nat := 1992042550830477215146061

theorem tailTrace_3879489 : CollatzResearch.WordTrace tailWord_3879489 prefixEnd_3879489 1992042550830477215146061 := by
  unfold tailWord_3879489
  simp only [CollatzResearch.WordTrace]
  refine ⟨141496588242281391816897521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94331058828187594544598347 141496588242281391816897521)
  ·
    refine ⟨106122441181711043862673141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141496588242281391816897521 106122441181711043862673141)
    ·
      refine ⟨9948978860785410362125607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106122441181711043862673141 9948978860785410362125607)
      ·
        refine ⟨14923468291178115543188411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948978860785410362125607 14923468291178115543188411)
        ·
          refine ⟨22385202436767173314782617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923468291178115543188411 22385202436767173314782617)
          ·
            refine ⟨16788901827575379986086963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22385202436767173314782617 16788901827575379986086963)
            ·
              refine ⟨25183352741363069979130445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16788901827575379986086963 25183352741363069979130445)
              ·
                refine ⟨9443757278011151242173917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25183352741363069979130445 9443757278011151242173917)
                ·
                  refine ⟨3541408979254181715815219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9443757278011151242173917 3541408979254181715815219)
                  ·
                    refine ⟨5312113468881272573722829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541408979254181715815219 5312113468881272573722829)
                    ·
                      refine ⟨1992042550830477215146061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312113468881272573722829 1992042550830477215146061)
                      ·
                        rfl

theorem cell23_3879489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3879489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879489 prefixEnd_3879489 := by exact prefixLift 3879489
  have htrace : WordTrace (prefixWord ++ tailWord_3879489) baseStart_3879489 baseEnd_3879489 := by
    simpa [prefixWord, tailWord_3879489, baseEnd_3879489] using wordTrace_append hprefix tailTrace_3879489
  have hstable : (prefixWord ++ tailWord_3879489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879489).length < 2 ^ (prefixWord ++ tailWord_3879489).sum := by decide
  have hdescent : baseEnd_3879489 < baseStart_3879489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879512 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3879512 : Nat := 118140960795 + 3879512 * 2 ^ 59
def prefixEnd_3879512 : Nat := 4983230072969 + 3 ^ 40 * 3879512 * 2
def baseEnd_3879512 : Nat := 1992054360885530625158455

theorem tailTrace_3879512 : CollatzResearch.WordTrace tailWord_3879512 prefixEnd_3879512 1992054360885530625158455 := by
  unfold tailWord_3879512
  simp only [CollatzResearch.WordTrace]
  refine ⟨70748713560599033372492395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94331618080798711163323193 70748713560599033372492395)
  ·
    refine ⟨106123070340898550058738593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70748713560599033372492395 106123070340898550058738593)
    ·
      refine ⟨79592302755673912544053945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106123070340898550058738593 79592302755673912544053945)
      ·
        refine ⟨59694227066755434408040459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79592302755673912544053945 59694227066755434408040459)
        ·
          refine ⟨89541340600133151612060689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59694227066755434408040459 89541340600133151612060689)
          ·
            refine ⟨67156005450099863709045517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89541340600133151612060689 67156005450099863709045517)
            ·
              refine ⟨25183502043787448890892069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67156005450099863709045517 25183502043787448890892069)
              ·
                refine ⟨4721906633210146667042263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25183502043787448890892069 4721906633210146667042263)
                ·
                  refine ⟨7082859949815220000563395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721906633210146667042263 7082859949815220000563395)
                  ·
                    refine ⟨10624289924722830000845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082859949815220000563395 10624289924722830000845093)
                    ·
                      refine ⟨1992054360885530625158455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10624289924722830000845093 1992054360885530625158455)
                      ·
                        rfl

theorem cell23_3879512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3879512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879512 prefixEnd_3879512 := by exact prefixLift 3879512
  have htrace : WordTrace (prefixWord ++ tailWord_3879512) baseStart_3879512 baseEnd_3879512 := by
    simpa [prefixWord, tailWord_3879512, baseEnd_3879512] using wordTrace_append hprefix tailTrace_3879512
  have hstable : (prefixWord ++ tailWord_3879512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879512).length < 2 ^ (prefixWord ++ tailWord_3879512).sum := by decide
  have hdescent : baseEnd_3879512 < baseStart_3879512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879556 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3879556 : Nat := 118140960795 + 3879556 * 2 ^ 59
def prefixEnd_3879556 : Nat := 4983230072969 + 3 ^ 40 * 3879556 * 2
def baseEnd_3879556 : Nat := 664025651344776151002751

theorem tailTrace_3879556 : CollatzResearch.WordTrace tailWord_3879556 prefixEnd_3879556 664025651344776151002751 := by
  unfold tailWord_3879556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70749515966519331129793261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94332687955359108173057681 70749515966519331129793261)
  ·
    refine ⟨26531068487444749173672473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70749515966519331129793261 26531068487444749173672473)
    ·
      refine ⟨19898301365583561880254355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26531068487444749173672473 19898301365583561880254355)
      ·
        refine ⟨29847452048375342820381533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898301365583561880254355 29847452048375342820381533)
        ·
          refine ⟨11192794518140753557643075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29847452048375342820381533 11192794518140753557643075)
          ·
            refine ⟨16789191777211130336464613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192794518140753557643075 16789191777211130336464613)
            ·
              refine ⟨3147973458227086938087115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16789191777211130336464613 3147973458227086938087115)
              ·
                refine ⟨4721960187340630407130673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147973458227086938087115 4721960187340630407130673)
                ·
                  refine ⟨3541470140505472805348005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721960187340630407130673 3541470140505472805348005)
                  ·
                    refine ⟨664025651344776151002751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541470140505472805348005 664025651344776151002751)
                    ·
                      rfl

theorem cell23_3879556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3879556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879556 prefixEnd_3879556 := by exact prefixLift 3879556
  have htrace : WordTrace (prefixWord ++ tailWord_3879556) baseStart_3879556 baseEnd_3879556 := by
    simpa [prefixWord, tailWord_3879556, baseEnd_3879556] using wordTrace_append hprefix tailTrace_3879556
  have hstable : (prefixWord ++ tailWord_3879556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879556).length < 2 ^ (prefixWord ++ tailWord_3879556).sum := by decide
  have hdescent : baseEnd_3879556 < baseStart_3879556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879597 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_3879597 : Nat := 118140960795 + 3879597 * 2 ^ 59
def prefixEnd_3879597 : Nat := 4983230072969 + 3 ^ 40 * 3879597 * 2
def baseEnd_3879597 : Nat := 1992098006741162792595565

theorem tailTrace_3879597 : CollatzResearch.WordTrace tailWord_3879597 prefixEnd_3879597 1992098006741162792595565 := by
  unfold tailWord_3879597
  simp only [CollatzResearch.WordTrace]
  refine ⟨141500527325890126261829045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94333684883926750841219363 141500527325890126261829045)
  ·
    refine ⟨13265674436802199337046473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141500527325890126261829045 13265674436802199337046473)
    ·
      refine ⟨9949255827601649502784855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13265674436802199337046473 9949255827601649502784855)
      ·
        refine ⟨14923883741402474254177283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9949255827601649502784855 14923883741402474254177283)
        ·
          refine ⟨22385825612103711381265925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923883741402474254177283 22385825612103711381265925)
          ·
            refine ⟨4197342302269445883987361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22385825612103711381265925 4197342302269445883987361)
            ·
              refine ⟨3148006726702084412990521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197342302269445883987361 3148006726702084412990521)
              ·
                refine ⟨2361005045026563309742891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148006726702084412990521 2361005045026563309742891)
                ·
                  refine ⟨3541507567539844964614337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361005045026563309742891 3541507567539844964614337)
                  ·
                    refine ⟨2656130675654883723460753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541507567539844964614337 2656130675654883723460753)
                    ·
                      refine ⟨1992098006741162792595565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656130675654883723460753 1992098006741162792595565)
                      ·
                        rfl

theorem cell23_3879597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_3879597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879597 prefixEnd_3879597 := by exact prefixLift 3879597
  have htrace : WordTrace (prefixWord ++ tailWord_3879597) baseStart_3879597 baseEnd_3879597 := by
    simpa [prefixWord, tailWord_3879597, baseEnd_3879597] using wordTrace_append hprefix tailTrace_3879597
  have hstable : (prefixWord ++ tailWord_3879597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879597).length < 2 ^ (prefixWord ++ tailWord_3879597).sum := by decide
  have hdescent : baseEnd_3879597 < baseStart_3879597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879612 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_3879612 : Nat := 118140960795 + 3879612 * 2 ^ 59
def prefixEnd_3879612 : Nat := 4983230072969 + 3 ^ 40 * 3879612 * 2
def baseEnd_3879612 : Nat := 664035236316993411302665

theorem tailTrace_3879612 : CollatzResearch.WordTrace tailWord_3879612 prefixEnd_3879612 664035236316993411302665 := by
  unfold tailWord_3879612
  simp only [CollatzResearch.WordTrace]
  refine ⟨70750537210417891911812545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94334049613890522549083393 70750537210417891911812545)
  ·
    refine ⟨53062902907813418933859409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70750537210417891911812545 53062902907813418933859409)
    ·
      refine ⟨39797177180860064200394557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53062902907813418933859409 39797177180860064200394557)
      ·
        refine ⟨14923941442822524075147959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39797177180860064200394557 14923941442822524075147959)
        ·
          refine ⟨22385912164233786112721939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14923941442822524075147959 22385912164233786112721939)
          ·
            refine ⟨33578868246350679169082909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22385912164233786112721939 33578868246350679169082909)
            ·
              refine ⟨12592075592381504688406091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33578868246350679169082909 12592075592381504688406091)
              ·
                refine ⟨18888113388572257032609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12592075592381504688406091 18888113388572257032609137)
                ·
                  refine ⟨14166085041429192774456853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18888113388572257032609137 14166085041429192774456853)
                  ·
                    refine ⟨664035236316993411302665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14166085041429192774456853 664035236316993411302665)
                    ·
                      rfl

theorem cell23_3879612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_3879612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879612 prefixEnd_3879612 := by exact prefixLift 3879612
  have htrace : WordTrace (prefixWord ++ tailWord_3879612) baseStart_3879612 baseEnd_3879612 := by
    simpa [prefixWord, tailWord_3879612, baseEnd_3879612] using wordTrace_append hprefix tailTrace_3879612
  have hstable : (prefixWord ++ tailWord_3879612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879612).length < 2 ^ (prefixWord ++ tailWord_3879612).sum := by decide
  have hdescent : baseEnd_3879612 < baseStart_3879612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879653 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3879653 : Nat := 118140960795 + 3879653 * 2 ^ 59
def prefixEnd_3879653 : Nat := 4983230072969 + 3 ^ 40 * 3879653 * 2
def baseEnd_3879653 : Nat := 1992126761657814573495307

theorem tailTrace_3879653 : CollatzResearch.WordTrace tailWord_3879653 prefixEnd_3879653 1992126761657814573495307 := by
  unfold tailWord_3879653
  simp only [CollatzResearch.WordTrace]
  refine ⟨141502569813687247825867613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94335046542458165217245075 141502569813687247825867613)
  ·
    refine ⟨53063463680132717934700355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141502569813687247825867613 53063463680132717934700355)
    ·
      refine ⟨79595195520199076902050533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53063463680132717934700355 79595195520199076902050533)
      ·
        refine ⟨14924099160037326919134475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79595195520199076902050533 14924099160037326919134475)
        ·
          refine ⟨22386148740055990378701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924099160037326919134475 22386148740055990378701713)
          ·
            refine ⟨16789611555041992784026285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22386148740055990378701713 16789611555041992784026285)
            ·
              refine ⟨6296104333140747294009857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16789611555041992784026285 6296104333140747294009857)
              ·
                refine ⟨4722078249855560470507393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296104333140747294009857 4722078249855560470507393)
                ·
                  refine ⟨3541558687391670352880545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722078249855560470507393 3541558687391670352880545)
                  ·
                    refine ⟨2656169015543752764660409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541558687391670352880545 2656169015543752764660409)
                    ·
                      refine ⟨1992126761657814573495307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656169015543752764660409 1992126761657814573495307)
                      ·
                        rfl

theorem cell23_3879653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3879653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879653 prefixEnd_3879653 := by exact prefixLift 3879653
  have htrace : WordTrace (prefixWord ++ tailWord_3879653) baseStart_3879653 baseEnd_3879653 := by
    simpa [prefixWord, tailWord_3879653, baseEnd_3879653] using wordTrace_append hprefix tailTrace_3879653
  have hstable : (prefixWord ++ tailWord_3879653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879653).length < 2 ^ (prefixWord ++ tailWord_3879653).sum := by decide
  have hdescent : baseEnd_3879653 < baseStart_3879653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879670 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3879670 : Nat := 118140960795 + 3879670 * 2 ^ 59
def prefixEnd_3879670 : Nat := 4983230072969 + 3 ^ 40 * 3879670 * 2
def baseEnd_3879670 : Nat := 1992135490828941006982729

theorem tailTrace_3879670 : CollatzResearch.WordTrace tailWord_3879670 prefixEnd_3879670 1992135490828941006982729 := by
  unfold tailWord_3879670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843949365914103733077279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94335459903083773152824309 8843949365914103733077279)
  ·
    refine ⟨13265924048871155599615919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843949365914103733077279 13265924048871155599615919)
    ·
      refine ⟨19898886073306733399423879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265924048871155599615919 19898886073306733399423879)
      ·
        refine ⟨29848329109960100099135819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898886073306733399423879 29848329109960100099135819)
        ·
          refine ⟨44772493664940150148703729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29848329109960100099135819 44772493664940150148703729)
          ·
            refine ⟨33579370248705112611527797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44772493664940150148703729 33579370248705112611527797)
            ·
              refine ⟨3148065960816104307330731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33579370248705112611527797 3148065960816104307330731)
              ·
                refine ⟨4722098941224156460996097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148065960816104307330731 4722098941224156460996097)
                ·
                  refine ⟨3541574205918117345747073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722098941224156460996097 3541574205918117345747073)
                  ·
                    refine ⟨2656180654438588009310305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541574205918117345747073 2656180654438588009310305)
                    ·
                      refine ⟨1992135490828941006982729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656180654438588009310305 1992135490828941006982729)
                      ·
                        rfl

theorem cell23_3879670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3879670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879670 prefixEnd_3879670 := by exact prefixLift 3879670
  have htrace : WordTrace (prefixWord ++ tailWord_3879670) baseStart_3879670 baseEnd_3879670 := by
    simpa [prefixWord, tailWord_3879670, baseEnd_3879670] using wordTrace_append hprefix tailTrace_3879670
  have hstable : (prefixWord ++ tailWord_3879670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879670).length < 2 ^ (prefixWord ++ tailWord_3879670).sum := by decide
  have hdescent : baseEnd_3879670 < baseStart_3879670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879729 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3879729 : Nat := 118140960795 + 3879729 * 2 ^ 59
def prefixEnd_3879729 : Nat := 4983230072969 + 3 ^ 40 * 3879729 * 2
def baseEnd_3879729 : Nat := 1992165786187556276144957

theorem tailTrace_3879729 : CollatzResearch.WordTrace tailWord_3879729 prefixEnd_3879729 1992165786187556276144957 := by
  unfold tailWord_3879729
  simp only [CollatzResearch.WordTrace]
  refine ⟨141505341761411912805634241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94336894507607941870422827 141505341761411912805634241)
  ·
    refine ⟨106129006321058934604225681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141505341761411912805634241 106129006321058934604225681)
    ·
      refine ⟨79596754740794200953169261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106129006321058934604225681 79596754740794200953169261)
      ·
        refine ⟨29848783027797825357438473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79596754740794200953169261 29848783027797825357438473)
        ·
          refine ⟨22386587270848369018078855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29848783027797825357438473 22386587270848369018078855)
          ·
            refine ⟨33579880906272553527118283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22386587270848369018078855 33579880906272553527118283)
            ·
              refine ⟨50369821359408830290677425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33579880906272553527118283 50369821359408830290677425)
              ·
                refine ⟨37777366019556622718008069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50369821359408830290677425 37777366019556622718008069)
                ·
                  refine ⟨7083256128666866759626513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37777366019556622718008069 7083256128666866759626513)
                  ·
                    refine ⟨5312442096500150069719885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7083256128666866759626513 5312442096500150069719885)
                    ·
                      refine ⟨1992165786187556276144957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312442096500150069719885 1992165786187556276144957)
                      ·
                        rfl

theorem cell23_3879729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3879729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879729 prefixEnd_3879729 := by exact prefixLift 3879729
  have htrace : WordTrace (prefixWord ++ tailWord_3879729) baseStart_3879729 baseEnd_3879729 := by
    simpa [prefixWord, tailWord_3879729, baseEnd_3879729] using wordTrace_append hprefix tailTrace_3879729
  have hstable : (prefixWord ++ tailWord_3879729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879729).length < 2 ^ (prefixWord ++ tailWord_3879729).sum := by decide
  have hdescent : baseEnd_3879729 < baseStart_3879729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879770 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_3879770 : Nat := 118140960795 + 3879770 * 2 ^ 59
def prefixEnd_3879770 : Nat := 4983230072969 + 3 ^ 40 * 3879770 * 2
def baseEnd_3879770 : Nat := 664062279631463538577423

theorem tailTrace_3879770 : CollatzResearch.WordTrace tailWord_3879770 prefixEnd_3879770 664062279631463538577423 := by
  unfold tailWord_3879770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35376709288565844201969191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94337891436175584538584509 35376709288565844201969191)
  ·
    refine ⟨53065063932848766302953787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35376709288565844201969191 53065063932848766302953787)
    ·
      refine ⟨79597595899273149454430681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53065063932848766302953787 79597595899273149454430681)
      ·
        refine ⟨59698196924454862090823011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79597595899273149454430681 59698196924454862090823011)
        ·
          refine ⟨89547295386682293136234517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59698196924454862090823011 89547295386682293136234517)
          ·
            refine ⟨4197529471250732490760993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89547295386682293136234517 4197529471250732490760993)
            ·
              refine ⟨3148147103438049368070745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197529471250732490760993 3148147103438049368070745)
              ·
                refine ⟨2361110327578537026053059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148147103438049368070745 2361110327578537026053059)
                ·
                  refine ⟨3541665491367805539079589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361110327578537026053059 3541665491367805539079589)
                  ·
                    refine ⟨664062279631463538577423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541665491367805539079589 664062279631463538577423)
                    ·
                      rfl

theorem cell23_3879770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_3879770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879770 prefixEnd_3879770 := by exact prefixLift 3879770
  have htrace : WordTrace (prefixWord ++ tailWord_3879770) baseStart_3879770 baseEnd_3879770 := by
    simpa [prefixWord, tailWord_3879770, baseEnd_3879770] using wordTrace_append hprefix tailTrace_3879770
  have hstable : (prefixWord ++ tailWord_3879770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879770).length < 2 ^ (prefixWord ++ tailWord_3879770).sum := by decide
  have hdescent : baseEnd_3879770 < baseStart_3879770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879776 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3879776 : Nat := 118140960795 + 3879776 * 2 ^ 59
def prefixEnd_3879776 : Nat := 4983230072969 + 3 ^ 40 * 3879776 * 2
def baseEnd_3879776 : Nat := 1992189919778317592257241

theorem tailTrace_3879776 : CollatzResearch.WordTrace tailWord_3879776 prefixEnd_3879776 1992189919778317592257241 := by
  unfold tailWord_3879776
  simp only [CollatzResearch.WordTrace]
  refine ⟨70753527996120819916297591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94338037328161093221730121 70753527996120819916297591)
  ·
    refine ⟨106130291994181229874446387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70753527996120819916297591 106130291994181229874446387)
    ·
      refine ⟨159195437991271844811669581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106130291994181229874446387 159195437991271844811669581)
      ·
        refine ⟨59698289246726941804376093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159195437991271844811669581 59698289246726941804376093)
        ·
          refine ⟨22386858467522603176641035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59698289246726941804376093 22386858467522603176641035)
          ·
            refine ⟨33580287701283904764961553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22386858467522603176641035 33580287701283904764961553)
            ·
              refine ⟨25185215775962928573721165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33580287701283904764961553 25185215775962928573721165)
              ·
                refine ⟨9444455915986098215145437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25185215775962928573721165 9444455915986098215145437)
                ·
                  refine ⟨3541670968494786830679539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9444455915986098215145437 3541670968494786830679539)
                  ·
                    refine ⟨5312506452742180246019309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541670968494786830679539 5312506452742180246019309)
                    ·
                      refine ⟨1992189919778317592257241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312506452742180246019309 1992189919778317592257241)
                      ·
                        rfl

theorem cell23_3879776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3879776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879776 prefixEnd_3879776 := by exact prefixLift 3879776
  have htrace : WordTrace (prefixWord ++ tailWord_3879776) baseStart_3879776 baseEnd_3879776 := by
    simpa [prefixWord, tailWord_3879776, baseEnd_3879776] using wordTrace_append hprefix tailTrace_3879776
  have hstable : (prefixWord ++ tailWord_3879776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879776).length < 2 ^ (prefixWord ++ tailWord_3879776).sum := by decide
  have hdescent : baseEnd_3879776 < baseStart_3879776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879779 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 3, 5]
def baseStart_3879779 : Nat := 118140960795 + 3879779 * 2 ^ 59
def prefixEnd_3879779 : Nat := 4983230072969 + 3 ^ 40 * 3879779 * 2
def baseEnd_3879779 : Nat := 664063820073427026839909

theorem tailTrace_3879779 : CollatzResearch.WordTrace tailWord_3879779 prefixEnd_3879779 664063820073427026839909 := by
  unfold tailWord_3879779
  simp only [CollatzResearch.WordTrace]
  refine ⟨141507165411230771344954391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94338110274153847563302927 141507165411230771344954391)
  ·
    refine ⟨212260748116846157017431587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141507165411230771344954391 212260748116846157017431587)
    ·
      refine ⟨318391122175269235526147381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212260748116846157017431587 318391122175269235526147381)
      ·
        refine ⟨29849167703931490830576317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318391122175269235526147381 29849167703931490830576317)
        ·
          refine ⟨11193437888974309061466119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29849167703931490830576317 11193437888974309061466119)
          ·
            refine ⟨16790156833461463592199179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11193437888974309061466119 16790156833461463592199179)
            ·
              refine ⟨25185235250192195388298769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16790156833461463592199179 25185235250192195388298769)
              ·
                refine ⟨18888926437644146541224077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25185235250192195388298769 18888926437644146541224077)
                ·
                  refine ⟨7083347414116554952959029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18888926437644146541224077 7083347414116554952959029)
                  ·
                    refine ⟨664063820073427026839909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7083347414116554952959029 664063820073427026839909)
                    ·
                      rfl

theorem cell23_3879779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 5].length) (baseStart_3879779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879779 prefixEnd_3879779 := by exact prefixLift 3879779
  have htrace : WordTrace (prefixWord ++ tailWord_3879779) baseStart_3879779 baseEnd_3879779 := by
    simpa [prefixWord, tailWord_3879779, baseEnd_3879779] using wordTrace_append hprefix tailTrace_3879779
  have hstable : (prefixWord ++ tailWord_3879779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879779).length < 2 ^ (prefixWord ++ tailWord_3879779).sum := by decide
  have hdescent : baseEnd_3879779 < baseStart_3879779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879813 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_3879813 : Nat := 118140960795 + 3879813 * 2 ^ 59
def prefixEnd_3879813 : Nat := 4983230072969 + 3 ^ 40 * 3879813 * 2
def baseEnd_3879813 : Nat := 664069639520844649164857

theorem tailTrace_3879813 : CollatzResearch.WordTrace tailWord_3879813 prefixEnd_3879813 664069639520844649164857 := by
  unfold tailWord_3879813
  simp only [CollatzResearch.WordTrace]
  refine ⟨141508405493107595151692093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94338936995405063434461395 141508405493107595151692093)
  ·
    refine ⟨53065652059915348181884535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141508405493107595151692093 53065652059915348181884535)
    ·
      refine ⟨79598478089873022272826803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53065652059915348181884535 79598478089873022272826803)
      ·
        refine ⟨119397717134809533409240205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79598478089873022272826803 119397717134809533409240205)
        ·
          refine ⟨44774143925553575028465077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119397717134809533409240205 44774143925553575028465077)
          ·
            refine ⟨4197575993020647658918601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44774143925553575028465077 4197575993020647658918601)
            ·
              refine ⟨3148181994765485744188951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197575993020647658918601 3148181994765485744188951)
              ·
                refine ⟨4722272992148228616283427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148181994765485744188951 4722272992148228616283427)
                ·
                  refine ⟨7083409488222342924425141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722272992148228616283427 7083409488222342924425141)
                  ·
                    refine ⟨664069639520844649164857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7083409488222342924425141 664069639520844649164857)
                    ·
                      rfl

theorem cell23_3879813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_3879813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879813 prefixEnd_3879813 := by exact prefixLift 3879813
  have htrace : WordTrace (prefixWord ++ tailWord_3879813) baseStart_3879813 baseEnd_3879813 := by
    simpa [prefixWord, tailWord_3879813, baseEnd_3879813] using wordTrace_append hprefix tailTrace_3879813
  have hstable : (prefixWord ++ tailWord_3879813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879813).length < 2 ^ (prefixWord ++ tailWord_3879813).sum := by decide
  have hdescent : baseEnd_3879813 < baseStart_3879813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879866 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_3879866 : Nat := 118140960795 + 3879866 * 2 ^ 59
def prefixEnd_3879866 : Nat := 4983230072969 + 3 ^ 40 * 3879866 * 2
def baseEnd_3879866 : Nat := 1992236133037222240131827

theorem tailTrace_3879866 : CollatzResearch.WordTrace tailWord_3879866 prefixEnd_3879866 1992236133037222240131827 := by
  unfold tailWord_3879866
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377584640478896300842863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94340225707943723468914301 35377584640478896300842863)
  ·
    refine ⟨53066376960718344451264295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35377584640478896300842863 53066376960718344451264295)
    ·
      refine ⟨79599565441077516676896443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53066376960718344451264295 79599565441077516676896443)
      ·
        refine ⟨119399348161616275015344665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79599565441077516676896443 119399348161616275015344665)
        ·
          refine ⟨89549511121212206261508499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119399348161616275015344665 89549511121212206261508499)
          ·
            refine ⟨134324266681818309392262749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89549511121212206261508499 134324266681818309392262749)
            ·
              refine ⟨50371600005681866022098531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134324266681818309392262749 50371600005681866022098531)
              ·
                refine ⟨75557400008522799033147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50371600005681866022098531 75557400008522799033147797)
                ·
                  refine ⟨3541753125399506204678803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75557400008522799033147797 3541753125399506204678803)
                  ·
                    refine ⟨5312629688099259307018205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541753125399506204678803 5312629688099259307018205)
                    ·
                      refine ⟨1992236133037222240131827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312629688099259307018205 1992236133037222240131827)
                      ·
                        rfl

theorem cell23_3879866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_3879866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879866 prefixEnd_3879866 := by exact prefixLift 3879866
  have htrace : WordTrace (prefixWord ++ tailWord_3879866) baseStart_3879866 baseEnd_3879866 := by
    simpa [prefixWord, tailWord_3879866, baseEnd_3879866] using wordTrace_append hprefix tailTrace_3879866
  have hstable : (prefixWord ++ tailWord_3879866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879866).length < 2 ^ (prefixWord ++ tailWord_3879866).sum := by decide
  have hdescent : baseEnd_3879866 < baseStart_3879866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879878 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3879878 : Nat := 118140960795 + 3879878 * 2 ^ 59
def prefixEnd_3879878 : Nat := 4983230072969 + 3 ^ 40 * 3879878 * 2
def baseEnd_3879878 : Nat := 1992242294805076193181773

theorem tailTrace_3879878 : CollatzResearch.WordTrace tailWord_3879878 prefixEnd_3879878 1992242294805076193181773 := by
  unfold tailWord_3879878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422211757433503476650259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94340517491914740835205525 4422211757433503476650259)
  ·
    refine ⟨6633317636150255214975389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422211757433503476650259 6633317636150255214975389)
    ·
      refine ⟨2487494113556345705615771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6633317636150255214975389 2487494113556345705615771)
      ·
        refine ⟨3731241170334518558423657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487494113556345705615771 3731241170334518558423657)
        ·
          refine ⟨2798430877750888918817743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731241170334518558423657 2798430877750888918817743)
          ·
            refine ⟨4197646316626333378226615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798430877750888918817743 4197646316626333378226615)
            ·
              refine ⟨6296469474939500067339923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197646316626333378226615 6296469474939500067339923)
              ·
                refine ⟨9444704212409250101009885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296469474939500067339923 9444704212409250101009885)
                ·
                  refine ⟨3541764079653468787878707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9444704212409250101009885 3541764079653468787878707)
                  ·
                    refine ⟨5312646119480203181818061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541764079653468787878707 5312646119480203181818061)
                    ·
                      refine ⟨1992242294805076193181773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312646119480203181818061 1992242294805076193181773)
                      ·
                        rfl

theorem cell23_3879878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3879878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879878 prefixEnd_3879878 := by exact prefixLift 3879878
  have htrace : WordTrace (prefixWord ++ tailWord_3879878) baseStart_3879878 baseEnd_3879878 := by
    simpa [prefixWord, tailWord_3879878, baseEnd_3879878] using wordTrace_append hprefix tailTrace_3879878
  have hstable : (prefixWord ++ tailWord_3879878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879878).length < 2 ^ (prefixWord ++ tailWord_3879878).sum := by decide
  have hdescent : baseEnd_3879878 < baseStart_3879878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879889 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_3879889 : Nat := 118140960795 + 3879889 * 2 ^ 59
def prefixEnd_3879889 : Nat := 4983230072969 + 3 ^ 40 * 3879889 * 2
def baseEnd_3879889 : Nat := 1992247943092275650144221

theorem tailTrace_3879889 : CollatzResearch.WordTrace tailWord_3879889 prefixEnd_3879889 1992247943092275650144221 := by
  unfold tailWord_3879889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141511177440832260131458721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94340784960554840087639147 141511177440832260131458721)
  ·
    refine ⟨106133383080624195098594041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141511177440832260131458721 106133383080624195098594041)
    ·
      refine ⟨79600037310468146323945531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106133383080624195098594041 79600037310468146323945531)
      ·
        refine ⟨119400055965702219485918297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79600037310468146323945531 119400055965702219485918297)
        ·
          refine ⟨89550041974276664614438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119400055965702219485918297 89550041974276664614438723)
          ·
            refine ⟨134325062961414996921658085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89550041974276664614438723 134325062961414996921658085)
            ·
              refine ⟨25185949305265311922810891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134325062961414996921658085 25185949305265311922810891)
              ·
                refine ⟨37778923957897967884216337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25185949305265311922810891 37778923957897967884216337)
                ·
                  refine ⟨28334192968423475913162253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37778923957897967884216337 28334192968423475913162253)
                  ·
                    refine ⟨10625322363158803467435845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28334192968423475913162253 10625322363158803467435845)
                    ·
                      refine ⟨1992247943092275650144221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10625322363158803467435845 1992247943092275650144221)
                      ·
                        rfl

theorem cell23_3879889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_3879889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3879889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3879889 prefixEnd_3879889 := by exact prefixLift 3879889
  have htrace : WordTrace (prefixWord ++ tailWord_3879889) baseStart_3879889 baseEnd_3879889 := by
    simpa [prefixWord, tailWord_3879889, baseEnd_3879889] using wordTrace_append hprefix tailTrace_3879889
  have hstable : (prefixWord ++ tailWord_3879889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879889).length < 2 ^ (prefixWord ++ tailWord_3879889).sum := by decide
  have hdescent : baseEnd_3879889 < baseStart_3879889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880013 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3880013 : Nat := 118140960795 + 3880013 * 2 ^ 59
def prefixEnd_3880013 : Nat := 4983230072969 + 3 ^ 40 * 3880013 * 2
def baseEnd_3880013 : Nat := 1992311614693433164993651

theorem tailTrace_3880013 : CollatzResearch.WordTrace tailWord_3880013 prefixEnd_3880013 1992311614693433164993651 := by
  unfold tailWord_3880013
  simp only [CollatzResearch.WordTrace]
  refine ⟨141515700092383029308972693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94343800061588686205981795 141515700092383029308972693)
  ·
    refine ⟨6633548441830454498858095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141515700092383029308972693 6633548441830454498858095)
    ·
      refine ⟨9950322662745681748287143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633548441830454498858095 9950322662745681748287143)
      ·
        refine ⟨14925483994118522622430715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950322662745681748287143 14925483994118522622430715)
        ·
          refine ⟨22388225991177783933646073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925483994118522622430715 22388225991177783933646073)
          ·
            refine ⟨16791169493383337950234555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22388225991177783933646073 16791169493383337950234555)
            ·
              refine ⟨25186754240075006925351833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791169493383337950234555 25186754240075006925351833)
              ·
                refine ⟨18890065680056255194013875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25186754240075006925351833 18890065680056255194013875)
                ·
                  refine ⟨28335098520084382791020813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18890065680056255194013875 28335098520084382791020813)
                  ·
                    refine ⟨10625661945031643546632805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28335098520084382791020813 10625661945031643546632805)
                    ·
                      refine ⟨1992311614693433164993651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10625661945031643546632805 1992311614693433164993651)
                      ·
                        rfl

theorem cell23_3880013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3880013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880013 prefixEnd_3880013 := by exact prefixLift 3880013
  have htrace : WordTrace (prefixWord ++ tailWord_3880013) baseStart_3880013 baseEnd_3880013 := by
    simpa [prefixWord, tailWord_3880013, baseEnd_3880013] using wordTrace_append hprefix tailTrace_3880013
  have hstable : (prefixWord ++ tailWord_3880013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880013).length < 2 ^ (prefixWord ++ tailWord_3880013).sum := by decide
  have hdescent : baseEnd_3880013 < baseStart_3880013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880019 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 10]
def baseStart_3880019 : Nat := 118140960795 + 3880019 * 2 ^ 59
def prefixEnd_3880019 : Nat := 4983230072969 + 3 ^ 40 * 3880019 * 2
def baseEnd_3880019 : Nat := 221368299508595571279847

theorem tailTrace_3880019 : CollatzResearch.WordTrace tailWord_3880019 prefixEnd_3880019 221368299508595571279847 := by
  unfold tailWord_3880019
  simp only [CollatzResearch.WordTrace]
  refine ⟨141515918930361292333691111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94343945953574194889127407 141515918930361292333691111)
  ·
    refine ⟨212273878395541938500536667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141515918930361292333691111 212273878395541938500536667)
    ·
      refine ⟨318410817593312907750805001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212273878395541938500536667 318410817593312907750805001)
      ·
        refine ⟨238808113194984680813103751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318410817593312907750805001 238808113194984680813103751)
        ·
          refine ⟨358212169792477021219655627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238808113194984680813103751 358212169792477021219655627)
          ·
            refine ⟨537318254688715531829483441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358212169792477021219655627 537318254688715531829483441)
            ·
              refine ⟨402988691016536648872112581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537318254688715531829483441 402988691016536648872112581)
              ·
                refine ⟨75560379565600621663521109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402988691016536648872112581 75560379565600621663521109)
                ·
                  refine ⟨221368299508595571279847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75560379565600621663521109 221368299508595571279847)
                  ·
                    rfl

theorem cell23_3880019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 10].length) (baseStart_3880019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880019 prefixEnd_3880019 := by exact prefixLift 3880019
  have htrace : WordTrace (prefixWord ++ tailWord_3880019) baseStart_3880019 baseEnd_3880019 := by
    simpa [prefixWord, tailWord_3880019, baseEnd_3880019] using wordTrace_append hprefix tailTrace_3880019
  have hstable : (prefixWord ++ tailWord_3880019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880019).length < 2 ^ (prefixWord ++ tailWord_3880019).sum := by decide
  have hdescent : baseEnd_3880019 < baseStart_3880019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880057 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_3880057 : Nat := 118140960795 + 3880057 * 2 ^ 59
def prefixEnd_3880057 : Nat := 4983230072969 + 3 ^ 40 * 3880057 * 2
def baseEnd_3880057 : Nat := 664111402614076997614483

theorem tailTrace_3880057 : CollatzResearch.WordTrace tailWord_3880057 prefixEnd_3880057 664111402614076997614483 := by
  unfold tailWord_3880057
  simp only [CollatzResearch.WordTrace]
  refine ⟨141517304904223624823574425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94344869936149083215716283 141517304904223624823574425)
  ·
    refine ⟨106137978678167718617680819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141517304904223624823574425 106137978678167718617680819)
    ·
      refine ⟨159206968017251577926521229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106137978678167718617680819 159206968017251577926521229)
      ·
        refine ⟨59702613006469341722445461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159206968017251577926521229 59702613006469341722445461)
        ·
          refine ⟨2798559984678250393239631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59702613006469341722445461 2798559984678250393239631)
          ·
            refine ⟨4197839977017375589859447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798559984678250393239631 4197839977017375589859447)
            ·
              refine ⟨6296759965526063384789171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197839977017375589859447 6296759965526063384789171)
              ·
                refine ⟨9445139948289095077183757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6296759965526063384789171 9445139948289095077183757)
                ·
                  refine ⟨3541927480608410653943909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9445139948289095077183757 3541927480608410653943909)
                  ·
                    refine ⟨664111402614076997614483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541927480608410653943909 664111402614076997614483)
                    ·
                      rfl

theorem cell23_3880057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_3880057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880057 prefixEnd_3880057 := by exact prefixLift 3880057
  have htrace : WordTrace (prefixWord ++ tailWord_3880057) baseStart_3880057 baseEnd_3880057 := by
    simpa [prefixWord, tailWord_3880057, baseEnd_3880057] using wordTrace_append hprefix tailTrace_3880057
  have hstable : (prefixWord ++ tailWord_3880057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880057).length < 2 ^ (prefixWord ++ tailWord_3880057).sum := by decide
  have hdescent : baseEnd_3880057 < baseStart_3880057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880083 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 1, 5]
def baseStart_3880083 : Nat := 118140960795 + 3880083 * 2 ^ 59
def prefixEnd_3880083 : Nat := 4983230072969 + 3 ^ 40 * 3880083 * 2
def baseEnd_3880083 : Nat := 664115852779749297039443

theorem tailTrace_3880083 : CollatzResearch.WordTrace tailWord_3880083 prefixEnd_3880083 664115852779749297039443 := by
  unfold tailWord_3880083
  simp only [CollatzResearch.WordTrace]
  refine ⟨141518253202129431264020903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94345502134752954176013935 141518253202129431264020903)
  ·
    refine ⟨212277379803194146896031355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141518253202129431264020903 212277379803194146896031355)
    ·
      refine ⟨318416069704791220344047033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212277379803194146896031355 318416069704791220344047033)
      ·
        refine ⟨238812052278593415258035275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318416069704791220344047033 238812052278593415258035275)
        ·
          refine ⟨358218078417890122887052913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238812052278593415258035275 358218078417890122887052913)
          ·
            refine ⟨268663558813417592165289685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358218078417890122887052913 268663558813417592165289685)
            ·
              refine ⟨6296802159689474816373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268663558813417592165289685 6296802159689474816373977)
              ·
                refine ⟨4722601619767106112280483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296802159689474816373977 4722601619767106112280483)
                ·
                  refine ⟨7083902429650659168420725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722601619767106112280483 7083902429650659168420725)
                  ·
                    refine ⟨664115852779749297039443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7083902429650659168420725 664115852779749297039443)
                    ·
                      rfl

theorem cell23_3880083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 5].length) (baseStart_3880083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880083 prefixEnd_3880083 := by exact prefixLift 3880083
  have htrace : WordTrace (prefixWord ++ tailWord_3880083) baseStart_3880083 baseEnd_3880083 := by
    simpa [prefixWord, tailWord_3880083, baseEnd_3880083] using wordTrace_append hprefix tailTrace_3880083
  have hstable : (prefixWord ++ tailWord_3880083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880083).length < 2 ^ (prefixWord ++ tailWord_3880083).sum := by decide
  have hdescent : baseEnd_3880083 < baseStart_3880083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880097 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3880097 : Nat := 118140960795 + 3880097 * 2 ^ 59
def prefixEnd_3880097 : Nat := 4983230072969 + 3 ^ 40 * 3880097 * 2
def baseEnd_3880097 : Nat := 1992354747068410836343265

theorem tailTrace_3880097 : CollatzResearch.WordTrace tailWord_3880097 prefixEnd_3880097 1992354747068410836343265 := by
  unfold tailWord_3880097
  simp only [CollatzResearch.WordTrace]
  refine ⟨141518763824078711655030545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94345842549385807770020363 141518763824078711655030545)
  ·
    refine ⟨106139072868059033741272909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141518763824078711655030545 106139072868059033741272909)
    ·
      refine ⟨39802152325522137652977341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106139072868059033741272909 39802152325522137652977341)
      ·
        refine ⟨14925807122070801619866503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39802152325522137652977341 14925807122070801619866503)
        ·
          refine ⟨22388710683106202429799755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925807122070801619866503 22388710683106202429799755)
          ·
            refine ⟨33583066024659303644699633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388710683106202429799755 33583066024659303644699633)
            ·
              refine ⟨25187299518494477733524725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33583066024659303644699633 25187299518494477733524725)
              ·
                refine ⟨2361309329858857287517943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25187299518494477733524725 2361309329858857287517943)
                ·
                  refine ⟨3541963994788285931276915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361309329858857287517943 3541963994788285931276915)
                  ·
                    refine ⟨5312945992182428896915373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541963994788285931276915 5312945992182428896915373)
                    ·
                      refine ⟨1992354747068410836343265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312945992182428896915373 1992354747068410836343265)
                      ·
                        rfl

theorem cell23_3880097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3880097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880097 prefixEnd_3880097 := by exact prefixLift 3880097
  have htrace : WordTrace (prefixWord ++ tailWord_3880097) baseStart_3880097 baseEnd_3880097 := by
    simpa [prefixWord, tailWord_3880097, baseEnd_3880097] using wordTrace_append hprefix tailTrace_3880097
  have hstable : (prefixWord ++ tailWord_3880097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880097).length < 2 ^ (prefixWord ++ tailWord_3880097).sum := by decide
  have hdescent : baseEnd_3880097 < baseStart_3880097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880114 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_3880114 : Nat := 118140960795 + 3880114 * 2 ^ 59
def prefixEnd_3880114 : Nat := 4983230072969 + 3 ^ 40 * 3880114 * 2
def baseEnd_3880114 : Nat := 1992363476239537269830687

theorem tailTrace_3880114 : CollatzResearch.WordTrace tailWord_3880114 prefixEnd_3880114 1992363476239537269830687 := by
  unfold tailWord_3880114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35379845966254280889599849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94346255910011415705599597 35379845966254280889599849)
  ·
    refine ⟨26534884474690710667199887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35379845966254280889599849 26534884474690710667199887)
    ·
      refine ⟨39802326712036066000799831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26534884474690710667199887 39802326712036066000799831)
      ·
        refine ⟨59703490068054099001199747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39802326712036066000799831 59703490068054099001199747)
        ·
          refine ⟨89555235102081148501799621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59703490068054099001199747 89555235102081148501799621)
          ·
            refine ⟨16791606581640215344087429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89555235102081148501799621 16791606581640215344087429)
            ·
              refine ⟨3148426234057540377016393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16791606581640215344087429 3148426234057540377016393)
              ·
                refine ⟨2361319675543155282762295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148426234057540377016393 2361319675543155282762295)
                ·
                  refine ⟨3541979513314732924143443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361319675543155282762295 3541979513314732924143443)
                  ·
                    refine ⟨5312969269972099386215165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541979513314732924143443 5312969269972099386215165)
                    ·
                      refine ⟨1992363476239537269830687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5312969269972099386215165 1992363476239537269830687)
                      ·
                        rfl

theorem cell23_3880114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_3880114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880114 prefixEnd_3880114 := by exact prefixLift 3880114
  have htrace : WordTrace (prefixWord ++ tailWord_3880114) baseStart_3880114 baseEnd_3880114 := by
    simpa [prefixWord, tailWord_3880114, baseEnd_3880114] using wordTrace_append hprefix tailTrace_3880114
  have hstable : (prefixWord ++ tailWord_3880114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880114).length < 2 ^ (prefixWord ++ tailWord_3880114).sum := by decide
  have hdescent : baseEnd_3880114 < baseStart_3880114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880194 : List Nat := [3, 4, 1, 1, 4, 1, 2, 7]
def baseStart_3880194 : Nat := 118140960795 + 3880194 * 2 ^ 59
def prefixEnd_3880194 : Nat := 4983230072969 + 3 ^ 40 * 3880194 * 2
def baseEnd_3880194 : Nat := 73792761284885072475197

theorem tailTrace_3880194 : CollatzResearch.WordTrace tailWord_3880194 prefixEnd_3880194 73792761284885072475197 := by
  unfold tailWord_3880194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35380575426181824305327909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94348201136484864814207757 35380575426181824305327909)
  ·
    refine ⟨6633857892409092057248983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35380575426181824305327909 6633857892409092057248983)
    ·
      refine ⟨9950786838613638085873475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633857892409092057248983 9950786838613638085873475)
      ·
        refine ⟨14926180257920457128810213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950786838613638085873475 14926180257920457128810213)
        ·
          refine ⟨2798658798360085711651915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14926180257920457128810213 2798658798360085711651915)
          ·
            refine ⟨4197988197540128567477873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798658798360085711651915 4197988197540128567477873)
            ·
              refine ⟨3148491148155096425608405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197988197540128567477873 3148491148155096425608405)
              ·
                refine ⟨73792761284885072475197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3148491148155096425608405 73792761284885072475197)
                ·
                  rfl

theorem cell23_3880194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_3880194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880194 prefixEnd_3880194 := by exact prefixLift 3880194
  have htrace : WordTrace (prefixWord ++ tailWord_3880194) baseStart_3880194 baseEnd_3880194 := by
    simpa [prefixWord, tailWord_3880194, baseEnd_3880194] using wordTrace_append hprefix tailTrace_3880194
  have hstable : (prefixWord ++ tailWord_3880194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880194).length < 2 ^ (prefixWord ++ tailWord_3880194).sum := by decide
  have hdescent : baseEnd_3880194 < baseStart_3880194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880197 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_3880197 : Nat := 118140960795 + 3880197 * 2 ^ 59
def prefixEnd_3880197 : Nat := 4983230072969 + 3 ^ 40 * 3880197 * 2
def baseEnd_3880197 : Nat := 1992406095133860445092805

theorem tailTrace_3880197 : CollatzResearch.WordTrace tailWord_3880197 prefixEnd_3880197 1992406095133860445092805 := by
  unfold tailWord_3880197
  simp only [CollatzResearch.WordTrace]
  refine ⟨141522411123716428733670845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94348274082477619155780563 141522411123716428733670845)
  ·
    refine ⟨53070904171393660775126567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141522411123716428733670845 53070904171393660775126567)
    ·
      refine ⟨79606356257090491162689851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53070904171393660775126567 79606356257090491162689851)
      ·
        refine ⟨119409534385635736744034777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79606356257090491162689851 119409534385635736744034777)
        ·
          refine ⟨89557150789226802558026083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119409534385635736744034777 89557150789226802558026083)
          ·
            refine ⟨134335726183840203837039125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89557150789226802558026083 134335726183840203837039125)
            ·
              refine ⟨6296987164867509554861209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134335726183840203837039125 6296987164867509554861209)
              ·
                refine ⟨4722740373650632166145907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296987164867509554861209 4722740373650632166145907)
                ·
                  refine ⟨7084110560475948249218861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722740373650632166145907 7084110560475948249218861)
                  ·
                    refine ⟨2656541460178480593457073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7084110560475948249218861 2656541460178480593457073)
                    ·
                      refine ⟨1992406095133860445092805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656541460178480593457073 1992406095133860445092805)
                      ·
                        rfl

theorem cell23_3880197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_3880197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880197 prefixEnd_3880197 := by exact prefixLift 3880197
  have htrace : WordTrace (prefixWord ++ tailWord_3880197) baseStart_3880197 baseEnd_3880197 := by
    simpa [prefixWord, tailWord_3880197, baseEnd_3880197] using wordTrace_append hprefix tailTrace_3880197
  have hstable : (prefixWord ++ tailWord_3880197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880197).length < 2 ^ (prefixWord ++ tailWord_3880197).sum := by decide
  have hdescent : baseEnd_3880197 < baseStart_3880197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880213 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3880213 : Nat := 118140960795 + 3880213 * 2 ^ 59
def prefixEnd_3880213 : Nat := 4983230072969 + 3 ^ 40 * 3880213 * 2
def baseEnd_3880213 : Nat := 1992414310824332382492731

theorem tailTrace_3880213 : CollatzResearch.WordTrace tailWord_3880213 prefixEnd_3880213 1992414310824332382492731 := by
  unfold tailWord_3880213
  simp only [CollatzResearch.WordTrace]
  refine ⟨141522994691658463466253293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94348663127772308977502195 141522994691658463466253293)
  ·
    refine ⟨53071123009371923799844985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141522994691658463466253293 53071123009371923799844985)
    ·
      refine ⟨39803342257028942849883739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53071123009371923799844985 39803342257028942849883739)
      ·
        refine ⟨59705013385543414274825609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39803342257028942849883739 59705013385543414274825609)
        ·
          refine ⟨44778760039157560706119207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59705013385543414274825609 44778760039157560706119207)
          ·
            refine ⟨67168140058736341059178811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44778760039157560706119207 67168140058736341059178811)
            ·
              refine ⟨100752210088104511588768217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67168140058736341059178811 100752210088104511588768217)
              ·
                refine ⟨75564157566078383691576163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100752210088104511588768217 75564157566078383691576163)
                ·
                  refine ⟨113346236349117575537364245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75564157566078383691576163 113346236349117575537364245)
                  ·
                    refine ⟨5313104828864886353313949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113346236349117575537364245 5313104828864886353313949)
                    ·
                      refine ⟨1992414310824332382492731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313104828864886353313949 1992414310824332382492731)
                      ·
                        rfl

theorem cell23_3880213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3880213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880213 prefixEnd_3880213 := by exact prefixLift 3880213
  have htrace : WordTrace (prefixWord ++ tailWord_3880213) baseStart_3880213 baseEnd_3880213 := by
    simpa [prefixWord, tailWord_3880213, baseEnd_3880213] using wordTrace_append hprefix tailTrace_3880213
  have hstable : (prefixWord ++ tailWord_3880213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880213).length < 2 ^ (prefixWord ++ tailWord_3880213).sum := by decide
  have hdescent : baseEnd_3880213 < baseStart_3880213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880227 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 4, 2, 2]
def baseStart_3880227 : Nat := 118140960795 + 3880227 * 2 ^ 59
def prefixEnd_3880227 : Nat := 4983230072969 + 3 ^ 40 * 3880227 * 2
def baseEnd_3880227 : Nat := 1992421499553495327717667

theorem tailTrace_3880227 : CollatzResearch.WordTrace tailWord_3880227 prefixEnd_3880227 1992421499553495327717667 := by
  unfold tailWord_3880227
  simp only [CollatzResearch.WordTrace]
  refine ⟨141523505313607743857262935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94349003542405162571508623 141523505313607743857262935)
  ·
    refine ⟨212285257970411615785894403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141523505313607743857262935 212285257970411615785894403)
    ·
      refine ⟨318427886955617423678841605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212285257970411615785894403 318427886955617423678841605)
      ·
        refine ⟨59705228804178266939782801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318427886955617423678841605 59705228804178266939782801)
        ·
          refine ⟨44778921603133700204837101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59705228804178266939782801 44778921603133700204837101)
          ·
            refine ⟨16792095601175137576813913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44778921603133700204837101 16792095601175137576813913)
            ·
              refine ⟨12594071700881353182610435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792095601175137576813913 12594071700881353182610435)
              ·
                refine ⟨18891107551322029773915653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594071700881353182610435 18891107551322029773915653)
                ·
                  refine ⟨3542082665872880582609185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18891107551322029773915653 3542082665872880582609185)
                  ·
                    refine ⟨2656561999404660436956889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542082665872880582609185 2656561999404660436956889)
                    ·
                      refine ⟨1992421499553495327717667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656561999404660436956889 1992421499553495327717667)
                      ·
                        rfl

theorem cell23_3880227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_3880227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880227 prefixEnd_3880227 := by exact prefixLift 3880227
  have htrace : WordTrace (prefixWord ++ tailWord_3880227) baseStart_3880227 baseEnd_3880227 := by
    simpa [prefixWord, tailWord_3880227, baseEnd_3880227] using wordTrace_append hprefix tailTrace_3880227
  have hstable : (prefixWord ++ tailWord_3880227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880227).length < 2 ^ (prefixWord ++ tailWord_3880227).sum := by decide
  have hdescent : baseEnd_3880227 < baseStart_3880227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880273 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_3880273 : Nat := 118140960795 + 3880273 * 2 ^ 59
def prefixEnd_3880273 : Nat := 4983230072969 + 3 ^ 40 * 3880273 * 2
def baseEnd_3880273 : Nat := 1992445119663602147742455

theorem tailTrace_3880273 : CollatzResearch.WordTrace tailWord_3880273 prefixEnd_3880273 1992445119663602147742455 := by
  unfold tailWord_3880273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141525183071441093713437473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94350122047627395808958315 141525183071441093713437473)
  ·
    refine ⟨106143887303580820285078105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141525183071441093713437473 106143887303580820285078105)
    ·
      refine ⟨79607915477685615213808579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106143887303580820285078105 79607915477685615213808579)
      ·
        refine ⟨119411873216528422820712869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79607915477685615213808579 119411873216528422820712869)
        ·
          refine ⟨22389726228099079278883663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119411873216528422820712869 22389726228099079278883663)
          ·
            refine ⟨33584589342148618918325495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22389726228099079278883663 33584589342148618918325495)
            ·
              refine ⟨50376884013222928377488243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33584589342148618918325495 50376884013222928377488243)
              ·
                refine ⟨75565326019834392566232365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50376884013222928377488243 75565326019834392566232365)
                ·
                  refine ⟨28336997257437897212337137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75565326019834392566232365 28336997257437897212337137)
                  ·
                    refine ⟨21252747943078422909252853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28336997257437897212337137 21252747943078422909252853)
                    ·
                      refine ⟨1992445119663602147742455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21252747943078422909252853 1992445119663602147742455)
                      ·
                        rfl

theorem cell23_3880273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_3880273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880273 prefixEnd_3880273 := by exact prefixLift 3880273
  have htrace : WordTrace (prefixWord ++ tailWord_3880273) baseStart_3880273 baseEnd_3880273 := by
    simpa [prefixWord, tailWord_3880273, baseEnd_3880273] using wordTrace_append hprefix tailTrace_3880273
  have hstable : (prefixWord ++ tailWord_3880273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880273).length < 2 ^ (prefixWord ++ tailWord_3880273).sum := by decide
  have hdescent : baseEnd_3880273 < baseStart_3880273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880290 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3880290 : Nat := 118140960795 + 3880290 * 2 ^ 59
def prefixEnd_3880290 : Nat := 4983230072969 + 3 ^ 40 * 3880290 * 2
def baseEnd_3880290 : Nat := 1992453848834728581229877

theorem tailTrace_3880290 : CollatzResearch.WordTrace tailWord_3880290 prefixEnd_3880290 1992453848834728581229877 := by
  unfold tailWord_3880290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381450778094876404201581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94350535408253003744537549 35381450778094876404201581)
  ·
    refine ⟨13268044041785578651575593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35381450778094876404201581 13268044041785578651575593)
    ·
      refine ⟨9951033031339183988681695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13268044041785578651575593 9951033031339183988681695)
      ·
        refine ⟨14926549547008775983022543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951033031339183988681695 14926549547008775983022543)
        ·
          refine ⟨22389824320513163974533815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926549547008775983022543 22389824320513163974533815)
          ·
            refine ⟨33584736480769745961800723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22389824320513163974533815 33584736480769745961800723)
            ·
              refine ⟨50377104721154618942701085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33584736480769745961800723 50377104721154618942701085)
              ·
                refine ⟨18891414270432982103512907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50377104721154618942701085 18891414270432982103512907)
                ·
                  refine ⟨28337121405649473155269361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18891414270432982103512907 28337121405649473155269361)
                  ·
                    refine ⟨21252841054237104866452021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28337121405649473155269361 21252841054237104866452021)
                    ·
                      refine ⟨1992453848834728581229877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21252841054237104866452021 1992453848834728581229877)
                      ·
                        rfl

theorem cell23_3880290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3880290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880290 prefixEnd_3880290 := by exact prefixLift 3880290
  have htrace : WordTrace (prefixWord ++ tailWord_3880290) baseStart_3880290 baseEnd_3880290 := by
    simpa [prefixWord, tailWord_3880290, baseEnd_3880290] using wordTrace_append hprefix tailTrace_3880290
  have hstable : (prefixWord ++ tailWord_3880290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880290).length < 2 ^ (prefixWord ++ tailWord_3880290).sum := by decide
  have hdescent : baseEnd_3880290 < baseStart_3880290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880344 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_3880344 : Nat := 118140960795 + 3880344 * 2 ^ 59
def prefixEnd_3880344 : Nat := 4983230072969 + 3 ^ 40 * 3880344 * 2
def baseEnd_3880344 : Nat := 664160525596690456651543

theorem tailTrace_3880344 : CollatzResearch.WordTrace tailWord_3880344 prefixEnd_3880344 664160525596690456651543 := by
  unfold tailWord_3880344
  simp only [CollatzResearch.WordTrace]
  refine ⟨70763886327091936419636043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94351848436122581892848057 70763886327091936419636043)
  ·
    refine ⟨106145829490637904629454065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70763886327091936419636043 106145829490637904629454065)
    ·
      refine ⟨79609372117978428472090549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106145829490637904629454065 79609372117978428472090549)
      ·
        refine ⟨7463378636060477669258489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79609372117978428472090549 7463378636060477669258489)
        ·
          refine ⟨5597533977045358251943867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7463378636060477669258489 5597533977045358251943867)
          ·
            refine ⟨8396300965568037377915801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597533977045358251943867 8396300965568037377915801)
            ·
              refine ⟨6297225724176028033436851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8396300965568037377915801 6297225724176028033436851)
              ·
                refine ⟨9445838586264042050155277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297225724176028033436851 9445838586264042050155277)
                ·
                  refine ⟨3542189469849015768808229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9445838586264042050155277 3542189469849015768808229)
                  ·
                    refine ⟨664160525596690456651543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3542189469849015768808229 664160525596690456651543)
                    ·
                      rfl

theorem cell23_3880344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_3880344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880344 prefixEnd_3880344 := by exact prefixLift 3880344
  have htrace : WordTrace (prefixWord ++ tailWord_3880344) baseStart_3880344 baseEnd_3880344 := by
    simpa [prefixWord, tailWord_3880344, baseEnd_3880344] using wordTrace_append hprefix tailTrace_3880344
  have hstable : (prefixWord ++ tailWord_3880344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880344).length < 2 ^ (prefixWord ++ tailWord_3880344).sum := by decide
  have hdescent : baseEnd_3880344 < baseStart_3880344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_3880363 : Nat := 118140960795 + 3880363 * 2 ^ 59
def prefixEnd_3880363 : Nat := 4983230072969 + 3 ^ 40 * 3880363 * 2
def baseEnd_3880363 : Nat := 1992491332922506795617041

theorem tailTrace_3880363 : CollatzResearch.WordTrace tailWord_3880363 prefixEnd_3880363 1992491332922506795617041 := by
  unfold tailWord_3880363
  simp only [CollatzResearch.WordTrace]
  refine ⟨141528465641115039084213743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94352310427410026056142495 141528465641115039084213743)
  ·
    refine ⟨212292698461672558626320615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141528465641115039084213743 212292698461672558626320615)
    ·
      refine ⟨318439047692508837939480923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212292698461672558626320615 318439047692508837939480923)
      ·
        refine ⟨477658571538763256909221385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318439047692508837939480923 477658571538763256909221385)
        ·
          refine ⟨358243928654072442681916039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477658571538763256909221385 358243928654072442681916039)
          ·
            refine ⟨537365892981108664022874059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358243928654072442681916039 537365892981108664022874059)
            ·
              refine ⟨806048839471662996034311089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537365892981108664022874059 806048839471662996034311089)
              ·
                refine ⟨604536629603747247025733317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806048839471662996034311089 604536629603747247025733317)
                ·
                  refine ⟨113350618050702608817324997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604536629603747247025733317 113350618050702608817324997)
                  ·
                    refine ⟨21253240884506739153248437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113350618050702608817324997 21253240884506739153248437)
                    ·
                      refine ⟨1992491332922506795617041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21253240884506739153248437 1992491332922506795617041)
                      ·
                        rfl

theorem cell23_3880363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_3880363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880363 prefixEnd_3880363 := by exact prefixLift 3880363
  have htrace : WordTrace (prefixWord ++ tailWord_3880363) baseStart_3880363 baseEnd_3880363 := by
    simpa [prefixWord, tailWord_3880363, baseEnd_3880363] using wordTrace_append hprefix tailTrace_3880363
  have hstable : (prefixWord ++ tailWord_3880363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880363).length < 2 ^ (prefixWord ++ tailWord_3880363).sum := by decide
  have hdescent : baseEnd_3880363 < baseStart_3880363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880394 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_3880394 : Nat := 118140960795 + 3880394 * 2 ^ 59
def prefixEnd_3880394 : Nat := 4983230072969 + 3 ^ 40 * 3880394 * 2
def baseEnd_3880394 : Nat := 1992507250822796174329399

theorem tailTrace_3880394 : CollatzResearch.WordTrace tailWord_3880394 prefixEnd_3880394 1992507250822796174329399 := by
  unfold tailWord_3880394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382399076000682844648059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94353064202668487585728157 35382399076000682844648059)
  ·
    refine ⟨53073598614001024266972089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35382399076000682844648059 53073598614001024266972089)
    ·
      refine ⟨39805198960500768200229067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53073598614001024266972089 39805198960500768200229067)
      ·
        refine ⟨59707798440751152300343601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39805198960500768200229067 59707798440751152300343601)
        ·
          refine ⟨44780848830563364225257701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59707798440751152300343601 44780848830563364225257701)
          ·
            refine ⟨8396409155730630792235819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44780848830563364225257701 8396409155730630792235819)
            ·
              refine ⟨12594613733595946188353729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396409155730630792235819 12594613733595946188353729)
              ·
                refine ⟨9445960300196959641265297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12594613733595946188353729 9445960300196959641265297)
                ·
                  refine ⟨7084470225147719730948973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9445960300196959641265297 7084470225147719730948973)
                  ·
                    refine ⟨2656676334430394899105865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7084470225147719730948973 2656676334430394899105865)
                    ·
                      refine ⟨1992507250822796174329399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656676334430394899105865 1992507250822796174329399)
                      ·
                        rfl

theorem cell23_3880394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_3880394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880394 prefixEnd_3880394 := by exact prefixLift 3880394
  have htrace : WordTrace (prefixWord ++ tailWord_3880394) baseStart_3880394 baseEnd_3880394 := by
    simpa [prefixWord, tailWord_3880394, baseEnd_3880394] using wordTrace_append hprefix tailTrace_3880394
  have hstable : (prefixWord ++ tailWord_3880394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880394).length < 2 ^ (prefixWord ++ tailWord_3880394).sum := by decide
  have hdescent : baseEnd_3880394 < baseStart_3880394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880420 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3880420 : Nat := 118140960795 + 3880420 * 2 ^ 59
def prefixEnd_3880420 : Nat := 4983230072969 + 3 ^ 40 * 3880420 * 2
def baseEnd_3880420 : Nat := 1992520601319813072604279

theorem tailTrace_3880420 : CollatzResearch.WordTrace tailWord_3880420 prefixEnd_3880420 1992520601319813072604279 := by
  unfold tailWord_3880420
  simp only [CollatzResearch.WordTrace]
  refine ⟨70765272300954268909519357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94353696401272358546025809 70765272300954268909519357)
  ·
    refine ⟨26536977112857850841069759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70765272300954268909519357 26536977112857850841069759)
    ·
      refine ⟨39805465669286776261604639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26536977112857850841069759 39805465669286776261604639)
      ·
        refine ⟨59708198503930164392406959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39805465669286776261604639 59708198503930164392406959)
        ·
          refine ⟨89562297755895246588610439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59708198503930164392406959 89562297755895246588610439)
          ·
            refine ⟨134343446633842869882915659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89562297755895246588610439 134343446633842869882915659)
            ·
              refine ⟨201515169950764304824373489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134343446633842869882915659 201515169950764304824373489)
              ·
                refine ⟨151136377463073228618280117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201515169950764304824373489 151136377463073228618280117)
                ·
                  refine ⟨14169035387163115182963761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151136377463073228618280117 14169035387163115182963761)
                  ·
                    refine ⟨10626776540372336387222821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14169035387163115182963761 10626776540372336387222821)
                    ·
                      refine ⟨1992520601319813072604279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10626776540372336387222821 1992520601319813072604279)
                      ·
                        rfl

theorem cell23_3880420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3880420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880420 prefixEnd_3880420 := by exact prefixLift 3880420
  have htrace : WordTrace (prefixWord ++ tailWord_3880420) baseStart_3880420 baseEnd_3880420 := by
    simpa [prefixWord, tailWord_3880420, baseEnd_3880420] using wordTrace_append hprefix tailTrace_3880420
  have hstable : (prefixWord ++ tailWord_3880420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880420).length < 2 ^ (prefixWord ++ tailWord_3880420).sum := by decide
  have hdescent : baseEnd_3880420 < baseStart_3880420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880424 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3880424 : Nat := 118140960795 + 3880424 * 2 ^ 59
def prefixEnd_3880424 : Nat := 4983230072969 + 3 ^ 40 * 3880424 * 2
def baseEnd_3880424 : Nat := 1992522655242431056954261

theorem tailTrace_3880424 : CollatzResearch.WordTrace tailWord_3880424 prefixEnd_3880424 1992522655242431056954261 := by
  unfold tailWord_3880424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70765345246947023251092163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94353793662596031001456217 70765345246947023251092163)
  ·
    refine ⟨106148017870420534876638245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70765345246947023251092163 106148017870420534876638245)
    ·
      refine ⟨19902753350703850289369671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106148017870420534876638245 19902753350703850289369671)
      ·
        refine ⟨29854130026055775434054507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19902753350703850289369671 29854130026055775434054507)
        ·
          refine ⟨44781195039083663151081761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29854130026055775434054507 44781195039083663151081761)
          ·
            refine ⟨33585896279312747363311321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44781195039083663151081761 33585896279312747363311321)
            ·
              refine ⟨25189422209484560522483491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33585896279312747363311321 25189422209484560522483491)
              ·
                refine ⟨37784133314226840783725237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25189422209484560522483491 37784133314226840783725237)
                ·
                  refine ⟨3542262498208766323474241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37784133314226840783725237 3542262498208766323474241)
                  ·
                    refine ⟨2656696873656574742605681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542262498208766323474241 2656696873656574742605681)
                    ·
                      refine ⟨1992522655242431056954261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656696873656574742605681 1992522655242431056954261)
                      ·
                        rfl

theorem cell23_3880424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3880424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880424 prefixEnd_3880424 := by exact prefixLift 3880424
  have htrace : WordTrace (prefixWord ++ tailWord_3880424) baseStart_3880424 baseEnd_3880424 := by
    simpa [prefixWord, tailWord_3880424, baseEnd_3880424] using wordTrace_append hprefix tailTrace_3880424
  have hstable : (prefixWord ++ tailWord_3880424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880424).length < 2 ^ (prefixWord ++ tailWord_3880424).sum := by decide
  have hdescent : baseEnd_3880424 < baseStart_3880424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880427 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 3]
def baseStart_3880427 : Nat := 118140960795 + 3880427 * 2 ^ 59
def prefixEnd_3880427 : Nat := 4983230072969 + 3 ^ 40 * 3880427 * 2
def baseEnd_3880427 : Nat := 1992524195684394545216747

theorem tailTrace_3880427 : CollatzResearch.WordTrace tailWord_3880427 prefixEnd_3880427 1992524195684394545216747 := by
  unfold tailWord_3880427
  simp only [CollatzResearch.WordTrace]
  refine ⟨141530799912883178014543535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94353866608588785343029023 141530799912883178014543535)
  ·
    refine ⟨212296199869324767021815303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141530799912883178014543535 212296199869324767021815303)
    ·
      refine ⟨318444299803987150532722955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212296199869324767021815303 318444299803987150532722955)
      ·
        refine ⟨477666449705980725799084433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318444299803987150532722955 477666449705980725799084433)
        ·
          refine ⟨358249837279485544349313325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477666449705980725799084433 358249837279485544349313325)
          ·
            refine ⟨134343688979807079130992497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358249837279485544349313325 134343688979807079130992497)
            ·
              refine ⟨100757766734855309348244373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134343688979807079130992497 100757766734855309348244373)
              ·
                refine ⟨4723020315696342625698955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100757766734855309348244373 4723020315696342625698955)
                ·
                  refine ⟨7084530473544513938548433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723020315696342625698955 7084530473544513938548433)
                  ·
                    refine ⟨5313397855158385453911325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084530473544513938548433 5313397855158385453911325)
                    ·
                      refine ⟨1992524195684394545216747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313397855158385453911325 1992524195684394545216747)
                      ·
                        rfl

theorem cell23_3880427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 3].length) (baseStart_3880427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880427 prefixEnd_3880427 := by exact prefixLift 3880427
  have htrace : WordTrace (prefixWord ++ tailWord_3880427) baseStart_3880427 baseEnd_3880427 := by
    simpa [prefixWord, tailWord_3880427, baseEnd_3880427] using wordTrace_append hprefix tailTrace_3880427
  have hstable : (prefixWord ++ tailWord_3880427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880427).length < 2 ^ (prefixWord ++ tailWord_3880427).sum := by decide
  have hdescent : baseEnd_3880427 < baseStart_3880427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880430 : List Nat := [4, 1, 2, 1, 2, 1, 1, 11]
def baseStart_3880430 : Nat := 118140960795 + 3880430 * 2 ^ 59
def prefixEnd_3880430 : Nat := 4983230072969 + 3 ^ 40 * 3880430 * 2
def baseEnd_3880430 : Nat := 73797249486161408647379

theorem tailTrace_3880430 : CollatzResearch.WordTrace tailWord_3880430 prefixEnd_3880430 73797249486161408647379 := by
  unfold tailWord_3880430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691363666484038690862843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94353939554581539684601829 17691363666484038690862843)
  ·
    refine ⟨26537045499726058036294265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17691363666484038690862843 26537045499726058036294265)
    ·
      refine ⟨19902784124794543527220699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26537045499726058036294265 19902784124794543527220699)
      ·
        refine ⟨29854176187191815290831049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19902784124794543527220699 29854176187191815290831049)
        ·
          refine ⟨22390632140393861468123287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29854176187191815290831049 22390632140393861468123287)
          ·
            refine ⟨33585948210590792202184931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22390632140393861468123287 33585948210590792202184931)
            ·
              refine ⟨50378922315886188303277397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33585948210590792202184931 50378922315886188303277397)
              ·
                refine ⟨73797249486161408647379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50378922315886188303277397 73797249486161408647379)
                ·
                  rfl

theorem cell23_3880430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_3880430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880430 prefixEnd_3880430 := by exact prefixLift 3880430
  have htrace : WordTrace (prefixWord ++ tailWord_3880430) baseStart_3880430 baseEnd_3880430 := by
    simpa [prefixWord, tailWord_3880430, baseEnd_3880430] using wordTrace_append hprefix tailTrace_3880430
  have hstable : (prefixWord ++ tailWord_3880430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880430).length < 2 ^ (prefixWord ++ tailWord_3880430).sum := by decide
  have hdescent : baseEnd_3880430 < baseStart_3880430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880441 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 1, 2, 2]
def baseStart_3880441 : Nat := 118140960795 + 3880441 * 2 ^ 59
def prefixEnd_3880441 : Nat := 4983230072969 + 3 ^ 40 * 3880441 * 2
def baseEnd_3880441 : Nat := 1992531384413557490441683

theorem tailTrace_3880441 : CollatzResearch.WordTrace tailWord_3880441 prefixEnd_3880441 1992531384413557490441683 := by
  unfold tailWord_3880441
  simp only [CollatzResearch.WordTrace]
  refine ⟨141531310534832458405553177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94354207023221638937035451 141531310534832458405553177)
  ·
    refine ⟨106148482901124343804164883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141531310534832458405553177 106148482901124343804164883)
    ·
      refine ⟨159222724351686515706247325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106148482901124343804164883 159222724351686515706247325)
      ·
        refine ⟨59708521631882443389842747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159222724351686515706247325 59708521631882443389842747)
        ·
          refine ⟨89562782447823665084764121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59708521631882443389842747 89562782447823665084764121)
          ·
            refine ⟨67172086835867748813573091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89562782447823665084764121 67172086835867748813573091)
            ·
              refine ⟨100758130253801623220359637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67172086835867748813573091 100758130253801623220359637)
              ·
                refine ⟨2361518677823475544227179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100758130253801623220359637 2361518677823475544227179)
                ·
                  refine ⟨3542278016735213316340769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361518677823475544227179 3542278016735213316340769)
                  ·
                    refine ⟨2656708512551409987255577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542278016735213316340769 2656708512551409987255577)
                    ·
                      refine ⟨1992531384413557490441683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656708512551409987255577 1992531384413557490441683)
                      ·
                        rfl

theorem cell23_3880441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_3880441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880441 prefixEnd_3880441 := by exact prefixLift 3880441
  have htrace : WordTrace (prefixWord ++ tailWord_3880441) baseStart_3880441 baseEnd_3880441 := by
    simpa [prefixWord, tailWord_3880441, baseEnd_3880441] using wordTrace_append hprefix tailTrace_3880441
  have hstable : (prefixWord ++ tailWord_3880441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880441).length < 2 ^ (prefixWord ++ tailWord_3880441).sum := by decide
  have hdescent : baseEnd_3880441 < baseStart_3880441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880452 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3880452 : Nat := 118140960795 + 3880452 * 2 ^ 59
def prefixEnd_3880452 : Nat := 4983230072969 + 3 ^ 40 * 3880452 * 2
def baseEnd_3880452 : Nat := 1992537032700756947404133

theorem tailTrace_3880452 : CollatzResearch.WordTrace tailWord_3880452 prefixEnd_3880452 1992537032700756947404133 := by
  unfold tailWord_3880452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70765855868896303642101805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94354474491861738189469073 70765855868896303642101805)
  ·
    refine ⟨26537195950836113865788177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70765855868896303642101805 26537195950836113865788177)
    ·
      refine ⟨19902896963127085399341133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26537195950836113865788177 19902896963127085399341133)
      ·
        refine ⟨7463586361172657024752925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19902896963127085399341133 7463586361172657024752925)
        ·
          refine ⟨2798844885439746384282347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7463586361172657024752925 2798844885439746384282347)
          ·
            refine ⟨4198267328159619576423521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798844885439746384282347 4198267328159619576423521)
            ·
              refine ⟨3148700496119714682317641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198267328159619576423521 3148700496119714682317641)
              ·
                refine ⟨2361525372089786011738231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148700496119714682317641 2361525372089786011738231)
                ·
                  refine ⟨3542288058134679017607347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361525372089786011738231 3542288058134679017607347)
                  ·
                    refine ⟨5313432087202018526411021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542288058134679017607347 5313432087202018526411021)
                    ·
                      refine ⟨1992537032700756947404133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313432087202018526411021 1992537032700756947404133)
                      ·
                        rfl

theorem cell23_3880452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3880452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880452 prefixEnd_3880452 := by exact prefixLift 3880452
  have htrace : WordTrace (prefixWord ++ tailWord_3880452) baseStart_3880452 baseEnd_3880452 := by
    simpa [prefixWord, tailWord_3880452, baseEnd_3880452] using wordTrace_append hprefix tailTrace_3880452
  have hstable : (prefixWord ++ tailWord_3880452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880452).length < 2 ^ (prefixWord ++ tailWord_3880452).sum := by decide
  have hdescent : baseEnd_3880452 < baseStart_3880452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880458 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_3880458 : Nat := 118140960795 + 3880458 * 2 ^ 59
def prefixEnd_3880458 : Nat := 4983230072969 + 3 ^ 40 * 3880458 * 2
def baseEnd_3880458 : Nat := 1992540113584683923929105

theorem tailTrace_3880458 : CollatzResearch.WordTrace tailWord_3880458 prefixEnd_3880458 1992540113584683923929105 := by
  unfold tailWord_3880458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382982643942717577230507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94354620383847246872614685 35382982643942717577230507)
  ·
    refine ⟨53074473965914076365845761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35382982643942717577230507 53074473965914076365845761)
    ·
      refine ⟨39805855474435557274384321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53074473965914076365845761 39805855474435557274384321)
      ·
        refine ⟨29854391605826667955788241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39805855474435557274384321 29854391605826667955788241)
        ·
          refine ⟨22390793704370000966841181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29854391605826667955788241 22390793704370000966841181)
          ·
            refine ⟨8396547639138750362565443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22390793704370000966841181 8396547639138750362565443)
            ·
              refine ⟨12594821458708125543848165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396547639138750362565443 12594821458708125543848165)
              ·
                refine ⟨2361529023507773539471531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12594821458708125543848165 2361529023507773539471531)
                ·
                  refine ⟨3542293535261660309207297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361529023507773539471531 3542293535261660309207297)
                  ·
                    refine ⟨2656720151446245231905473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542293535261660309207297 2656720151446245231905473)
                    ·
                      refine ⟨1992540113584683923929105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656720151446245231905473 1992540113584683923929105)
                      ·
                        rfl

theorem cell23_3880458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_3880458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880458 prefixEnd_3880458 := by exact prefixLift 3880458
  have htrace : WordTrace (prefixWord ++ tailWord_3880458) baseStart_3880458 baseEnd_3880458 := by
    simpa [prefixWord, tailWord_3880458, baseEnd_3880458] using wordTrace_append hprefix tailTrace_3880458
  have hstable : (prefixWord ++ tailWord_3880458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880458).length < 2 ^ (prefixWord ++ tailWord_3880458).sum := by decide
  have hdescent : baseEnd_3880458 < baseStart_3880458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880501 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_3880501 : Nat := 118140960795 + 3880501 * 2 ^ 59
def prefixEnd_3880501 : Nat := 4983230072969 + 3 ^ 40 * 3880501 * 2
def baseEnd_3880501 : Nat := 1992562193252827255691407

theorem tailTrace_3880501 : CollatzResearch.WordTrace tailWord_3880501 prefixEnd_3880501 1992562193252827255691407 := by
  unfold tailWord_3880501
  simp only [CollatzResearch.WordTrace]
  refine ⟨141533498914615088652737357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94355665943076725768491571 141533498914615088652737357)
  ·
    refine ⟨53075062092980658244776509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141533498914615088652737357 53075062092980658244776509)
    ·
      refine ⟨19903148284867746841791191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53075062092980658244776509 19903148284867746841791191)
      ·
        refine ⟨29854722427301620262686787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19903148284867746841791191 29854722427301620262686787)
        ·
          refine ⟨44782083640952430394030181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29854722427301620262686787 44782083640952430394030181)
          ·
            refine ⟨8396640682678580698880659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44782083640952430394030181 8396640682678580698880659)
            ·
              refine ⟨12594961024017871048320989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396640682678580698880659 12594961024017871048320989)
              ·
                refine ⟨4723110384006701643120371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12594961024017871048320989 4723110384006701643120371)
                ·
                  refine ⟨7084665576010052464680557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723110384006701643120371 7084665576010052464680557)
                  ·
                    refine ⟨2656749591003769674255209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7084665576010052464680557 2656749591003769674255209)
                    ·
                      refine ⟨1992562193252827255691407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656749591003769674255209 1992562193252827255691407)
                      ·
                        rfl

theorem cell23_3880501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_3880501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880501 prefixEnd_3880501 := by exact prefixLift 3880501
  have htrace : WordTrace (prefixWord ++ tailWord_3880501) baseStart_3880501 baseEnd_3880501 := by
    simpa [prefixWord, tailWord_3880501, baseEnd_3880501] using wordTrace_append hprefix tailTrace_3880501
  have hstable : (prefixWord ++ tailWord_3880501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880501).length < 2 ^ (prefixWord ++ tailWord_3880501).sum := by decide
  have hdescent : baseEnd_3880501 < baseStart_3880501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880508 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3880508 : Nat := 118140960795 + 3880508 * 2 ^ 59
def prefixEnd_3880508 : Nat := 4983230072969 + 3 ^ 40 * 3880508 * 2
def baseEnd_3880508 : Nat := 1992565787617408728303875

theorem tailTrace_3880508 : CollatzResearch.WordTrace tailWord_3880508 prefixEnd_3880508 1992565787617408728303875 := by
  unfold tailWord_3880508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70766877112794864424121089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94355836150393152565494785 70766877112794864424121089)
  ·
    refine ⟨53075157834596148318090817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70766877112794864424121089 53075157834596148318090817)
    ·
      refine ⟨39806368375947111238568113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53075157834596148318090817 39806368375947111238568113)
      ·
        refine ⟨29854776281960333428926085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39806368375947111238568113 29854776281960333428926085)
        ·
          refine ⟨5597770552867562517923641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29854776281960333428926085 5597770552867562517923641)
          ·
            refine ⟨4198327914650671888442731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5597770552867562517923641 4198327914650671888442731)
            ·
              refine ⟨6297491871976007832664097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198327914650671888442731 6297491871976007832664097)
              ·
                refine ⟨4723118903982005874498073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297491871976007832664097 4723118903982005874498073)
                ·
                  refine ⟨3542339177986504405873555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723118903982005874498073 3542339177986504405873555)
                  ·
                    refine ⟨5313508766979756608810333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542339177986504405873555 5313508766979756608810333)
                    ·
                      refine ⟨1992565787617408728303875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313508766979756608810333 1992565787617408728303875)
                      ·
                        rfl

theorem cell23_3880508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3880508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880508 prefixEnd_3880508 := by exact prefixLift 3880508
  have htrace : WordTrace (prefixWord ++ tailWord_3880508) baseStart_3880508 baseEnd_3880508 := by
    simpa [prefixWord, tailWord_3880508, baseEnd_3880508] using wordTrace_append hprefix tailTrace_3880508
  have hstable : (prefixWord ++ tailWord_3880508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880508).length < 2 ^ (prefixWord ++ tailWord_3880508).sum := by decide
  have hdescent : baseEnd_3880508 < baseStart_3880508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880525 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_3880525 : Nat := 118140960795 + 3880525 * 2 ^ 59
def prefixEnd_3880525 : Nat := 4983230072969 + 3 ^ 40 * 3880525 * 2
def baseEnd_3880525 : Nat := 1992574516788535161791297

theorem tailTrace_3880525 : CollatzResearch.WordTrace tailWord_3880525 prefixEnd_3880525 1992574516788535161791297 := by
  unfold tailWord_3880525
  simp only [CollatzResearch.WordTrace]
  refine ⟨141534374266528140751611029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94356249511018760501074019 141534374266528140751611029)
  ·
    refine ⟨6634423793743506597731767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141534374266528140751611029 6634423793743506597731767)
    ·
      refine ⟨9951635690615259896597651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6634423793743506597731767 9951635690615259896597651)
      ·
        refine ⟨14927453535922889844896477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951635690615259896597651 14927453535922889844896477)
        ·
          refine ⟨5597795075971083691836179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14927453535922889844896477 5597795075971083691836179)
          ·
            refine ⟨8396692613956625537754269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597795075971083691836179 8396692613956625537754269)
            ·
              refine ⟨3148759730233734576657851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8396692613956625537754269 3148759730233734576657851)
              ·
                refine ⟨4723139595350601864986777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148759730233734576657851 4723139595350601864986777)
                ·
                  refine ⟨3542354696512951398740083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723139595350601864986777 3542354696512951398740083)
                  ·
                    refine ⟨5313532044769427098110125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542354696512951398740083 5313532044769427098110125)
                    ·
                      refine ⟨1992574516788535161791297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313532044769427098110125 1992574516788535161791297)
                      ·
                        rfl

theorem cell23_3880525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_3880525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880525 prefixEnd_3880525 := by exact prefixLift 3880525
  have htrace : WordTrace (prefixWord ++ tailWord_3880525) baseStart_3880525 baseEnd_3880525 := by
    simpa [prefixWord, tailWord_3880525, baseEnd_3880525] using wordTrace_append hprefix tailTrace_3880525
  have hstable : (prefixWord ++ tailWord_3880525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880525).length < 2 ^ (prefixWord ++ tailWord_3880525).sum := by decide
  have hdescent : baseEnd_3880525 < baseStart_3880525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880577 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3880577 : Nat := 118140960795 + 3880577 * 2 ^ 59
def prefixEnd_3880577 : Nat := 4983230072969 + 3 ^ 40 * 3880577 * 2
def baseEnd_3880577 : Nat := 1992601217782568958341057

theorem tailTrace_3880577 : CollatzResearch.WordTrace tailWord_3880577 prefixEnd_3880577 1992601217782568958341057 := by
  unfold tailWord_3880577
  simp only [CollatzResearch.WordTrace]
  refine ⟨141536270862339753632503985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94357513908226502421669323 141536270862339753632503985)
  ·
    refine ⟨106152203146754815224377989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141536270862339753632503985 106152203146754815224377989)
    ·
      refine ⟨19903538090016527854570873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106152203146754815224377989 19903538090016527854570873)
      ·
        refine ⟨14927653567512395890928155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903538090016527854570873 14927653567512395890928155)
        ·
          refine ⟨22391480351268593836392233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927653567512395890928155 22391480351268593836392233)
          ·
            refine ⟨16793610263451445377294175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22391480351268593836392233 16793610263451445377294175)
            ·
              refine ⟨25190415395177168065941263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16793610263451445377294175 25190415395177168065941263)
              ·
                refine ⟨37785623092765752098911895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25190415395177168065941263 37785623092765752098911895)
                ·
                  refine ⟨56678434639148628148367843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37785623092765752098911895 56678434639148628148367843)
                  ·
                    refine ⟨85017651958722942222551765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56678434639148628148367843 85017651958722942222551765)
                    ·
                      refine ⟨1992601217782568958341057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85017651958722942222551765 1992601217782568958341057)
                      ·
                        rfl

theorem cell23_3880577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3880577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880577 prefixEnd_3880577 := by exact prefixLift 3880577
  have htrace : WordTrace (prefixWord ++ tailWord_3880577) baseStart_3880577 baseEnd_3880577 := by
    simpa [prefixWord, tailWord_3880577, baseEnd_3880577] using wordTrace_append hprefix tailTrace_3880577
  have hstable : (prefixWord ++ tailWord_3880577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880577).length < 2 ^ (prefixWord ++ tailWord_3880577).sum := by decide
  have hdescent : baseEnd_3880577 < baseStart_3880577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880587 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4]
def baseStart_3880587 : Nat := 118140960795 + 3880587 * 2 ^ 59
def prefixEnd_3880587 : Nat := 4983230072969 + 3 ^ 40 * 3880587 * 2
def baseEnd_3880587 : Nat := 1992606352589113919216011

theorem tailTrace_3880587 : CollatzResearch.WordTrace tailWord_3880587 prefixEnd_3880587 1992606352589113919216011 := by
  unfold tailWord_3880587
  simp only [CollatzResearch.WordTrace]
  refine ⟨141536635592303525340368015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94357757061535683560245343 141536635592303525340368015)
  ·
    refine ⟨212304953388455288010552023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141536635592303525340368015 212304953388455288010552023)
    ·
      refine ⟨318457430082682932015828035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212304953388455288010552023 318457430082682932015828035)
      ·
        refine ⟨477686145124024398023742053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318457430082682932015828035 477686145124024398023742053)
        ·
          refine ⟨89566152210754574629451635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477686145124024398023742053 89566152210754574629451635)
          ·
            refine ⟨134349228316131861944177453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89566152210754574629451635 134349228316131861944177453)
            ·
              refine ⟨50380960618549448229066545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134349228316131861944177453 50380960618549448229066545)
              ·
                refine ⟨37785720463912086171799909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50380960618549448229066545 37785720463912086171799909)
                ·
                  refine ⟨7084822586983516157212483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37785720463912086171799909 7084822586983516157212483)
                  ·
                    refine ⟨10627233880475274235818725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7084822586983516157212483 10627233880475274235818725)
                    ·
                      refine ⟨1992606352589113919216011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10627233880475274235818725 1992606352589113919216011)
                      ·
                        rfl

theorem cell23_3880587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_3880587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880587 prefixEnd_3880587 := by exact prefixLift 3880587
  have htrace : WordTrace (prefixWord ++ tailWord_3880587) baseStart_3880587 baseEnd_3880587 := by
    simpa [prefixWord, tailWord_3880587, baseEnd_3880587] using wordTrace_append hprefix tailTrace_3880587
  have hstable : (prefixWord ++ tailWord_3880587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880587).length < 2 ^ (prefixWord ++ tailWord_3880587).sum := by decide
  have hdescent : baseEnd_3880587 < baseStart_3880587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880621 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_3880621 : Nat := 118140960795 + 3880621 * 2 ^ 59
def prefixEnd_3880621 : Nat := 4983230072969 + 3 ^ 40 * 3880621 * 2
def baseEnd_3880621 : Nat := 1992623810931366786190855

theorem tailTrace_3880621 : CollatzResearch.WordTrace tailWord_3880621 prefixEnd_3880621 1992623810931366786190855 := by
  unfold tailWord_3880621
  simp only [CollatzResearch.WordTrace]
  refine ⟨141537875674180349147105717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94358583782786899431403811 141537875674180349147105717)
  ·
    refine ⟨13269175844454407732541161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141537875674180349147105717 13269175844454407732541161)
    ·
      refine ⟨9951881883340805799405871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13269175844454407732541161 9951881883340805799405871)
      ·
        refine ⟨14927822825011208699108807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951881883340805799405871 14927822825011208699108807)
        ·
          refine ⟨22391734237516813048663211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927822825011208699108807 22391734237516813048663211)
          ·
            refine ⟨33587601356275219572994817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391734237516813048663211 33587601356275219572994817)
            ·
              refine ⟨25190701017206414679746113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33587601356275219572994817 25190701017206414679746113)
              ·
                refine ⟨18893025762904811009809585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25190701017206414679746113 18893025762904811009809585)
                ·
                  refine ⟨14169769322178608257357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18893025762904811009809585 14169769322178608257357189)
                  ·
                    refine ⟨2656831747908489048254473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14169769322178608257357189 2656831747908489048254473)
                    ·
                      refine ⟨1992623810931366786190855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656831747908489048254473 1992623810931366786190855)
                      ·
                        rfl

theorem cell23_3880621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_3880621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880621 prefixEnd_3880621 := by exact prefixLift 3880621
  have htrace : WordTrace (prefixWord ++ tailWord_3880621) baseStart_3880621 baseEnd_3880621 := by
    simpa [prefixWord, tailWord_3880621, baseEnd_3880621] using wordTrace_append hprefix tailTrace_3880621
  have hstable : (prefixWord ++ tailWord_3880621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880621).length < 2 ^ (prefixWord ++ tailWord_3880621).sum := by decide
  have hdescent : baseEnd_3880621 < baseStart_3880621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880622 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_3880622 : Nat := 118140960795 + 3880622 * 2 ^ 59
def prefixEnd_3880622 : Nat := 4983230072969 + 3 ^ 40 * 3880622 * 2
def baseEnd_3880622 : Nat := 221402702712446809142039

theorem tailTrace_3880622 : CollatzResearch.WordTrace tailWord_3880622 prefixEnd_3880622 221402702712446809142039 := by
  unfold tailWord_3880622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692239018397090789736515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94358608098117817545261413 17692239018397090789736515)
  ·
    refine ⟨26538358527595636184604773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692239018397090789736515 26538358527595636184604773)
    ·
      refine ⟨4975942223924181784613395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26538358527595636184604773 4975942223924181784613395)
      ·
        refine ⟨7463913335886272676920093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975942223924181784613395 7463913335886272676920093)
        ·
          refine ⟨2798967500957352253845035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7463913335886272676920093 2798967500957352253845035)
          ·
            refine ⟨4198451251436028380767553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798967500957352253845035 4198451251436028380767553)
            ·
              refine ⟨3148838438577021285575665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198451251436028380767553 3148838438577021285575665)
              ·
                refine ⟨2361628828932765964181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148838438577021285575665 2361628828932765964181749)
                ·
                  refine ⟨221402702712446809142039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361628828932765964181749 221402702712446809142039)
                  ·
                    rfl

theorem cell23_3880622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_3880622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880622 prefixEnd_3880622 := by exact prefixLift 3880622
  have htrace : WordTrace (prefixWord ++ tailWord_3880622) baseStart_3880622 baseEnd_3880622 := by
    simpa [prefixWord, tailWord_3880622, baseEnd_3880622] using wordTrace_append hprefix tailTrace_3880622
  have hstable : (prefixWord ++ tailWord_3880622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880622).length < 2 ^ (prefixWord ++ tailWord_3880622).sum := by decide
  have hdescent : baseEnd_3880622 < baseStart_3880622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880624 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_3880624 : Nat := 118140960795 + 3880624 * 2 ^ 59
def prefixEnd_3880624 : Nat := 4983230072969 + 3 ^ 40 * 3880624 * 2
def baseEnd_3880624 : Nat := 1992625351373330274453341

theorem tailTrace_3880624 : CollatzResearch.WordTrace tailWord_3880624 prefixEnd_3880624 1992625351373330274453341 := by
  unfold tailWord_3880624
  simp only [CollatzResearch.WordTrace]
  refine ⟨70768992546584740329732463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94358656728779653772976617 70768992546584740329732463)
  ·
    refine ⟨106153488819877110494598695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70768992546584740329732463 106153488819877110494598695)
    ·
      refine ⟨159230233229815665741898043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106153488819877110494598695 159230233229815665741898043)
      ·
        refine ⟨238845349844723498612847065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159230233229815665741898043 238845349844723498612847065)
        ·
          refine ⟨179134012383542623959635299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238845349844723498612847065 179134012383542623959635299)
          ·
            refine ⟨268701018575313935939452949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179134012383542623959635299 268701018575313935939452949)
            ·
              refine ⟨12595360245717840747161857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268701018575313935939452949 12595360245717840747161857)
              ·
                refine ⟨9446520184288380560371393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12595360245717840747161857 9446520184288380560371393)
                ·
                  refine ⟨7084890138216285420278545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446520184288380560371393 7084890138216285420278545)
                  ·
                    refine ⟨5313667603662214065208909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084890138216285420278545 5313667603662214065208909)
                    ·
                      refine ⟨1992625351373330274453341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313667603662214065208909 1992625351373330274453341)
                      ·
                        rfl

theorem cell23_3880624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_3880624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880624 prefixEnd_3880624 := by exact prefixLift 3880624
  have htrace : WordTrace (prefixWord ++ tailWord_3880624) baseStart_3880624 baseEnd_3880624 := by
    simpa [prefixWord, tailWord_3880624, baseEnd_3880624] using wordTrace_append hprefix tailTrace_3880624
  have hstable : (prefixWord ++ tailWord_3880624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880624).length < 2 ^ (prefixWord ++ tailWord_3880624).sum := by decide
  have hdescent : baseEnd_3880624 < baseStart_3880624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880644 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 6]
def baseStart_3880644 : Nat := 118140960795 + 3880644 * 2 ^ 59
def prefixEnd_3880644 : Nat := 4983230072969 + 3 ^ 40 * 3880644 * 2
def baseEnd_3880644 : Nat := 221403957887380021800361

theorem tailTrace_3880644 : CollatzResearch.WordTrace tailWord_3880644 prefixEnd_3880644 221403957887380021800361 := by
  unfold tailWord_3880644
  simp only [CollatzResearch.WordTrace]
  refine ⟨70769357276548512037596493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94359143035398016050128657 70769357276548512037596493)
  ·
    refine ⟨26538508978705692014098685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70769357276548512037596493 26538508978705692014098685)
    ·
      refine ⟨9951940867014634505287007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26538508978705692014098685 9951940867014634505287007)
      ·
        refine ⟨14927911300521951757930511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951940867014634505287007 14927911300521951757930511)
        ·
          refine ⟨22391866950782927636895767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927911300521951757930511 22391866950782927636895767)
          ·
            refine ⟨33587800426174391455343651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22391866950782927636895767 33587800426174391455343651)
            ·
              refine ⟨50381700639261587183015477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33587800426174391455343651 50381700639261587183015477)
              ·
                refine ⟨4723284434930773798407701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50381700639261587183015477 4723284434930773798407701)
                ·
                  refine ⟨221403957887380021800361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4723284434930773798407701 221403957887380021800361)
                  ·
                    rfl

theorem cell23_3880644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_3880644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880644 prefixEnd_3880644 := by exact prefixLift 3880644
  have htrace : WordTrace (prefixWord ++ tailWord_3880644) baseStart_3880644 baseEnd_3880644 := by
    simpa [prefixWord, tailWord_3880644, baseEnd_3880644] using wordTrace_append hprefix tailTrace_3880644
  have hstable : (prefixWord ++ tailWord_3880644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880644).length < 2 ^ (prefixWord ++ tailWord_3880644).sum := by decide
  have hdescent : baseEnd_3880644 < baseStart_3880644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880658 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3880658 : Nat := 118140960795 + 3880658 * 2 ^ 59
def prefixEnd_3880658 : Nat := 4983230072969 + 3 ^ 40 * 3880658 * 2
def baseEnd_3880658 : Nat := 1992642809715583141428185

theorem tailTrace_3880658 : CollatzResearch.WordTrace tailWord_3880658 prefixEnd_3880658 1992642809715583141428185 := by
  unfold tailWord_3880658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35384806293761576116550657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94359483450030869644135085 35384806293761576116550657)
  ·
    refine ⟨26538604720321182087412993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35384806293761576116550657 26538604720321182087412993)
    ·
      refine ⟨19903953540240886565559745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26538604720321182087412993 19903953540240886565559745)
      ·
        refine ⟨14927965155180664924169809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903953540240886565559745 14927965155180664924169809)
        ·
          refine ⟨11195973866385498693127357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927965155180664924169809 11195973866385498693127357)
          ·
            refine ⟨4198490199894562009922759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11195973866385498693127357 4198490199894562009922759)
            ·
              refine ⟨6297735299841843014884139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198490199894562009922759 6297735299841843014884139)
              ·
                refine ⟨9446602949762764522326209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297735299841843014884139 9446602949762764522326209)
                ·
                  refine ⟨7084952212322073391744657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446602949762764522326209 7084952212322073391744657)
                  ·
                    refine ⟨5313714159241555043808493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7084952212322073391744657 5313714159241555043808493)
                    ·
                      refine ⟨1992642809715583141428185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313714159241555043808493 1992642809715583141428185)
                      ·
                        rfl

theorem cell23_3880658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3880658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880658 prefixEnd_3880658 := by exact prefixLift 3880658
  have htrace : WordTrace (prefixWord ++ tailWord_3880658) baseStart_3880658 baseEnd_3880658 := by
    simpa [prefixWord, tailWord_3880658, baseEnd_3880658] using wordTrace_append hprefix tailTrace_3880658
  have hstable : (prefixWord ++ tailWord_3880658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880658).length < 2 ^ (prefixWord ++ tailWord_3880658).sum := by decide
  have hdescent : baseEnd_3880658 < baseStart_3880658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880722 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3880722 : Nat := 118140960795 + 3880722 * 2 ^ 59
def prefixEnd_3880722 : Nat := 4983230072969 + 3 ^ 40 * 3880722 * 2
def baseEnd_3880722 : Nat := 1992675672477470891027891

theorem tailTrace_3880722 : CollatzResearch.WordTrace tailWord_3880722 prefixEnd_3880722 1992675672477470891027891 := by
  unfold tailWord_3880722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385389861703610849133105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94361039631209628931021613 35385389861703610849133105)
  ·
    refine ⟨26539042396277708136849829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35385389861703610849133105 26539042396277708136849829)
    ·
      refine ⟨4976070449302070275659343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26539042396277708136849829 4976070449302070275659343)
      ·
        refine ⟨7464105673953105413489015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976070449302070275659343 7464105673953105413489015)
        ·
          refine ⟨11196158510929658120233523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464105673953105413489015 11196158510929658120233523)
          ·
            refine ⟨16794237766394487180350285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196158510929658120233523 16794237766394487180350285)
            ·
              refine ⟨6297839162397932692631357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16794237766394487180350285 6297839162397932692631357)
              ·
                refine ⟨2361689685899224759736759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6297839162397932692631357 2361689685899224759736759)
                ·
                  refine ⟨3542534528848837139605139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361689685899224759736759 3542534528848837139605139)
                  ·
                    refine ⟨5313801793273255709407709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542534528848837139605139 5313801793273255709407709)
                    ·
                      refine ⟨1992675672477470891027891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313801793273255709407709 1992675672477470891027891)
                      ·
                        rfl

theorem cell23_3880722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3880722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880722 prefixEnd_3880722 := by exact prefixLift 3880722
  have htrace : WordTrace (prefixWord ++ tailWord_3880722) baseStart_3880722 baseEnd_3880722 := by
    simpa [prefixWord, tailWord_3880722, baseEnd_3880722] using wordTrace_append hprefix tailTrace_3880722
  have hstable : (prefixWord ++ tailWord_3880722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880722).length < 2 ^ (prefixWord ++ tailWord_3880722).sum := by decide
  have hdescent : baseEnd_3880722 < baseStart_3880722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880755 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 2, 4]
def baseStart_3880755 : Nat := 118140960795 + 3880755 * 2 ^ 59
def prefixEnd_3880755 : Nat := 4983230072969 + 3 ^ 40 * 3880755 * 2
def baseEnd_3880755 : Nat := 664230872446356420638413

theorem tailTrace_3880755 : CollatzResearch.WordTrace tailWord_3880755 prefixEnd_3880755 664230872446356420638413 := by
  unfold tailWord_3880755
  simp only [CollatzResearch.WordTrace]
  refine ⟨141542763055694890032483719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94361842037129926688322479 141542763055694890032483719)
  ·
    refine ⟨212314144583542335048725579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141542763055694890032483719 212314144583542335048725579)
    ·
      refine ⟨318471216875313502573088369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212314144583542335048725579 318471216875313502573088369)
      ·
        refine ⟨238853412656485126929816277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318471216875313502573088369 238853412656485126929816277)
        ·
          refine ⟨5598126859136370162417569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238853412656485126929816277 5598126859136370162417569)
          ·
            refine ⟨4198595144352277621813177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598126859136370162417569 4198595144352277621813177)
            ·
              refine ⟨3148946358264208216359883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198595144352277621813177 3148946358264208216359883)
              ·
                refine ⟨4723419537396312324539825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148946358264208216359883 4723419537396312324539825)
                ·
                  refine ⟨3542564653047234243404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723419537396312324539825 3542564653047234243404869)
                  ·
                    refine ⟨664230872446356420638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3542564653047234243404869 664230872446356420638413)
                    ·
                      rfl

theorem cell23_3880755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 4].length) (baseStart_3880755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880755 prefixEnd_3880755 := by exact prefixLift 3880755
  have htrace : WordTrace (prefixWord ++ tailWord_3880755) baseStart_3880755 baseEnd_3880755 := by
    simpa [prefixWord, tailWord_3880755, baseEnd_3880755] using wordTrace_append hprefix tailTrace_3880755
  have hstable : (prefixWord ++ tailWord_3880755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880755).length < 2 ^ (prefixWord ++ tailWord_3880755).sum := by decide
  have hdescent : baseEnd_3880755 < baseStart_3880755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880765 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3880765 : Nat := 118140960795 + 3880765 * 2 ^ 59
def prefixEnd_3880765 : Nat := 4983230072969 + 3 ^ 40 * 3880765 * 2
def baseEnd_3880765 : Nat := 1992697752145614222790193

theorem tailTrace_3880765 : CollatzResearch.WordTrace tailWord_3880765 prefixEnd_3880765 1992697752145614222790193 := by
  unfold tailWord_3880765
  simp only [CollatzResearch.WordTrace]
  refine ⟨141543127785658661740347749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94362085190439107826898499 141543127785658661740347749)
  ·
    refine ⟨26539336459810999076315203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141543127785658661740347749 26539336459810999076315203)
    ·
      refine ⟨39809004689716498614472805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539336459810999076315203 39809004689716498614472805)
      ·
        refine ⟨7464188379321843490213651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39809004689716498614472805 7464188379321843490213651)
        ·
          refine ⟨11196282568982765235320477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464188379321843490213651 11196282568982765235320477)
          ·
            refine ⟨4198605963368536963245179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11196282568982765235320477 4198605963368536963245179)
            ·
              refine ⟨6297908945052805444867769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198605963368536963245179 6297908945052805444867769)
              ·
                refine ⟨4723431708789604083650827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6297908945052805444867769 4723431708789604083650827)
                ·
                  refine ⟨7085147563184406125476241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723431708789604083650827 7085147563184406125476241)
                  ·
                    refine ⟨5313860672388304594107181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085147563184406125476241 5313860672388304594107181)
                    ·
                      refine ⟨1992697752145614222790193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313860672388304594107181 1992697752145614222790193)
                      ·
                        rfl

theorem cell23_3880765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3880765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880765 prefixEnd_3880765 := by exact prefixLift 3880765
  have htrace : WordTrace (prefixWord ++ tailWord_3880765) baseStart_3880765 baseEnd_3880765 := by
    simpa [prefixWord, tailWord_3880765, baseEnd_3880765] using wordTrace_append hprefix tailTrace_3880765
  have hstable : (prefixWord ++ tailWord_3880765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880765).length < 2 ^ (prefixWord ++ tailWord_3880765).sum := by decide
  have hdescent : baseEnd_3880765 < baseStart_3880765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880794 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_3880794 : Nat := 118140960795 + 3880794 * 2 ^ 59
def prefixEnd_3880794 : Nat := 4983230072969 + 3 ^ 40 * 3880794 * 2
def baseEnd_3880794 : Nat := 664237547694864869775853

theorem tailTrace_3880794 : CollatzResearch.WordTrace tailWord_3880794 prefixEnd_3880794 664237547694864869775853 := by
  unfold tailWord_3880794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386046375638399923288359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94362790335035733128768957 35386046375638399923288359)
  ·
    refine ⟨53079069563457599884932539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35386046375638399923288359 53079069563457599884932539)
    ·
      refine ⟨79618604345186399827398809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53079069563457599884932539 79618604345186399827398809)
      ·
        refine ⟨59713953258889799870549107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79618604345186399827398809 59713953258889799870549107)
        ·
          refine ⟨89570929888334699805823661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59713953258889799870549107 89570929888334699805823661)
          ·
            refine ⟨33589098708125512427183873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89570929888334699805823661 33589098708125512427183873)
            ·
              refine ⟨25191824031094134320387905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33589098708125512427183873 25191824031094134320387905)
              ·
                refine ⟨18893868023320600740290929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25191824031094134320387905 18893868023320600740290929)
                ·
                  refine ⟨14170401017490450555218197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18893868023320600740290929 14170401017490450555218197)
                  ·
                    refine ⟨664237547694864869775853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14170401017490450555218197 664237547694864869775853)
                    ·
                      rfl

theorem cell23_3880794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_3880794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880794 prefixEnd_3880794 := by exact prefixLift 3880794
  have htrace : WordTrace (prefixWord ++ tailWord_3880794) baseStart_3880794 baseEnd_3880794 := by
    simpa [prefixWord, tailWord_3880794, baseEnd_3880794] using wordTrace_append hprefix tailTrace_3880794
  have hstable : (prefixWord ++ tailWord_3880794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880794).length < 2 ^ (prefixWord ++ tailWord_3880794).sum := by decide
  have hdescent : baseEnd_3880794 < baseStart_3880794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880796 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3880796 : Nat := 118140960795 + 3880796 * 2 ^ 59
def prefixEnd_3880796 : Nat := 4983230072969 + 3 ^ 40 * 3880796 * 2
def baseEnd_3880796 : Nat := 1992713670045903601502551

theorem tailTrace_3880796 : CollatzResearch.WordTrace tailWord_3880796 prefixEnd_3880796 1992713670045903601502551 := by
  unfold tailWord_3880796
  simp only [CollatzResearch.WordTrace]
  refine ⟨70772129224273177017363121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94362838965697569356484161 70772129224273177017363121)
  ·
    refine ⟨53079096918204882763022341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70772129224273177017363121 53079096918204882763022341)
    ·
      refine ⟨9952330672163415518066689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53079096918204882763022341 9952330672163415518066689)
      ·
        refine ⟨7464248004122561638550017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9952330672163415518066689 7464248004122561638550017)
        ·
          refine ⟨5598186003091921228912513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464248004122561638550017 5598186003091921228912513)
          ·
            refine ⟨4198639502318940921684385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598186003091921228912513 4198639502318940921684385)
            ·
              refine ⟨3148979626739205691263289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198639502318940921684385 3148979626739205691263289)
              ·
                refine ⟨2361734720054404268447467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148979626739205691263289 2361734720054404268447467)
                ·
                  refine ⟨3542602080081606402671201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361734720054404268447467 3542602080081606402671201)
                  ·
                    refine ⟨2656951560061204802003401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542602080081606402671201 2656951560061204802003401)
                    ·
                      refine ⟨1992713670045903601502551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656951560061204802003401 1992713670045903601502551)
                      ·
                        rfl

theorem cell23_3880796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3880796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880796 prefixEnd_3880796 := by exact prefixLift 3880796
  have htrace : WordTrace (prefixWord ++ tailWord_3880796) baseStart_3880796 baseEnd_3880796 := by
    simpa [prefixWord, tailWord_3880796, baseEnd_3880796] using wordTrace_append hprefix tailTrace_3880796
  have hstable : (prefixWord ++ tailWord_3880796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880796).length < 2 ^ (prefixWord ++ tailWord_3880796).sum := by decide
  have hdescent : baseEnd_3880796 < baseStart_3880796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880801 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_3880801 : Nat := 118140960795 + 3880801 * 2 ^ 59
def prefixEnd_3880801 : Nat := 4983230072969 + 3 ^ 40 * 3880801 * 2
def baseEnd_3880801 : Nat := 1992716237449176081940027

theorem tailTrace_3880801 : CollatzResearch.WordTrace tailWord_3880801 prefixEnd_3880801 1992716237449176081940027 := by
  unfold tailWord_3880801
  simp only [CollatzResearch.WordTrace]
  refine ⟨141544440813528239888658257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94362960542352159925772171 141544440813528239888658257)
  ·
    refine ⟨106158330610146179916493693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141544440813528239888658257 106158330610146179916493693)
    ·
      refine ⟨39809373978804817468685135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106158330610146179916493693 39809373978804817468685135)
      ·
        refine ⟨59714060968207226203027703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39809373978804817468685135 59714060968207226203027703)
        ·
          refine ⟨89571091452310839304541555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59714060968207226203027703 89571091452310839304541555)
          ·
            refine ⟨134356637178466258956812333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89571091452310839304541555 134356637178466258956812333)
            ·
              refine ⟨50383738941924847108804625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134356637178466258956812333 50383738941924847108804625)
              ·
                refine ⟨37787804206443635331603469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50383738941924847108804625 37787804206443635331603469)
                ·
                  refine ⟨14170426577416363249351301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37787804206443635331603469 14170426577416363249351301)
                  ·
                    refine ⟨2656954983265568109253369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14170426577416363249351301 2656954983265568109253369)
                    ·
                      refine ⟨1992716237449176081940027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656954983265568109253369 1992716237449176081940027)
                      ·
                        rfl

theorem cell23_3880801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_3880801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880801 prefixEnd_3880801 := by exact prefixLift 3880801
  have htrace : WordTrace (prefixWord ++ tailWord_3880801) baseStart_3880801 baseEnd_3880801 := by
    simpa [prefixWord, tailWord_3880801, baseEnd_3880801] using wordTrace_append hprefix tailTrace_3880801
  have hstable : (prefixWord ++ tailWord_3880801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880801).length < 2 ^ (prefixWord ++ tailWord_3880801).sum := by decide
  have hdescent : baseEnd_3880801 < baseStart_3880801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880818 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_3880818 : Nat := 118140960795 + 3880818 * 2 ^ 59
def prefixEnd_3880818 : Nat := 4983230072969 + 3 ^ 40 * 3880818 * 2
def baseEnd_3880818 : Nat := 1992724966620302515427449

theorem tailTrace_3880818 : CollatzResearch.WordTrace tailWord_3880818 prefixEnd_3880818 1992724966620302515427449 := by
  unfold tailWord_3880818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386265213616662948006777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94363373902977767861351405 35386265213616662948006777)
  ·
    refine ⟨26539698910212497211005083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35386265213616662948006777 26539698910212497211005083)
    ·
      refine ⟨39809548365318745816507625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26539698910212497211005083 39809548365318745816507625)
      ·
        refine ⟨29857161273989059362380719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39809548365318745816507625 29857161273989059362380719)
        ·
          refine ⟨44785741910983589043571079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29857161273989059362380719 44785741910983589043571079)
          ·
            refine ⟨67178612866475383565356619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44785741910983589043571079 67178612866475383565356619)
            ·
              refine ⟨100767919299713075348034929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67178612866475383565356619 100767919299713075348034929)
              ·
                refine ⟨75575939474784806511026197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100767919299713075348034929 75575939474784806511026197)
                ·
                  refine ⟨3542622162880537805204353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75575939474784806511026197 3542622162880537805204353)
                  ·
                    refine ⟨2656966622160403353903265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542622162880537805204353 2656966622160403353903265)
                    ·
                      refine ⟨1992724966620302515427449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656966622160403353903265 1992724966620302515427449)
                      ·
                        rfl

theorem cell23_3880818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_3880818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880818 prefixEnd_3880818 := by exact prefixLift 3880818
  have htrace : WordTrace (prefixWord ++ tailWord_3880818) baseStart_3880818 baseEnd_3880818 := by
    simpa [prefixWord, tailWord_3880818, baseEnd_3880818] using wordTrace_append hprefix tailTrace_3880818
  have hstable : (prefixWord ++ tailWord_3880818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880818).length < 2 ^ (prefixWord ++ tailWord_3880818).sum := by decide
  have hdescent : baseEnd_3880818 < baseStart_3880818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880821 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3880821 : Nat := 118140960795 + 3880821 * 2 ^ 59
def prefixEnd_3880821 : Nat := 4983230072969 + 3 ^ 40 * 3880821 * 2
def baseEnd_3880821 : Nat := 1992726507062266003689935

theorem tailTrace_3880821 : CollatzResearch.WordTrace tailWord_3880821 prefixEnd_3880821 1992726507062266003689935 := by
  unfold tailWord_3880821
  simp only [CollatzResearch.WordTrace]
  refine ⟨141545170273455783304386317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94363446848970522202924211 141545170273455783304386317)
  ·
    refine ⟨53079438852545918739144869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141545170273455783304386317 53079438852545918739144869)
    ·
      refine ⟨9952394784852359763589663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53079438852545918739144869 9952394784852359763589663)
      ·
        refine ⟨14928592177278539645384495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952394784852359763589663 14928592177278539645384495)
        ·
          refine ⟨22392888265917809468076743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928592177278539645384495 22392888265917809468076743)
          ·
            refine ⟨33589332398876714202115115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22392888265917809468076743 33589332398876714202115115)
            ·
              refine ⟨50383998598315071303172673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33589332398876714202115115 50383998598315071303172673)
              ·
                refine ⟨37787998948736303477379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50383998598315071303172673 37787998948736303477379505)
                ·
                  refine ⟨28340999211552227608034629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37787998948736303477379505 28340999211552227608034629)
                  ·
                    refine ⟨5313937352166042676506493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28340999211552227608034629 5313937352166042676506493)
                    ·
                      refine ⟨1992726507062266003689935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5313937352166042676506493 1992726507062266003689935)
                      ·
                        rfl

theorem cell23_3880821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3880821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880821 prefixEnd_3880821 := by exact prefixLift 3880821
  have htrace : WordTrace (prefixWord ++ tailWord_3880821) baseStart_3880821 baseEnd_3880821 := by
    simpa [prefixWord, tailWord_3880821, baseEnd_3880821] using wordTrace_append hprefix tailTrace_3880821
  have hstable : (prefixWord ++ tailWord_3880821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880821).length < 2 ^ (prefixWord ++ tailWord_3880821).sum := by decide
  have hdescent : baseEnd_3880821 < baseStart_3880821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880839 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_3880839 : Nat := 118140960795 + 3880839 * 2 ^ 59
def prefixEnd_3880839 : Nat := 4983230072969 + 3 ^ 40 * 3880839 * 2
def baseEnd_3880839 : Nat := 1992735749714046933264853

theorem tailTrace_3880839 : CollatzResearch.WordTrace tailWord_3880839 prefixEnd_3880839 1992735749714046933264853 := by
  unfold tailWord_3880839
  simp only [CollatzResearch.WordTrace]
  refine ⟨141545826787390572378541571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94363884524927048252361047 141545826787390572378541571)
  ·
    refine ⟨212318740181085858567812357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141545826787390572378541571 212318740181085858567812357)
    ·
      refine ⟨39809763783953598481464817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212318740181085858567812357 39809763783953598481464817)
      ·
        refine ⟨29857322837965198861098613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39809763783953598481464817 29857322837965198861098613)
        ·
          refine ⟨2799124016059237393227995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29857322837965198861098613 2799124016059237393227995)
          ·
            refine ⟨4198686024088856089841993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799124016059237393227995 4198686024088856089841993)
            ·
              refine ⟨3149014518066642067381495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198686024088856089841993 3149014518066642067381495)
              ·
                refine ⟨4723521777099963101072243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149014518066642067381495 4723521777099963101072243)
                ·
                  refine ⟨7085282665649944651608365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723521777099963101072243 7085282665649944651608365)
                  ·
                    refine ⟨2656980999618729244353137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7085282665649944651608365 2656980999618729244353137)
                    ·
                      refine ⟨1992735749714046933264853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656980999618729244353137 1992735749714046933264853)
                      ·
                        rfl

theorem cell23_3880839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_3880839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880839 prefixEnd_3880839 := by exact prefixLift 3880839
  have htrace : WordTrace (prefixWord ++ tailWord_3880839) baseStart_3880839 baseEnd_3880839 := by
    simpa [prefixWord, tailWord_3880839, baseEnd_3880839] using wordTrace_append hprefix tailTrace_3880839
  have hstable : (prefixWord ++ tailWord_3880839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880839).length < 2 ^ (prefixWord ++ tailWord_3880839).sum := by decide
  have hdescent : baseEnd_3880839 < baseStart_3880839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880852 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3880852 : Nat := 118140960795 + 3880852 * 2 ^ 59
def prefixEnd_3880852 : Nat := 4983230072969 + 3 ^ 40 * 3880852 * 2
def baseEnd_3880852 : Nat := 1992742424962555382402293

theorem tailTrace_3880852 : CollatzResearch.WordTrace tailWord_3880852 prefixEnd_3880852 1992742424962555382402293 := by
  unfold tailWord_3880852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773150468171737799382405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94364200624228983732509873 70773150468171737799382405)
  ·
    refine ⟨13269965712782200837384201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70773150468171737799382405 13269965712782200837384201)
    ·
      refine ⟨9952474284586650628038151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13269965712782200837384201 9952474284586650628038151)
      ·
        refine ⟨14928711426879975942057227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952474284586650628038151 14928711426879975942057227)
        ·
          refine ⟨22393067140319963913085841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928711426879975942057227 22393067140319963913085841)
          ·
            refine ⟨16794800355239972934814381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22393067140319963913085841 16794800355239972934814381)
            ·
              refine ⟨6298050133214989850555393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16794800355239972934814381 6298050133214989850555393)
              ·
                refine ⟨4723537599911242387916545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298050133214989850555393 4723537599911242387916545)
                ·
                  refine ⟨3542653199933431790937409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723537599911242387916545 3542653199933431790937409)
                  ·
                    refine ⟨2656989899950073843203057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542653199933431790937409 2656989899950073843203057)
                    ·
                      refine ⟨1992742424962555382402293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2656989899950073843203057 1992742424962555382402293)
                      ·
                        rfl

theorem cell23_3880852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3880852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880852 prefixEnd_3880852 := by exact prefixLift 3880852
  have htrace : WordTrace (prefixWord ++ tailWord_3880852) baseStart_3880852 baseEnd_3880852 := by
    simpa [prefixWord, tailWord_3880852, baseEnd_3880852] using wordTrace_append hprefix tailTrace_3880852
  have hstable : (prefixWord ++ tailWord_3880852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880852).length < 2 ^ (prefixWord ++ tailWord_3880852).sum := by decide
  have hdescent : baseEnd_3880852 < baseStart_3880852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880858 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_3880858 : Nat := 118140960795 + 3880858 * 2 ^ 59
def prefixEnd_3880858 : Nat := 4983230072969 + 3 ^ 40 * 3880858 * 2
def baseEnd_3880858 : Nat := 221416167316275817658585

theorem tailTrace_3880858 : CollatzResearch.WordTrace tailWord_3880858 prefixEnd_3880858 221416167316275817658585 := by
  unfold tailWord_3880858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386629943580434655870807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94364346516214492415655485 35386629943580434655870807)
  ·
    refine ⟨53079944915370651983806211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35386629943580434655870807 53079944915370651983806211)
    ·
      refine ⟨79619917373055977975709317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53079944915370651983806211 79619917373055977975709317)
      ·
        refine ⟨14928734507447995870445497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79619917373055977975709317 14928734507447995870445497)
        ·
          refine ⟨11196550880585996902834123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14928734507447995870445497 11196550880585996902834123)
          ·
            refine ⟨16794826320878995354251185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196550880585996902834123 16794826320878995354251185)
            ·
              refine ⟨12596119740659246515688389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16794826320878995354251185 12596119740659246515688389)
              ·
                refine ⟨2361772451373608721691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12596119740659246515688389 2361772451373608721691573)
                ·
                  refine ⟨221416167316275817658585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361772451373608721691573 221416167316275817658585)
                  ·
                    rfl

theorem cell23_3880858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_3880858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880858 prefixEnd_3880858 := by exact prefixLift 3880858
  have htrace : WordTrace (prefixWord ++ tailWord_3880858) baseStart_3880858 baseEnd_3880858 := by
    simpa [prefixWord, tailWord_3880858, baseEnd_3880858] using wordTrace_append hprefix tailTrace_3880858
  have hstable : (prefixWord ++ tailWord_3880858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880858).length < 2 ^ (prefixWord ++ tailWord_3880858).sum := by decide
  have hdescent : baseEnd_3880858 < baseStart_3880858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880864 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3880864 : Nat := 118140960795 + 3880864 * 2 ^ 59
def prefixEnd_3880864 : Nat := 4983230072969 + 3 ^ 40 * 3880864 * 2
def baseEnd_3880864 : Nat := 1992748586730409335452237

theorem tailTrace_3880864 : CollatzResearch.WordTrace tailWord_3880864 prefixEnd_3880864 1992748586730409335452237 := by
  unfold tailWord_3880864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773369306150000824100823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94364492408200001098801097 70773369306150000824100823)
  ·
    refine ⟨106160053959225001236151235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70773369306150000824100823 106160053959225001236151235)
    ·
      refine ⟨159240080938837501854226853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106160053959225001236151235 159240080938837501854226853)
      ·
        refine ⟨29857515176032031597667535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159240080938837501854226853 29857515176032031597667535)
        ·
          refine ⟨44786272764048047396501303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29857515176032031597667535 44786272764048047396501303)
          ·
            refine ⟨67179409146072071094751955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44786272764048047396501303 67179409146072071094751955)
            ·
              refine ⟨100769113719108106642127933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67179409146072071094751955 100769113719108106642127933)
              ·
                refine ⟨37788417644665539990797975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100769113719108106642127933 37788417644665539990797975)
                ·
                  refine ⟨56682626466998309986196963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37788417644665539990797975 56682626466998309986196963)
                  ·
                    refine ⟨85023939700497464979295445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56682626466998309986196963 85023939700497464979295445)
                    ·
                      refine ⟨1992748586730409335452237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85023939700497464979295445 1992748586730409335452237)
                      ·
                        rfl

theorem cell23_3880864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3880864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880864 prefixEnd_3880864 := by exact prefixLift 3880864
  have htrace : WordTrace (prefixWord ++ tailWord_3880864) baseStart_3880864 baseEnd_3880864 := by
    simpa [prefixWord, tailWord_3880864, baseEnd_3880864] using wordTrace_append hprefix tailTrace_3880864
  have hstable : (prefixWord ++ tailWord_3880864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880864).length < 2 ^ (prefixWord ++ tailWord_3880864).sum := by decide
  have hdescent : baseEnd_3880864 < baseStart_3880864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880871 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3880871 : Nat := 118140960795 + 3880871 * 2 ^ 59
def prefixEnd_3880871 : Nat := 4983230072969 + 3 ^ 40 * 3880871 * 2
def baseEnd_3880871 : Nat := 664250727031663602688235

theorem tailTrace_3880871 : CollatzResearch.WordTrace tailWord_3880871 prefixEnd_3880871 664250727031663602688235 := by
  unfold tailWord_3880871
  simp only [CollatzResearch.WordTrace]
  refine ⟨141546993923274641843706467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94364662615516427895804311 141546993923274641843706467)
  ·
    refine ⟨212320490884911962765559701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141546993923274641843706467 212320490884911962765559701)
    ·
      refine ⟨9952523010230248254635611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212320490884911962765559701 9952523010230248254635611)
      ·
        refine ⟨14928784515345372381953417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952523010230248254635611 14928784515345372381953417)
        ·
          refine ⟨11196588386509029286465063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14928784515345372381953417 11196588386509029286465063)
          ·
            refine ⟨16794882579763543929697595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196588386509029286465063 16794882579763543929697595)
            ·
              refine ⟨25192323869645315894546393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16794882579763543929697595 25192323869645315894546393)
              ·
                refine ⟨18894242902233986920909795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25192323869645315894546393 18894242902233986920909795)
                ·
                  refine ⟨28341364353350980381364693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18894242902233986920909795 28341364353350980381364693)
                  ·
                    refine ⟨664250727031663602688235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28341364353350980381364693 664250727031663602688235)
                    ·
                      rfl

theorem cell23_3880871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3880871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880871 prefixEnd_3880871 := by exact prefixLift 3880871
  have htrace : WordTrace (prefixWord ++ tailWord_3880871) baseStart_3880871 baseEnd_3880871 := by
    simpa [prefixWord, tailWord_3880871, baseEnd_3880871] using wordTrace_append hprefix tailTrace_3880871
  have hstable : (prefixWord ++ tailWord_3880871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880871).length < 2 ^ (prefixWord ++ tailWord_3880871).sum := by decide
  have hdescent : baseEnd_3880871 < baseStart_3880871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880891 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 6, 2]
def baseStart_3880891 : Nat := 118140960795 + 3880891 * 2 ^ 59
def prefixEnd_3880891 : Nat := 4983230072969 + 3 ^ 40 * 3880891 * 2
def baseEnd_3880891 : Nat := 1992762450708080729814613

theorem tailTrace_3880891 : CollatzResearch.WordTrace tailWord_3880891 prefixEnd_3880891 1992762450708080729814613 := by
  unfold tailWord_3880891
  simp only [CollatzResearch.WordTrace]
  refine ⟨141547723383202185259434527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94365148922134790172956351 141547723383202185259434527)
  ·
    refine ⟨212321585074803277889151791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141547723383202185259434527 212321585074803277889151791)
    ·
      refine ⟨318482377612204916833727687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212321585074803277889151791 318482377612204916833727687)
      ·
        refine ⟨477723566418307375250591531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318482377612204916833727687 477723566418307375250591531)
        ·
          refine ⟨716585349627461062875887297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477723566418307375250591531 716585349627461062875887297)
          ·
            refine ⟨537439012220595797156915473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716585349627461062875887297 537439012220595797156915473)
            ·
              refine ⟨403079259165446847867686605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537439012220595797156915473 403079259165446847867686605)
              ·
                refine ⟨151154722187042567950382477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403079259165446847867686605 151154722187042567950382477)
                ·
                  refine ⟨56683020820140962981393429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151154722187042567950382477 56683020820140962981393429)
                  ·
                    refine ⟨2657016600944107639752817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56683020820140962981393429 2657016600944107639752817)
                    ·
                      refine ⟨1992762450708080729814613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657016600944107639752817 1992762450708080729814613)
                      ·
                        rfl

theorem cell23_3880891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6, 2].length) (baseStart_3880891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880891 prefixEnd_3880891 := by exact prefixLift 3880891
  have htrace : WordTrace (prefixWord ++ tailWord_3880891) baseStart_3880891 baseEnd_3880891 := by
    simpa [prefixWord, tailWord_3880891, baseEnd_3880891] using wordTrace_append hprefix tailTrace_3880891
  have hstable : (prefixWord ++ tailWord_3880891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880891).length < 2 ^ (prefixWord ++ tailWord_3880891).sum := by decide
  have hdescent : baseEnd_3880891 < baseStart_3880891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880892 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 5]
def baseStart_3880892 : Nat := 118140960795 + 3880892 * 2 ^ 59
def prefixEnd_3880892 : Nat := 4983230072969 + 3 ^ 40 * 3880892 * 2
def baseEnd_3880892 : Nat := 221418107132081691766901

theorem tailTrace_3880892 : CollatzResearch.WordTrace tailWord_3880892 prefixEnd_3880892 221418107132081691766901 := by
  unfold tailWord_3880892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773879928099281215110465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94365173237465708286813953 70773879928099281215110465)
  ·
    refine ⟨53080409946074460911332849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70773879928099281215110465 53080409946074460911332849)
    ·
      refine ⟨39810307459555845683499637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53080409946074460911332849 39810307459555845683499637)
      ·
        refine ⟨3732216324333360532828091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39810307459555845683499637 3732216324333360532828091)
        ·
          refine ⟨5598324486500040799242137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732216324333360532828091 5598324486500040799242137)
          ·
            refine ⟨4198743364875030599431603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598324486500040799242137 4198743364875030599431603)
            ·
              refine ⟨6298115047312545899147405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198743364875030599431603 6298115047312545899147405)
              ·
                refine ⟨2361793142742204712180277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298115047312545899147405 2361793142742204712180277)
                ·
                  refine ⟨221418107132081691766901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361793142742204712180277 221418107132081691766901)
                  ·
                    rfl

theorem cell23_3880892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_3880892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880892 prefixEnd_3880892 := by exact prefixLift 3880892
  have htrace : WordTrace (prefixWord ++ tailWord_3880892) baseStart_3880892 baseEnd_3880892 := by
    simpa [prefixWord, tailWord_3880892, baseEnd_3880892] using wordTrace_append hprefix tailTrace_3880892
  have hstable : (prefixWord ++ tailWord_3880892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880892).length < 2 ^ (prefixWord ++ tailWord_3880892).sum := by decide
  have hdescent : baseEnd_3880892 < baseStart_3880892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880908 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3880908 : Nat := 118140960795 + 3880908 * 2 ^ 59
def prefixEnd_3880908 : Nat := 4983230072969 + 3 ^ 40 * 3880908 * 2
def baseEnd_3880908 : Nat := 1992771179879207163302035

theorem tailTrace_3880908 : CollatzResearch.WordTrace tailWord_3880908 prefixEnd_3880908 1992771179879207163302035 := by
  unfold tailWord_3880908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70774171712070298581401689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94365562282760398108535585 70774171712070298581401689)
  ·
    refine ⟨53080628784052723936051267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70774171712070298581401689 53080628784052723936051267)
    ·
      refine ⟨79620943176079085904076901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53080628784052723936051267 79620943176079085904076901)
      ·
        refine ⟨14928926845514828607014419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79620943176079085904076901 14928926845514828607014419)
        ·
          refine ⟨22393390268272242910521629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928926845514828607014419 22393390268272242910521629)
          ·
            refine ⟨8397521350602091091445611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22393390268272242910521629 8397521350602091091445611)
            ·
              refine ⟨12596282025903136637168417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397521350602091091445611 12596282025903136637168417)
              ·
                refine ⟨9447211519427352477876313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596282025903136637168417 9447211519427352477876313)
                ·
                  refine ⟨7085408639570514358407235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447211519427352477876313 7085408639570514358407235)
                  ·
                    refine ⟨10628112959355771537610853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085408639570514358407235 10628112959355771537610853)
                    ·
                      refine ⟨1992771179879207163302035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10628112959355771537610853 1992771179879207163302035)
                      ·
                        rfl

theorem cell23_3880908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3880908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880908 prefixEnd_3880908 := by exact prefixLift 3880908
  have htrace : WordTrace (prefixWord ++ tailWord_3880908) baseStart_3880908 baseEnd_3880908 := by
    simpa [prefixWord, tailWord_3880908, baseEnd_3880908] using wordTrace_append hprefix tailTrace_3880908
  have hstable : (prefixWord ++ tailWord_3880908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880908).length < 2 ^ (prefixWord ++ tailWord_3880908).sum := by decide
  have hdescent : baseEnd_3880908 < baseStart_3880908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3880945 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_3880945 : Nat := 118140960795 + 3880945 * 2 ^ 59
def prefixEnd_3880945 : Nat := 4983230072969 + 3 ^ 40 * 3880945 * 2
def baseEnd_3880945 : Nat := 1992790178663423518539365

theorem tailTrace_3880945 : CollatzResearch.WordTrace tailWord_3880945 prefixEnd_3880945 1992790178663423518539365 := by
  unfold tailWord_3880945
  simp only [CollatzResearch.WordTrace]
  refine ⟨141549692925006552481900289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94366461950004368321266859 141549692925006552481900289)
  ·
    refine ⟨106162269693754914361425217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141549692925006552481900289 106162269693754914361425217)
    ·
      refine ⟨79621702270316185771068913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106162269693754914361425217 79621702270316185771068913)
      ·
        refine ⟨59716276702737139328301685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79621702270316185771068913 59716276702737139328301685)
        ·
          refine ⟨5598400940881606812028283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59716276702737139328301685 5598400940881606812028283)
          ·
            refine ⟨8397601411322410218042425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598400940881606812028283 8397601411322410218042425)
            ·
              refine ⟨6298201058491807663531819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397601411322410218042425 6298201058491807663531819)
              ·
                refine ⟨9447301587737711495297729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298201058491807663531819 9447301587737711495297729)
                ·
                  refine ⟨7085476190803283621473297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447301587737711495297729 7085476190803283621473297)
                  ·
                    refine ⟨5314107143102462716104973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085476190803283621473297 5314107143102462716104973)
                    ·
                      refine ⟨1992790178663423518539365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5314107143102462716104973 1992790178663423518539365)
                      ·
                        rfl

theorem cell23_3880945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_3880945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3880945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3880945 prefixEnd_3880945 := by exact prefixLift 3880945
  have htrace : WordTrace (prefixWord ++ tailWord_3880945) baseStart_3880945 baseEnd_3880945 := by
    simpa [prefixWord, tailWord_3880945, baseEnd_3880945] using wordTrace_append hprefix tailTrace_3880945
  have hstable : (prefixWord ++ tailWord_3880945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3880945).length < 2 ^ (prefixWord ++ tailWord_3880945).sum := by decide
  have hdescent : baseEnd_3880945 < baseStart_3880945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3880945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881002 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3881002 : Nat := 118140960795 + 3881002 * 2 ^ 59
def prefixEnd_3881002 : Nat := 4983230072969 + 3 ^ 40 * 3881002 * 2
def baseEnd_3881002 : Nat := 1992819447060729795526603

theorem tailTrace_3881002 : CollatzResearch.WordTrace tailWord_3881002 prefixEnd_3881002 1992819447060729795526603 := by
  unfold tailWord_3881002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35387942971450012804181315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94367847923866700811150173 35387942971450012804181315)
  ·
    refine ⟨53081914457175019206271973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35387942971450012804181315 53081914457175019206271973)
    ·
      refine ⟨9952858960720316101175995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53081914457175019206271973 9952858960720316101175995)
      ·
        refine ⟨14929288441080474151763993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952858960720316101175995 14929288441080474151763993)
        ·
          refine ⟨11196966330810355613822995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14929288441080474151763993 11196966330810355613822995)
          ·
            refine ⟨16795449496215533420734493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11196966330810355613822995 16795449496215533420734493)
            ·
              refine ⟨6298293561080825032775435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16795449496215533420734493 6298293561080825032775435)
              ·
                refine ⟨9447440341621237549163153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298293561080825032775435 9447440341621237549163153)
                ·
                  refine ⟨7085580256215928161872365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447440341621237549163153 7085580256215928161872365)
                  ·
                    refine ⟨2657092596080973060702137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7085580256215928161872365 2657092596080973060702137)
                    ·
                      refine ⟨1992819447060729795526603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657092596080973060702137 1992819447060729795526603)
                      ·
                        rfl

theorem cell23_3881002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3881002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881002 prefixEnd_3881002 := by exact prefixLift 3881002
  have htrace : WordTrace (prefixWord ++ tailWord_3881002) baseStart_3881002 baseEnd_3881002 := by
    simpa [prefixWord, tailWord_3881002, baseEnd_3881002] using wordTrace_append hprefix tailTrace_3881002
  have hstable : (prefixWord ++ tailWord_3881002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881002).length < 2 ^ (prefixWord ++ tailWord_3881002).sum := by decide
  have hdescent : baseEnd_3881002 < baseStart_3881002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881012 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3881012 : Nat := 118140960795 + 3881012 * 2 ^ 59
def prefixEnd_3881012 : Nat := 4983230072969 + 3 ^ 40 * 3881012 * 2
def baseEnd_3881012 : Nat := 664274860622424918800519

theorem tailTrace_3881012 : CollatzResearch.WordTrace tailWord_3881012 prefixEnd_3881012 664274860622424918800519 := by
  unfold tailWord_3881012
  simp only [CollatzResearch.WordTrace]
  refine ⟨70776068307881911462294645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94368091077175881949726193 70776068307881911462294645)
  ·
    refine ⟨6635256403863929199590123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70776068307881911462294645 6635256403863929199590123)
    ·
      refine ⟨9952884605795893799385185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635256403863929199590123 9952884605795893799385185)
      ·
        refine ⟨7464663454346920349538889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9952884605795893799385185 7464663454346920349538889)
        ·
          refine ⟨5598497590760190262154167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464663454346920349538889 5598497590760190262154167)
          ·
            refine ⟨8397746386140285393231251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598497590760190262154167 8397746386140285393231251)
            ·
              refine ⟨12596619579210428089846877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397746386140285393231251 12596619579210428089846877)
              ·
                refine ⟨4723732342203910533692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12596619579210428089846877 4723732342203910533692579)
                ·
                  refine ⟨7085598513305865800538869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723732342203910533692579 7085598513305865800538869)
                  ·
                    refine ⟨664274860622424918800519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7085598513305865800538869 664274860622424918800519)
                    ·
                      rfl

theorem cell23_3881012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3881012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881012 prefixEnd_3881012 := by exact prefixLift 3881012
  have htrace : WordTrace (prefixWord ++ tailWord_3881012) baseStart_3881012 baseEnd_3881012 := by
    simpa [prefixWord, tailWord_3881012, baseEnd_3881012] using wordTrace_append hprefix tailTrace_3881012
  have hstable : (prefixWord ++ tailWord_3881012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881012).length < 2 ^ (prefixWord ++ tailWord_3881012).sum := by decide
  have hdescent : baseEnd_3881012 < baseStart_3881012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881015 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_3881015 : Nat := 118140960795 + 3881015 * 2 ^ 59
def prefixEnd_3881015 : Nat := 4983230072969 + 3 ^ 40 * 3881015 * 2
def baseEnd_3881015 : Nat := 1992826122309238244664043

theorem tailTrace_3881015 : CollatzResearch.WordTrace tailWord_3881015 prefixEnd_3881015 1992826122309238244664043 := by
  unfold tailWord_3881015
  simp only [CollatzResearch.WordTrace]
  refine ⟨141552246034752954436948499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94368164023168636291298999 141552246034752954436948499)
  ·
    refine ⟨212328369052129431655422749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141552246034752954436948499 212328369052129431655422749)
    ·
      refine ⟨79623138394548536870783531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212328369052129431655422749 79623138394548536870783531)
      ·
        refine ⟨119434707591822805306175297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79623138394548536870783531 119434707591822805306175297)
        ·
          refine ⟨89576030693867103979631473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119434707591822805306175297 89576030693867103979631473)
          ·
            refine ⟨67182023020400327984723605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89576030693867103979631473 67182023020400327984723605)
            ·
              refine ⟨3149157329081265374283919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67182023020400327984723605 3149157329081265374283919)
              ·
                refine ⟨4723735993621898061425879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149157329081265374283919 4723735993621898061425879)
                ·
                  refine ⟨7085603990432847092138819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723735993621898061425879 7085603990432847092138819)
                  ·
                    refine ⟨10628405985649270638208229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7085603990432847092138819 10628405985649270638208229)
                    ·
                      refine ⟨1992826122309238244664043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10628405985649270638208229 1992826122309238244664043)
                      ·
                        rfl

theorem cell23_3881015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_3881015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881015 prefixEnd_3881015 := by exact prefixLift 3881015
  have htrace : WordTrace (prefixWord ++ tailWord_3881015) baseStart_3881015 baseEnd_3881015 := by
    simpa [prefixWord, tailWord_3881015, baseEnd_3881015] using wordTrace_append hprefix tailTrace_3881015
  have hstable : (prefixWord ++ tailWord_3881015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881015).length < 2 ^ (prefixWord ++ tailWord_3881015).sum := by decide
  have hdescent : baseEnd_3881015 < baseStart_3881015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881021 : List Nat := [1, 4, 1, 3, 1, 1, 12]
def baseStart_3881021 : Nat := 118140960795 + 3881021 * 2 ^ 59
def prefixEnd_3881021 : Nat := 4983230072969 + 3 ^ 40 * 3881021 * 2
def baseEnd_3881021 : Nat := 24602829669051422483815

theorem tailTrace_3881021 : CollatzResearch.WordTrace tailWord_3881021 prefixEnd_3881021 24602829669051422483815 := by
  unfold tailWord_3881021
  simp only [CollatzResearch.WordTrace]
  refine ⟨141552464872731217461666917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94368309915154144974444611 141552464872731217461666917)
  ·
    refine ⟨26541087163637103274062547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141552464872731217461666917 26541087163637103274062547)
    ·
      refine ⟨39811630745455654911093821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26541087163637103274062547 39811630745455654911093821)
      ·
        refine ⟨14929361529545870591660183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39811630745455654911093821 14929361529545870591660183)
        ·
          refine ⟨22394042294318805887490275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14929361529545870591660183 22394042294318805887490275)
          ·
            refine ⟨33591063441478208831235413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22394042294318805887490275 33591063441478208831235413)
            ·
              refine ⟨24602829669051422483815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 33591063441478208831235413 24602829669051422483815)
              ·
                rfl

theorem cell23_3881021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 12].length) (baseStart_3881021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881021 prefixEnd_3881021 := by exact prefixLift 3881021
  have htrace : WordTrace (prefixWord ++ tailWord_3881021) baseStart_3881021 baseEnd_3881021 := by
    simpa [prefixWord, tailWord_3881021, baseEnd_3881021] using wordTrace_append hprefix tailTrace_3881021
  have hstable : (prefixWord ++ tailWord_3881021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881021).length < 2 ^ (prefixWord ++ tailWord_3881021).sum := by decide
  have hdescent : baseEnd_3881021 < baseStart_3881021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881025 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3881025 : Nat := 118140960795 + 3881025 * 2 ^ 59
def prefixEnd_3881025 : Nat := 4983230072969 + 3 ^ 40 * 3881025 * 2
def baseEnd_3881025 : Nat := 664277085705261068512999

theorem tailTrace_3881025 : CollatzResearch.WordTrace tailWord_3881025 prefixEnd_3881025 664277085705261068512999 := by
  unfold tailWord_3881025
  simp only [CollatzResearch.WordTrace]
  refine ⟨141552610764716726144812529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94368407176477817429875019 141552610764716726144812529)
  ·
    refine ⟨106164458073537544608609397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141552610764716726144812529 106164458073537544608609397)
    ·
      refine ⟨9952917944394144807057131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106164458073537544608609397 9952917944394144807057131)
      ·
        refine ⟨14929376916591217210585697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952917944394144807057131 14929376916591217210585697)
        ·
          refine ⟨11197032687443412907939273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14929376916591217210585697 11197032687443412907939273)
          ·
            refine ⟨8397774515582559680954455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11197032687443412907939273 8397774515582559680954455)
            ·
              refine ⟨12596661773373839521431683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397774515582559680954455 12596661773373839521431683)
              ·
                refine ⟨18894992660060759282147525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596661773373839521431683 18894992660060759282147525)
                ·
                  refine ⟨3542811123761392365402661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18894992660060759282147525 3542811123761392365402661)
                  ·
                    refine ⟨664277085705261068512999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3542811123761392365402661 664277085705261068512999)
                    ·
                      rfl

theorem cell23_3881025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3881025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881025 prefixEnd_3881025 := by exact prefixLift 3881025
  have htrace : WordTrace (prefixWord ++ tailWord_3881025) baseStart_3881025 baseEnd_3881025 := by
    simpa [prefixWord, tailWord_3881025, baseEnd_3881025] using wordTrace_append hprefix tailTrace_3881025
  have hstable : (prefixWord ++ tailWord_3881025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881025).length < 2 ^ (prefixWord ++ tailWord_3881025).sum := by decide
  have hdescent : baseEnd_3881025 < baseStart_3881025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881042 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3881042 : Nat := 118140960795 + 3881042 * 2 ^ 59
def prefixEnd_3881042 : Nat := 4983230072969 + 3 ^ 40 * 3881042 * 2
def baseEnd_3881042 : Nat := 664279995428969879675473

theorem tailTrace_3881042 : CollatzResearch.WordTrace tailWord_3881042 prefixEnd_3881042 664279995428969879675473 := by
  unfold tailWord_3881042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35388307701413784512045345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94368820537103425365454253 35388307701413784512045345)
  ·
    refine ⟨26541230776060338384034009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35388307701413784512045345 26541230776060338384034009)
    ·
      refine ⟨19905923082045253788025507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26541230776060338384034009 19905923082045253788025507)
      ·
        refine ⟨29858884623067880682038261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19905923082045253788025507 29858884623067880682038261)
        ·
          refine ⟨2799270433412613813941087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29858884623067880682038261 2799270433412613813941087)
          ·
            refine ⟨4198905650118920720911631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799270433412613813941087 4198905650118920720911631)
            ·
              refine ⟨6298358475178381081367447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198905650118920720911631 6298358475178381081367447)
              ·
                refine ⟨9447537712767571622051171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298358475178381081367447 9447537712767571622051171)
                ·
                  refine ⟨14171306569151357433076757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447537712767571622051171 14171306569151357433076757)
                  ·
                    refine ⟨664279995428969879675473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14171306569151357433076757 664279995428969879675473)
                    ·
                      rfl

theorem cell23_3881042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3881042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881042 prefixEnd_3881042 := by exact prefixLift 3881042
  have htrace : WordTrace (prefixWord ++ tailWord_3881042) baseStart_3881042 baseEnd_3881042 := by
    simpa [prefixWord, tailWord_3881042, baseEnd_3881042] using wordTrace_append hprefix tailTrace_3881042
  have hstable : (prefixWord ++ tailWord_3881042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881042).length < 2 ^ (prefixWord ++ tailWord_3881042).sum := by decide
  have hdescent : baseEnd_3881042 < baseStart_3881042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881045 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3881045 : Nat := 118140960795 + 3881045 * 2 ^ 59
def prefixEnd_3881045 : Nat := 4983230072969 + 3 ^ 40 * 3881045 * 2
def baseEnd_3881045 : Nat := 1992841526728873127288905

theorem tailTrace_3881045 : CollatzResearch.WordTrace tailWord_3881045 prefixEnd_3881045 1992841526728873127288905 := by
  unfold tailWord_3881045
  simp only [CollatzResearch.WordTrace]
  refine ⟨141553340224644269560540589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94368893483096179707027059 141553340224644269560540589)
  ·
    refine ⟨53082502584241601085202721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141553340224644269560540589 53082502584241601085202721)
    ·
      refine ⟨39811876938181200813902041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53082502584241601085202721 39811876938181200813902041)
      ·
        refine ⟨29858907703635900610426531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39811876938181200813902041 29858907703635900610426531)
        ·
          refine ⟨44788361555453850915639797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29858907703635900610426531 44788361555453850915639797)
          ·
            refine ⟨4198908895823798523341231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44788361555453850915639797 4198908895823798523341231)
            ·
              refine ⟨6298363343735697785011847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198908895823798523341231 6298363343735697785011847)
              ·
                refine ⟨9447545015603546677517771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298363343735697785011847 9447545015603546677517771)
                ·
                  refine ⟨14171317523405320016276657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447545015603546677517771 14171317523405320016276657)
                  ·
                    refine ⟨10628488142553990012207493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14171317523405320016276657 10628488142553990012207493)
                    ·
                      refine ⟨1992841526728873127288905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10628488142553990012207493 1992841526728873127288905)
                      ·
                        rfl

theorem cell23_3881045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3881045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881045 prefixEnd_3881045 := by exact prefixLift 3881045
  have htrace : WordTrace (prefixWord ++ tailWord_3881045) baseStart_3881045 baseEnd_3881045 := by
    simpa [prefixWord, tailWord_3881045, baseEnd_3881045] using wordTrace_append hprefix tailTrace_3881045
  have hstable : (prefixWord ++ tailWord_3881045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881045).length < 2 ^ (prefixWord ++ tailWord_3881045).sum := by decide
  have hdescent : baseEnd_3881045 < baseStart_3881045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881052 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3881052 : Nat := 118140960795 + 3881052 * 2 ^ 59
def prefixEnd_3881052 : Nat := 4983230072969 + 3 ^ 40 * 3881052 * 2
def baseEnd_3881052 : Nat := 1992845121093454599901373

theorem tailTrace_3881052 : CollatzResearch.WordTrace tailWord_3881052 prefixEnd_3881052 1992845121093454599901373 := by
  unfold tailWord_3881052
  simp only [CollatzResearch.WordTrace]
  refine ⟨70776797767809454878022705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94369063690412606504030273 70776797767809454878022705)
  ·
    refine ⟨53082598325857091158517029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70776797767809454878022705 53082598325857091158517029)
    ·
      refine ⟨9952987186098204592221943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53082598325857091158517029 9952987186098204592221943)
      ·
        refine ⟨14929480779147306888332915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952987186098204592221943 14929480779147306888332915)
        ·
          refine ⟨22394221168720960332499373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14929480779147306888332915 22394221168720960332499373)
          ·
            refine ⟨8397832938270360124687265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22394221168720960332499373 8397832938270360124687265)
            ·
              refine ⟨6298374703702770093515449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397832938270360124687265 6298374703702770093515449)
              ·
                refine ⟨4723781027777077570136587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298374703702770093515449 4723781027777077570136587)
                ·
                  refine ⟨7085671541665616355204881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723781027777077570136587 7085671541665616355204881)
                  ·
                    refine ⟨5314253656249212266403661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085671541665616355204881 5314253656249212266403661)
                    ·
                      refine ⟨1992845121093454599901373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5314253656249212266403661 1992845121093454599901373)
                      ·
                        rfl

theorem cell23_3881052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3881052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881052 prefixEnd_3881052 := by exact prefixLift 3881052
  have htrace : WordTrace (prefixWord ++ tailWord_3881052) baseStart_3881052 baseEnd_3881052 := by
    simpa [prefixWord, tailWord_3881052, baseEnd_3881052] using wordTrace_append hprefix tailTrace_3881052
  have hstable : (prefixWord ++ tailWord_3881052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881052).length < 2 ^ (prefixWord ++ tailWord_3881052).sum := by decide
  have hdescent : baseEnd_3881052 < baseStart_3881052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881122 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3881122 : Nat := 118140960795 + 3881122 * 2 ^ 59
def prefixEnd_3881122 : Nat := 4983230072969 + 3 ^ 40 * 3881122 * 2
def baseEnd_3881122 : Nat := 1992881064739269326026051

theorem tailTrace_3881122 : CollatzResearch.WordTrace tailWord_3881122 prefixEnd_3881122 1992881064739269326026051 := by
  unfold tailWord_3881122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35389037161341327927773405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94370765763576874474062413 35389037161341327927773405)
  ·
    refine ⟨13270888935502997972915027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35389037161341327927773405 13270888935502997972915027)
    ·
      refine ⟨19906333403254496959372541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13270888935502997972915027 19906333403254496959372541)
      ·
        refine ⟨7464875026220436359764703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19906333403254496959372541 7464875026220436359764703)
        ·
          refine ⟨11197312539330654539647055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464875026220436359764703 11197312539330654539647055)
          ·
            refine ⟨16795968808995981809470583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197312539330654539647055 16795968808995981809470583)
            ·
              refine ⟨25193953213493972714205875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16795968808995981809470583 25193953213493972714205875)
              ·
                refine ⟨37790929820240959071308813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25193953213493972714205875 37790929820240959071308813)
                ·
                  refine ⟨14171598682590359651740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37790929820240959071308813 14171598682590359651740805)
                  ·
                    refine ⟨2657174752985692434701401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14171598682590359651740805 2657174752985692434701401)
                    ·
                      refine ⟨1992881064739269326026051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657174752985692434701401 1992881064739269326026051)
                      ·
                        rfl

theorem cell23_3881122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3881122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881122 prefixEnd_3881122 := by exact prefixLift 3881122
  have htrace : WordTrace (prefixWord ++ tailWord_3881122) baseStart_3881122 baseEnd_3881122 := by
    simpa [prefixWord, tailWord_3881122, baseEnd_3881122] using wordTrace_append hprefix tailTrace_3881122
  have hstable : (prefixWord ++ tailWord_3881122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881122).length < 2 ^ (prefixWord ++ tailWord_3881122).sum := by decide
  have hdescent : baseEnd_3881122 < baseStart_3881122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881131 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_3881131 : Nat := 118140960795 + 3881131 * 2 ^ 59
def prefixEnd_3881131 : Nat := 4983230072969 + 3 ^ 40 * 3881131 * 2
def baseEnd_3881131 : Nat := 1992885686065159790813509

theorem tailTrace_3881131 : CollatzResearch.WordTrace tailWord_3881131 prefixEnd_3881131 1992885686065159790813509 := by
  unfold tailWord_3881131
  simp only [CollatzResearch.WordTrace]
  refine ⟨141556476902332706248171247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94370984601555137498780831 141556476902332706248171247)
  ·
    refine ⟨212334715353499059372256871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141556476902332706248171247 212334715353499059372256871)
    ·
      refine ⟨318502073030248589058385307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212334715353499059372256871 318502073030248589058385307)
      ·
        refine ⟨477753109545372883587577961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318502073030248589058385307 477753109545372883587577961)
        ·
          refine ⟨358314832159029662690683471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477753109545372883587577961 358314832159029662690683471)
          ·
            refine ⟨537472248238544494036025207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358314832159029662690683471 537472248238544494036025207)
            ·
              refine ⟨806208372357816741054037811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537472248238544494036025207 806208372357816741054037811)
              ·
                refine ⟨1209312558536725111581056717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806208372357816741054037811 1209312558536725111581056717)
                ·
                  refine ⟨453492209451271916842896269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209312558536725111581056717 453492209451271916842896269)
                  ·
                    refine ⟨170059578544226968816086101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453492209451271916842896269 170059578544226968816086101)
                    ·
                      refine ⟨1992885686065159790813509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170059578544226968816086101 1992885686065159790813509)
                      ·
                        rfl

theorem cell23_3881131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_3881131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881131 prefixEnd_3881131 := by exact prefixLift 3881131
  have htrace : WordTrace (prefixWord ++ tailWord_3881131) baseStart_3881131 baseEnd_3881131 := by
    simpa [prefixWord, tailWord_3881131, baseEnd_3881131] using wordTrace_append hprefix tailTrace_3881131
  have hstable : (prefixWord ++ tailWord_3881131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881131).length < 2 ^ (prefixWord ++ tailWord_3881131).sum := by decide
  have hdescent : baseEnd_3881131 < baseStart_3881131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881145 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 5]
def baseStart_3881145 : Nat := 118140960795 + 3881145 * 2 ^ 59
def prefixEnd_3881145 : Nat := 4983230072969 + 3 ^ 40 * 3881145 * 2
def baseEnd_3881145 : Nat := 221432541643813637337605

theorem tailTrace_3881145 : CollatzResearch.WordTrace tailWord_3881145 prefixEnd_3881145 221432541643813637337605 := by
  unfold tailWord_3881145
  simp only [CollatzResearch.WordTrace]
  refine ⟨141556987524281986639180889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94371325016187991092787259 141556987524281986639180889)
  ·
    refine ⟨106167740643211489979385667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141556987524281986639180889 106167740643211489979385667)
    ·
      refine ⟨159251610964817234969078501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106167740643211489979385667 159251610964817234969078501)
      ·
        refine ⟨29859677055903231556702219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159251610964817234969078501 29859677055903231556702219)
        ·
          refine ⟨44789515583854847335053329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29859677055903231556702219 44789515583854847335053329)
          ·
            refine ⟨33592136687891135501289997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44789515583854847335053329 33592136687891135501289997)
            ·
              refine ⟨12597051257959175812983749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33592136687891135501289997 12597051257959175812983749)
              ·
                refine ⟨2361947110867345464934453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12597051257959175812983749 2361947110867345464934453)
                ·
                  refine ⟨221432541643813637337605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361947110867345464934453 221432541643813637337605)
                  ·
                    rfl

theorem cell23_3881145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 5].length) (baseStart_3881145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881145 prefixEnd_3881145 := by exact prefixLift 3881145
  have htrace : WordTrace (prefixWord ++ tailWord_3881145) baseStart_3881145 baseEnd_3881145 := by
    simpa [prefixWord, tailWord_3881145, baseEnd_3881145] using wordTrace_append hprefix tailTrace_3881145
  have hstable : (prefixWord ++ tailWord_3881145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881145).length < 2 ^ (prefixWord ++ tailWord_3881145).sum := by decide
  have hdescent : baseEnd_3881145 < baseStart_3881145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881195 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 4, 2]
def baseStart_3881195 : Nat := 118140960795 + 3881195 * 2 ^ 59
def prefixEnd_3881195 : Nat := 4983230072969 + 3 ^ 40 * 3881195 * 2
def baseEnd_3881195 : Nat := 1992918548827047540413215

theorem tailTrace_3881195 : CollatzResearch.WordTrace tailWord_3881195 prefixEnd_3881195 1992918548827047540413215 := by
  unfold tailWord_3881195
  simp only [CollatzResearch.WordTrace]
  refine ⟨141558811174100845178501039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94372540782733896785667359 141558811174100845178501039)
  ·
    refine ⟨212338216761151267767751559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141558811174100845178501039 212338216761151267767751559)
    ·
      refine ⟨318507325141726901651627339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212338216761151267767751559 318507325141726901651627339)
      ·
        refine ⟨477760987712590352477441009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318507325141726901651627339 477760987712590352477441009)
        ·
          refine ⟨358320740784442764358080757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477760987712590352477441009 358320740784442764358080757)
          ·
            refine ⟨33592569448541509158570071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358320740784442764358080757 33592569448541509158570071)
            ·
              refine ⟨50388854172812263737855107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33592569448541509158570071 50388854172812263737855107)
              ·
                refine ⟨75583281259218395606782661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50388854172812263737855107 75583281259218395606782661)
                ·
                  refine ⟨14171865236103449176271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75583281259218395606782661 14171865236103449176271749)
                  ·
                    refine ⟨2657224731769396720550953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14171865236103449176271749 2657224731769396720550953)
                    ·
                      refine ⟨1992918548827047540413215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657224731769396720550953 1992918548827047540413215)
                      ·
                        rfl

theorem cell23_3881195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4, 2].length) (baseStart_3881195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881195 prefixEnd_3881195 := by exact prefixLift 3881195
  have htrace : WordTrace (prefixWord ++ tailWord_3881195) baseStart_3881195 baseEnd_3881195 := by
    simpa [prefixWord, tailWord_3881195, baseEnd_3881195] using wordTrace_append hprefix tailTrace_3881195
  have hstable : (prefixWord ++ tailWord_3881195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881195).length < 2 ^ (prefixWord ++ tailWord_3881195).sum := by decide
  have hdescent : baseEnd_3881195 < baseStart_3881195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881212 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_3881212 : Nat := 118140960795 + 3881212 * 2 ^ 59
def prefixEnd_3881212 : Nat := 4983230072969 + 3 ^ 40 * 3881212 * 2
def baseEnd_3881212 : Nat := 1992927277998173973900637

theorem tailTrace_3881212 : CollatzResearch.WordTrace tailWord_3881212 prefixEnd_3881212 1992927277998173973900637 := by
  unfold tailWord_3881212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70779715607519628540934945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94372954143359504721246593 70779715607519628540934945)
  ·
    refine ⟨53084786705639721405701209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70779715607519628540934945 53084786705639721405701209)
    ·
      refine ⟨39813590029229791054275907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53084786705639721405701209 39813590029229791054275907)
      ·
        refine ⟨59720385043844686581413861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39813590029229791054275907 59720385043844686581413861)
        ·
          refine ⟨11197572195720878734015099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59720385043844686581413861 11197572195720878734015099)
          ·
            refine ⟨16796358293581318101022649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197572195720878734015099 16796358293581318101022649)
            ·
              refine ⟨12597268720185988575766987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796358293581318101022649 12597268720185988575766987)
              ·
                refine ⟨18895903080278982863650481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597268720185988575766987 18895903080278982863650481)
                ·
                  refine ⟨14171927310209237147737861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18895903080278982863650481 14171927310209237147737861)
                  ·
                    refine ⟨2657236370664231965200849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14171927310209237147737861 2657236370664231965200849)
                    ·
                      refine ⟨1992927277998173973900637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657236370664231965200849 1992927277998173973900637)
                      ·
                        rfl

theorem cell23_3881212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_3881212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881212 prefixEnd_3881212 := by exact prefixLift 3881212
  have htrace : WordTrace (prefixWord ++ tailWord_3881212) baseStart_3881212 baseEnd_3881212 := by
    simpa [prefixWord, tailWord_3881212, baseEnd_3881212] using wordTrace_append hprefix tailTrace_3881212
  have hstable : (prefixWord ++ tailWord_3881212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881212).length < 2 ^ (prefixWord ++ tailWord_3881212).sum := by decide
  have hdescent : baseEnd_3881212 < baseStart_3881212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881239 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 1, 4]
def baseStart_3881239 : Nat := 118140960795 + 3881239 * 2 ^ 59
def prefixEnd_3881239 : Nat := 4983230072969 + 3 ^ 40 * 3881239 * 2
def baseEnd_3881239 : Nat := 664313713991948456087671

theorem tailTrace_3881239 : CollatzResearch.WordTrace tailWord_3881239 prefixEnd_3881239 664313713991948456087671 := by
  unfold tailWord_3881239
  simp only [CollatzResearch.WordTrace]
  refine ⟨141560415985941440693102771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94373610657294293795401847 141560415985941440693102771)
  ·
    refine ⟨212340623978912161039654157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141560415985941440693102771 212340623978912161039654157)
    ·
      refine ⟨79627733992092060389870309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212340623978912161039654157 79627733992092060389870309)
      ·
        refine ⟨14930200123517261323100683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79627733992092060389870309 14930200123517261323100683)
        ·
          refine ⟨22395300185275891984651025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930200123517261323100683 22395300185275891984651025)
          ·
            refine ⟨16796475138956918988488269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22395300185275891984651025 16796475138956918988488269)
            ·
              refine ⟨6298678177108844620683101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16796475138956918988488269 6298678177108844620683101)
              ·
                refine ⟨2362004316415816732756163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298678177108844620683101 2362004316415816732756163)
                ·
                  refine ⟨3543006474623725099134245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362004316415816732756163 3543006474623725099134245)
                  ·
                    refine ⟨664313713991948456087671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543006474623725099134245 664313713991948456087671)
                    ·
                      rfl

theorem cell23_3881239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_3881239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881239 prefixEnd_3881239 := by exact prefixLift 3881239
  have htrace : WordTrace (prefixWord ++ tailWord_3881239) baseStart_3881239 baseEnd_3881239 := by
    simpa [prefixWord, tailWord_3881239, baseEnd_3881239] using wordTrace_append hprefix tailTrace_3881239
  have hstable : (prefixWord ++ tailWord_3881239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881239).length < 2 ^ (prefixWord ++ tailWord_3881239).sum := by decide
  have hdescent : baseEnd_3881239 < baseStart_3881239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881256 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3881256 : Nat := 118140960795 + 3881256 * 2 ^ 59
def prefixEnd_3881256 : Nat := 4983230072969 + 3 ^ 40 * 3881256 * 2
def baseEnd_3881256 : Nat := 664316623715657267250145

theorem tailTrace_3881256 : CollatzResearch.WordTrace tailWord_3881256 prefixEnd_3881256 664316623715657267250145 := by
  unfold tailWord_3881256
  simp only [CollatzResearch.WordTrace]
  refine ⟨70780518013439926298235811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94374024017919901730981081 70780518013439926298235811)
  ·
    refine ⟨106170777020159889447353717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70780518013439926298235811 106170777020159889447353717)
    ·
      refine ⟨9953510345639989635689411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106170777020159889447353717 9953510345639989635689411)
      ·
        refine ⟨14930265518459984453534117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9953510345639989635689411 14930265518459984453534117)
        ·
          refine ⟨2799424784711247085037647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14930265518459984453534117 2799424784711247085037647)
          ·
            refine ⟨4199137177066870627556471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799424784711247085037647 4199137177066870627556471)
            ·
              refine ⟨6298705765600305941334707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199137177066870627556471 6298705765600305941334707)
              ·
                refine ⟨9448058648400458912002061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298705765600305941334707 9448058648400458912002061)
                ·
                  refine ⟨3543021993150172092000773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9448058648400458912002061 3543021993150172092000773)
                  ·
                    refine ⟨664316623715657267250145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543021993150172092000773 664316623715657267250145)
                    ·
                      rfl

theorem cell23_3881256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3881256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881256 prefixEnd_3881256 := by exact prefixLift 3881256
  have htrace : WordTrace (prefixWord ++ tailWord_3881256) baseStart_3881256 baseEnd_3881256 := by
    simpa [prefixWord, tailWord_3881256, baseEnd_3881256] using wordTrace_append hprefix tailTrace_3881256
  have hstable : (prefixWord ++ tailWord_3881256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881256).length < 2 ^ (prefixWord ++ tailWord_3881256).sum := by decide
  have hdescent : baseEnd_3881256 < baseStart_3881256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 4, 4]
def baseStart_3881295 : Nat := 118140960795 + 3881295 * 2 ^ 59
def prefixEnd_3881295 : Nat := 4983230072969 + 3 ^ 40 * 3881295 * 2
def baseEnd_3881295 : Nat := 664323298964165716387585

theorem tailTrace_3881295 : CollatzResearch.WordTrace tailWord_3881295 prefixEnd_3881295 664323298964165716387585 := by
  unfold tailWord_3881295
  simp only [CollatzResearch.WordTrace]
  refine ⟨141562458473738562257141339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94374972315825708171427559 141562458473738562257141339)
  ·
    refine ⟨212343687710607843385712009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141562458473738562257141339 212343687710607843385712009)
    ·
      refine ⟨159257765782955882539284007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212343687710607843385712009 159257765782955882539284007)
      ·
        refine ⟨238886648674433823808926011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159257765782955882539284007 238886648674433823808926011)
        ·
          refine ⟨358329973011650735713389017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238886648674433823808926011 358329973011650735713389017)
          ·
            refine ⟨268747479758738051785041763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358329973011650735713389017 268747479758738051785041763)
            ·
              refine ⟨403121219638107077677562645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268747479758738051785041763 403121219638107077677562645)
              ·
                refine ⟨18896307170536269266135749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403121219638107077677562645 18896307170536269266135749)
                ·
                  refine ⟨3543057594475550487400453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18896307170536269266135749 3543057594475550487400453)
                  ·
                    refine ⟨664323298964165716387585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543057594475550487400453 664323298964165716387585)
                    ·
                      rfl

theorem cell23_3881295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_3881295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881295 prefixEnd_3881295 := by exact prefixLift 3881295
  have htrace : WordTrace (prefixWord ++ tailWord_3881295) baseStart_3881295 baseEnd_3881295 := by
    simpa [prefixWord, tailWord_3881295, baseEnd_3881295] using wordTrace_append hprefix tailTrace_3881295
  have hstable : (prefixWord ++ tailWord_3881295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881295).length < 2 ^ (prefixWord ++ tailWord_3881295).sum := by decide
  have hdescent : baseEnd_3881295 < baseStart_3881295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881315 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3881315 : Nat := 118140960795 + 3881315 * 2 ^ 59
def prefixEnd_3881315 : Nat := 4983230072969 + 3 ^ 40 * 3881315 * 2
def baseEnd_3881315 : Nat := 1992980166505587070912663

theorem tailTrace_3881315 : CollatzResearch.WordTrace tailWord_3881315 prefixEnd_3881315 1992980166505587070912663 := by
  unfold tailWord_3881315
  simp only [CollatzResearch.WordTrace]
  refine ⟨141563187933666105672869399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94375458622444070448579599 141563187933666105672869399)
  ·
    refine ⟨212344781900499158509304099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141563187933666105672869399 212344781900499158509304099)
    ·
      refine ⟨318517172850748737763956149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212344781900499158509304099 318517172850748737763956149)
      ·
        refine ⟨29860984954757694165370889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318517172850748737763956149 29860984954757694165370889)
        ·
          refine ⟨22395738716068270624028167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29860984954757694165370889 22395738716068270624028167)
          ·
            refine ⟨33593608074102405936042251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22395738716068270624028167 33593608074102405936042251)
            ·
              refine ⟨50390412111153608904063377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33593608074102405936042251 50390412111153608904063377)
              ·
                refine ⟨37792809083365206678047533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50390412111153608904063377 37792809083365206678047533)
                ·
                  refine ⟨14172303406261952504267825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37792809083365206678047533 14172303406261952504267825)
                  ·
                    refine ⟨10629227554696464378200869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14172303406261952504267825 10629227554696464378200869)
                    ·
                      refine ⟨1992980166505587070912663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10629227554696464378200869 1992980166505587070912663)
                      ·
                        rfl

theorem cell23_3881315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3881315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881315 prefixEnd_3881315 := by exact prefixLift 3881315
  have htrace : WordTrace (prefixWord ++ tailWord_3881315) baseStart_3881315 baseEnd_3881315 := by
    simpa [prefixWord, tailWord_3881315, baseEnd_3881315] using wordTrace_append hprefix tailTrace_3881315
  have hstable : (prefixWord ++ tailWord_3881315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881315).length < 2 ^ (prefixWord ++ tailWord_3881315).sum := by decide
  have hdescent : baseEnd_3881315 < baseStart_3881315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881352 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3881352 : Nat := 118140960795 + 3881352 * 2 ^ 59
def prefixEnd_3881352 : Nat := 4983230072969 + 3 ^ 40 * 3881352 * 2
def baseEnd_3881352 : Nat := 1992999165289803426149993

theorem tailTrace_3881352 : CollatzResearch.WordTrace tailWord_3881352 prefixEnd_3881352 1992999165289803426149993 := by
  unfold tailWord_3881352
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782268717266030495983155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94376358289688040661310873 70782268717266030495983155)
  ·
    refine ⟨106173403075899045743974733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70782268717266030495983155 106173403075899045743974733)
    ·
      refine ⟨39815026153462142153990525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106173403075899045743974733 39815026153462142153990525)
      ·
        refine ⟨14930634807548303307746447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39815026153462142153990525 14930634807548303307746447)
        ·
          refine ⟨22395952211322454961619671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14930634807548303307746447 22395952211322454961619671)
          ·
            refine ⟨33593928316983682442429507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22395952211322454961619671 33593928316983682442429507)
            ·
              refine ⟨50390892475475523663644261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33593928316983682442429507 50390892475475523663644261)
              ·
                refine ⟨9448292339151660686933299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50390892475475523663644261 9448292339151660686933299)
                ·
                  refine ⟨14172438508727491030399949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448292339151660686933299 14172438508727491030399949)
                  ·
                    refine ⟨5314664440772809136399981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14172438508727491030399949 5314664440772809136399981)
                    ·
                      refine ⟨1992999165289803426149993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5314664440772809136399981 1992999165289803426149993)
                      ·
                        rfl

theorem cell23_3881352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3881352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881352 prefixEnd_3881352 := by exact prefixLift 3881352
  have htrace : WordTrace (prefixWord ++ tailWord_3881352) baseStart_3881352 baseEnd_3881352 := by
    simpa [prefixWord, tailWord_3881352, baseEnd_3881352] using wordTrace_append hprefix tailTrace_3881352
  have hstable : (prefixWord ++ tailWord_3881352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881352).length < 2 ^ (prefixWord ++ tailWord_3881352).sum := by decide
  have hdescent : baseEnd_3881352 < baseStart_3881352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881353 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 1, 2, 2]
def baseStart_3881353 : Nat := 118140960795 + 3881353 * 2 ^ 59
def prefixEnd_3881353 : Nat := 4983230072969 + 3 ^ 40 * 3881353 * 2
def baseEnd_3881353 : Nat := 1992999678770457922237489

theorem tailTrace_3881353 : CollatzResearch.WordTrace tailWord_3881353 prefixEnd_3881353 1992999678770457922237489 := by
  unfold tailWord_3881353
  simp only [CollatzResearch.WordTrace]
  refine ⟨141564573907528438162752713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94376382605018958775168475 141564573907528438162752713)
  ·
    refine ⟨106173430430646328622064535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141564573907528438162752713 106173430430646328622064535)
    ·
      refine ⟨159260145645969492933096803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106173430430646328622064535 159260145645969492933096803)
      ·
        refine ⟨238890218468954239399645205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159260145645969492933096803 238890218468954239399645205)
        ·
          refine ⟨11197978990732229971858369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 238890218468954239399645205 11197978990732229971858369)
          ·
            refine ⟨8398484243049172478893777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11197978990732229971858369 8398484243049172478893777)
            ·
              refine ⟨6298863182286879359170333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398484243049172478893777 6298863182286879359170333)
              ·
                refine ⟨2362073693357579759688875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298863182286879359170333 2362073693357579759688875)
                ·
                  refine ⟨3543110540036369639533313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362073693357579759688875 3543110540036369639533313)
                  ·
                    refine ⟨2657332905027277229649985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3543110540036369639533313 2657332905027277229649985)
                    ·
                      refine ⟨1992999678770457922237489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657332905027277229649985 1992999678770457922237489)
                      ·
                        rfl

theorem cell23_3881353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 2, 2].length) (baseStart_3881353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881353 prefixEnd_3881353 := by exact prefixLift 3881353
  have htrace : WordTrace (prefixWord ++ tailWord_3881353) baseStart_3881353 baseEnd_3881353 := by
    simpa [prefixWord, tailWord_3881353, baseEnd_3881353] using wordTrace_append hprefix tailTrace_3881353
  have hstable : (prefixWord ++ tailWord_3881353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881353).length < 2 ^ (prefixWord ++ tailWord_3881353).sum := by decide
  have hdescent : baseEnd_3881353 < baseStart_3881353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881356 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_3881356 : Nat := 118140960795 + 3881356 * 2 ^ 59
def prefixEnd_3881356 : Nat := 4983230072969 + 3 ^ 40 * 3881356 * 2
def baseEnd_3881356 : Nat := 1993001219212421410499975

theorem tailTrace_3881356 : CollatzResearch.WordTrace tailWord_3881356 prefixEnd_3881356 1993001219212421410499975 := by
  unfold tailWord_3881356
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782341663258784837555961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94376455551011713116741281 70782341663258784837555961)
  ·
    refine ⟨53086756247444088628166971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70782341663258784837555961 53086756247444088628166971)
    ·
      refine ⟨79630134371166132942250457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53086756247444088628166971 79630134371166132942250457)
      ·
        refine ⟨59722600778374599706687843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79630134371166132942250457 59722600778374599706687843)
        ·
          refine ⟨89583901167561899560031765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59722600778374599706687843 89583901167561899560031765)
          ·
            refine ⟨4199245367229464041876489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89583901167561899560031765 4199245367229464041876489)
            ·
              refine ⟨3149434025422098031407367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199245367229464041876489 3149434025422098031407367)
              ·
                refine ⟨4724151038133147047111051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149434025422098031407367 4724151038133147047111051)
                ·
                  refine ⟨7086226557199720570666577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724151038133147047111051 7086226557199720570666577)
                  ·
                    refine ⟨5314669917899790427999933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7086226557199720570666577 5314669917899790427999933)
                    ·
                      refine ⟨1993001219212421410499975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5314669917899790427999933 1993001219212421410499975)
                      ·
                        rfl

theorem cell23_3881356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_3881356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881356 prefixEnd_3881356 := by exact prefixLift 3881356
  have htrace : WordTrace (prefixWord ++ tailWord_3881356) baseStart_3881356 baseEnd_3881356 := by
    simpa [prefixWord, tailWord_3881356, baseEnd_3881356] using wordTrace_append hprefix tailTrace_3881356
  have hstable : (prefixWord ++ tailWord_3881356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881356).length < 2 ^ (prefixWord ++ tailWord_3881356).sum := by decide
  have hdescent : baseEnd_3881356 < baseStart_3881356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881443 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3881443 : Nat := 118140960795 + 3881443 * 2 ^ 59
def prefixEnd_3881443 : Nat := 4983230072969 + 3 ^ 40 * 3881443 * 2
def baseEnd_3881443 : Nat := 1993045892029362570112075

theorem tailTrace_3881443 : CollatzResearch.WordTrace tailWord_3881443 prefixEnd_3881443 1993045892029362570112075 := by
  unfold tailWord_3881443
  simp only [CollatzResearch.WordTrace]
  refine ⟨141567856477202383533528983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94378570984801589022352655 141567856477202383533528983)
  ·
    refine ⟨212351784715803575300293475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141567856477202383533528983 212351784715803575300293475)
    ·
      refine ⟨318527677073705362950440213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212351784715803575300293475 318527677073705362950440213)
      ·
        refine ⟨14930984862829938888301885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 318527677073705362950440213 14930984862829938888301885)
        ·
          refine ⟨5599119323561227083113207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14930984862829938888301885 5599119323561227083113207)
          ·
            refine ⟨8398678985341840624669811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599119323561227083113207 8398678985341840624669811)
            ·
              refine ⟨12598018478012760937004717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398678985341840624669811 12598018478012760937004717)
              ·
                refine ⟨4724256929254785351376769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12598018478012760937004717 4724256929254785351376769)
                ·
                  refine ⟨3543192696941089013532577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724256929254785351376769 3543192696941089013532577)
                  ·
                    refine ⟨2657394522705816760149433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3543192696941089013532577 2657394522705816760149433)
                    ·
                      refine ⟨1993045892029362570112075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657394522705816760149433 1993045892029362570112075)
                      ·
                        rfl

theorem cell23_3881443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3881443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881443 prefixEnd_3881443 := by exact prefixLift 3881443
  have htrace : WordTrace (prefixWord ++ tailWord_3881443) baseStart_3881443 baseEnd_3881443 := by
    simpa [prefixWord, tailWord_3881443, baseEnd_3881443] using wordTrace_append hprefix tailTrace_3881443
  have hstable : (prefixWord ++ tailWord_3881443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881443).length < 2 ^ (prefixWord ++ tailWord_3881443).sum := by decide
  have hdescent : baseEnd_3881443 < baseStart_3881443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881455 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_3881455 : Nat := 118140960795 + 3881455 * 2 ^ 59
def prefixEnd_3881455 : Nat := 4983230072969 + 3 ^ 40 * 3881455 * 2
def baseEnd_3881455 : Nat := 1993052053797216523162019

theorem tailTrace_3881455 : CollatzResearch.WordTrace tailWord_3881455 prefixEnd_3881455 1993052053797216523162019 := by
  unfold tailWord_3881455
  simp only [CollatzResearch.WordTrace]
  refine ⟨141568294153158909582965819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94378862768772606388643879 141568294153158909582965819)
  ·
    refine ⟨212352441229738364374448729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141568294153158909582965819 212352441229738364374448729)
    ·
      refine ⟨159264330922303773280836547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212352441229738364374448729 159264330922303773280836547)
      ·
        refine ⟨238896496383455659921254821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159264330922303773280836547 238896496383455659921254821)
        ·
          refine ⟨44793093071897936235235279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238896496383455659921254821 44793093071897936235235279)
          ·
            refine ⟨67189639607846904352852919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44793093071897936235235279 67189639607846904352852919)
            ·
              refine ⟨100784459411770356529279379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67189639607846904352852919 100784459411770356529279379)
              ·
                refine ⟨151176689117655534793919069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100784459411770356529279379 151176689117655534793919069)
                ·
                  refine ⟨56691258419120825547719651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151176689117655534793919069 56691258419120825547719651)
                  ·
                    refine ⟨85036887628681238321579477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56691258419120825547719651 85036887628681238321579477)
                    ·
                      refine ⟨1993052053797216523162019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85036887628681238321579477 1993052053797216523162019)
                      ·
                        rfl

theorem cell23_3881455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_3881455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881455 prefixEnd_3881455 := by exact prefixLift 3881455
  have htrace : WordTrace (prefixWord ++ tailWord_3881455) baseStart_3881455 baseEnd_3881455 := by
    simpa [prefixWord, tailWord_3881455, baseEnd_3881455] using wordTrace_append hprefix tailTrace_3881455
  have hstable : (prefixWord ++ tailWord_3881455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881455).length < 2 ^ (prefixWord ++ tailWord_3881455).sum := by decide
  have hdescent : baseEnd_3881455 < baseStart_3881455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881552 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_3881552 : Nat := 118140960795 + 3881552 * 2 ^ 59
def prefixEnd_3881552 : Nat := 4983230072969 + 3 ^ 40 * 3881552 * 2
def baseEnd_3881552 : Nat := 664367287140234214549691

theorem tailTrace_3881552 : CollatzResearch.WordTrace tailWord_3881552 prefixEnd_3881552 664367287140234214549691 := by
  unfold tailWord_3881552
  simp only [CollatzResearch.WordTrace]
  refine ⟨70785916016903747574623455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94381221355871663432831273 70785916016903747574623455)
  ·
    refine ⟨106178874025355621361935183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70785916016903747574623455 106178874025355621361935183)
    ·
      refine ⟨159268311038033432042902775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106178874025355621361935183 159268311038033432042902775)
      ·
        refine ⟨238902466557050148064354163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159268311038033432042902775 238902466557050148064354163)
        ·
          refine ⟨358353699835575222096531245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238902466557050148064354163 358353699835575222096531245)
          ·
            refine ⟨134382637438340708286199217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358353699835575222096531245 134382637438340708286199217)
            ·
              refine ⟨100786978078755531214649413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134382637438340708286199217 100786978078755531214649413)
              ·
                refine ⟨18897558389766662102746765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100786978078755531214649413 18897558389766662102746765)
                ·
                  refine ⟨7086584396162498288530037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18897558389766662102746765 7086584396162498288530037)
                  ·
                    refine ⟨664367287140234214549691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7086584396162498288530037 664367287140234214549691)
                    ·
                      rfl

theorem cell23_3881552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_3881552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881552 prefixEnd_3881552 := by exact prefixLift 3881552
  have htrace : WordTrace (prefixWord ++ tailWord_3881552) baseStart_3881552 baseEnd_3881552 := by
    simpa [prefixWord, tailWord_3881552, baseEnd_3881552] using wordTrace_append hprefix tailTrace_3881552
  have hstable : (prefixWord ++ tailWord_3881552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881552).length < 2 ^ (prefixWord ++ tailWord_3881552).sum := by decide
  have hdescent : baseEnd_3881552 < baseStart_3881552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881556 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 6]
def baseStart_3881556 : Nat := 118140960795 + 3881556 * 2 ^ 59
def prefixEnd_3881556 : Nat := 4983230072969 + 3 ^ 40 * 3881556 * 2
def baseEnd_3881556 : Nat := 221455990593702291999895

theorem tailTrace_3881556 : CollatzResearch.WordTrace tailWord_3881556 prefixEnd_3881556 221455990593702291999895 := by
  unfold tailWord_3881556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70785988962896501916196261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94381318617195335888261681 70785988962896501916196261)
  ·
    refine ⟨13272372930543094109286799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70785988962896501916196261 13272372930543094109286799)
    ·
      refine ⟨19908559395814641163930199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13272372930543094109286799 19908559395814641163930199)
      ·
        refine ⟨29862839093721961745895299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19908559395814641163930199 29862839093721961745895299)
        ·
          refine ⟨44794258640582942618842949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29862839093721961745895299 44794258640582942618842949)
          ·
            refine ⟨8398923495109301741033053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44794258640582942618842949 8398923495109301741033053)
            ·
              refine ⟨3149596310665988152887395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8398923495109301741033053 3149596310665988152887395)
              ·
                refine ⟨4724394465998982229331093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149596310665988152887395 4724394465998982229331093)
                ·
                  refine ⟨221455990593702291999895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4724394465998982229331093 221455990593702291999895)
                  ·
                    rfl

theorem cell23_3881556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_3881556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881556 prefixEnd_3881556 := by exact prefixLift 3881556
  have htrace : WordTrace (prefixWord ++ tailWord_3881556) baseStart_3881556 baseEnd_3881556 := by
    simpa [prefixWord, tailWord_3881556, baseEnd_3881556] using wordTrace_append hprefix tailTrace_3881556
  have hstable : (prefixWord ++ tailWord_3881556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881556).length < 2 ^ (prefixWord ++ tailWord_3881556).sum := by decide
  have hdescent : baseEnd_3881556 < baseStart_3881556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881559 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_3881559 : Nat := 118140960795 + 3881559 * 2 ^ 59
def prefixEnd_3881559 : Nat := 4983230072969 + 3 ^ 40 * 3881559 * 2
def baseEnd_3881559 : Nat := 1993105455785284116261541

theorem tailTrace_3881559 : CollatzResearch.WordTrace tailWord_3881559 prefixEnd_3881559 1993105455785284116261541 := by
  unfold tailWord_3881559
  simp only [CollatzResearch.WordTrace]
  refine ⟨141572087344782135344751731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94381391563188090229834487 141572087344782135344751731)
  ·
    refine ⟨212358131017173203017127597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141572087344782135344751731 212358131017173203017127597)
    ·
      refine ⟨79634299131439951131422849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212358131017173203017127597 79634299131439951131422849)
      ·
        refine ⟨59725724348579963348567137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79634299131439951131422849 59725724348579963348567137)
        ·
          refine ⟨44794293261434972511425353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59725724348579963348567137 44794293261434972511425353)
          ·
            refine ⟨33595719946076229383569015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44794293261434972511425353 33595719946076229383569015)
            ·
              refine ⟨50393579919114344075353523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33595719946076229383569015 50393579919114344075353523)
              ·
                refine ⟨75590369878671516113030285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50393579919114344075353523 75590369878671516113030285)
                ·
                  refine ⟨28346388704501818542386357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75590369878671516113030285 28346388704501818542386357)
                  ·
                    refine ⟨2657473941047045488348721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28346388704501818542386357 2657473941047045488348721)
                    ·
                      refine ⟨1993105455785284116261541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657473941047045488348721 1993105455785284116261541)
                      ·
                        rfl

theorem cell23_3881559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_3881559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881559 prefixEnd_3881559 := by exact prefixLift 3881559
  have htrace : WordTrace (prefixWord ++ tailWord_3881559) baseStart_3881559 baseEnd_3881559 := by
    simpa [prefixWord, tailWord_3881559, baseEnd_3881559] using wordTrace_append hprefix tailTrace_3881559
  have hstable : (prefixWord ++ tailWord_3881559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881559).length < 2 ^ (prefixWord ++ tailWord_3881559).sum := by decide
  have hdescent : baseEnd_3881559 < baseStart_3881559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881569 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3881569 : Nat := 118140960795 + 3881569 * 2 ^ 59
def prefixEnd_3881569 : Nat := 4983230072969 + 3 ^ 40 * 3881569 * 2
def baseEnd_3881569 : Nat := 664370196863943025712165

theorem tailTrace_3881569 : CollatzResearch.WordTrace tailWord_3881569 prefixEnd_3881569 664370196863943025712165 := by
  unfold tailWord_3881569
  simp only [CollatzResearch.WordTrace]
  refine ⟨141572452074745907052615761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94381634716497271368410507 141572452074745907052615761)
  ·
    refine ⟨106179339056059430289461821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141572452074745907052615761 106179339056059430289461821)
    ·
      refine ⟨39817252146022286358548183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106179339056059430289461821 39817252146022286358548183)
      ·
        refine ⟨59725878219033429537822275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39817252146022286358548183 59725878219033429537822275)
        ·
          refine ⟨89588817328550144306733413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59725878219033429537822275 89588817328550144306733413)
          ·
            refine ⟨16797903249103152057512515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89588817328550144306733413 16797903249103152057512515)
            ·
              refine ⟨25196854873654728086268773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16797903249103152057512515 25196854873654728086268773)
              ·
                refine ⟨4724410288810261516175395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25196854873654728086268773 4724410288810261516175395)
                ·
                  refine ⟨7086615433215392274263093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724410288810261516175395 7086615433215392274263093)
                  ·
                    refine ⟨664370196863943025712165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7086615433215392274263093 664370196863943025712165)
                    ·
                      rfl

theorem cell23_3881569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3881569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881569 prefixEnd_3881569 := by exact prefixLift 3881569
  have htrace : WordTrace (prefixWord ++ tailWord_3881569) baseStart_3881569 baseEnd_3881569 := by
    simpa [prefixWord, tailWord_3881569, baseEnd_3881569] using wordTrace_append hprefix tailTrace_3881569
  have hstable : (prefixWord ++ tailWord_3881569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881569).length < 2 ^ (prefixWord ++ tailWord_3881569).sum := by decide
  have hdescent : baseEnd_3881569 < baseStart_3881569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881583 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 1, 1, 3]
def baseStart_3881583 : Nat := 118140960795 + 3881583 * 2 ^ 59
def prefixEnd_3881583 : Nat := 4983230072969 + 3 ^ 40 * 3881583 * 2
def baseEnd_3881583 : Nat := 1993117779320992022361431

theorem tailTrace_3881583 : CollatzResearch.WordTrace tailWord_3881583 prefixEnd_3881583 1993117779320992022361431 := by
  unfold tailWord_3881583
  simp only [CollatzResearch.WordTrace]
  refine ⟨141572962696695187443625403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94381975131130124962416935 141572962696695187443625403)
  ·
    refine ⟨212359444045042781165438105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141572962696695187443625403 212359444045042781165438105)
    ·
      refine ⟨159269583033782085874078579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212359444045042781165438105 159269583033782085874078579)
      ·
        refine ⟨238904374550673128811117869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159269583033782085874078579 238904374550673128811117869)
        ·
          refine ⟨89589140456502423304169201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238904374550673128811117869 89589140456502423304169201)
          ·
            refine ⟨67191855342376817478126901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89589140456502423304169201 67191855342376817478126901)
            ·
              refine ⟨6299236438347826638574397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67191855342376817478126901 6299236438347826638574397)
              ·
                refine ⟨2362213664380434989465399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6299236438347826638574397 2362213664380434989465399)
                ·
                  refine ⟨3543320496570652484198099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362213664380434989465399 3543320496570652484198099)
                  ·
                    refine ⟨5314980744855978726297149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3543320496570652484198099 5314980744855978726297149)
                    ·
                      refine ⟨1993117779320992022361431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5314980744855978726297149 1993117779320992022361431)
                      ·
                        rfl

theorem cell23_3881583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 1, 3].length) (baseStart_3881583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881583 prefixEnd_3881583 := by exact prefixLift 3881583
  have htrace : WordTrace (prefixWord ++ tailWord_3881583) baseStart_3881583 baseEnd_3881583 := by
    simpa [prefixWord, tailWord_3881583, baseEnd_3881583] using wordTrace_append hprefix tailTrace_3881583
  have hstable : (prefixWord ++ tailWord_3881583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881583).length < 2 ^ (prefixWord ++ tailWord_3881583).sum := by decide
  have hdescent : baseEnd_3881583 < baseStart_3881583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_3881592 : Nat := 118140960795 + 3881592 * 2 ^ 59
def prefixEnd_3881592 : Nat := 4983230072969 + 3 ^ 40 * 3881592 * 2
def baseEnd_3881592 : Nat := 1993122400646882487148889

theorem tailTrace_3881592 : CollatzResearch.WordTrace tailWord_3881592 prefixEnd_3881592 1993122400646882487148889 := by
  unfold tailWord_3881592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70786645476831290990351515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94382193969108387987135353 70786645476831290990351515)
  ·
    refine ⟨106179968215246936485527273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70786645476831290990351515 106179968215246936485527273)
    ·
      refine ⟨79634976161435202364145455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106179968215246936485527273 79634976161435202364145455)
      ·
        refine ⟨119452464242152803546218183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79634976161435202364145455 119452464242152803546218183)
        ·
          refine ⟨179178696363229205319327275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119452464242152803546218183 179178696363229205319327275)
          ·
            refine ⟨268768044544843807978990913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179178696363229205319327275 268768044544843807978990913)
            ·
              refine ⟨201576033408632855984243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268768044544843807978990913 201576033408632855984243185)
              ·
                refine ⟨151182025056474641988182389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201576033408632855984243185 151182025056474641988182389)
                ·
                  refine ⟨14173314849044497686392099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151182025056474641988182389 14173314849044497686392099)
                  ·
                    refine ⟨21259972273566746529588149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14173314849044497686392099 21259972273566746529588149)
                    ·
                      refine ⟨1993122400646882487148889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21259972273566746529588149 1993122400646882487148889)
                      ·
                        rfl

theorem cell23_3881592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_3881592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881592 prefixEnd_3881592 := by exact prefixLift 3881592
  have htrace : WordTrace (prefixWord ++ tailWord_3881592) baseStart_3881592 baseEnd_3881592 := by
    simpa [prefixWord, tailWord_3881592, baseEnd_3881592] using wordTrace_append hprefix tailTrace_3881592
  have hstable : (prefixWord ++ tailWord_3881592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881592).length < 2 ^ (prefixWord ++ tailWord_3881592).sum := by decide
  have hdescent : baseEnd_3881592 < baseStart_3881592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881600 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 1, 1, 3]
def baseStart_3881600 : Nat := 118140960795 + 3881600 * 2 ^ 59
def prefixEnd_3881600 : Nat := 4983230072969 + 3 ^ 40 * 3881600 * 2
def baseEnd_3881600 : Nat := 1993126508492118455848853

theorem tailTrace_3881600 : CollatzResearch.WordTrace tailWord_3881600 prefixEnd_3881600 1993126508492118455848853 := by
  unfold tailWord_3881600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70786791368816799673497127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94382388491755732897996169 70786791368816799673497127)
  ·
    refine ⟨106180187053225199510245691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70786791368816799673497127 106180187053225199510245691)
    ·
      refine ⟨159270280579837799265368537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106180187053225199510245691 159270280579837799265368537)
      ·
        refine ⟨119452710434878349449026403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159270280579837799265368537 119452710434878349449026403)
        ·
          refine ⟨179179065652317524173539605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119452710434878349449026403 179179065652317524173539605)
          ·
            refine ⟨8399018702452383945634669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179179065652317524173539605 8399018702452383945634669)
            ·
              refine ⟨3149632013419643979613001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399018702452383945634669 3149632013419643979613001)
              ·
                refine ⟨2362224010064732984709751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149632013419643979613001 2362224010064732984709751)
                ·
                  refine ⟨3543336015097099477064627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362224010064732984709751 3543336015097099477064627)
                  ·
                    refine ⟨5315004022645649215596941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3543336015097099477064627 5315004022645649215596941)
                    ·
                      refine ⟨1993126508492118455848853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315004022645649215596941 1993126508492118455848853)
                      ·
                        rfl

theorem cell23_3881600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_3881600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881600 prefixEnd_3881600 := by exact prefixLift 3881600
  have htrace : WordTrace (prefixWord ++ tailWord_3881600) baseStart_3881600 baseEnd_3881600 := by
    simpa [prefixWord, tailWord_3881600, baseEnd_3881600] using wordTrace_append hprefix tailTrace_3881600
  have hstable : (prefixWord ++ tailWord_3881600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881600).length < 2 ^ (prefixWord ++ tailWord_3881600).sum := by decide
  have hdescent : baseEnd_3881600 < baseStart_3881600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881609 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_3881609 : Nat := 118140960795 + 3881609 * 2 ^ 59
def prefixEnd_3881609 : Nat := 4983230072969 + 3 ^ 40 * 3881609 * 2
def baseEnd_3881609 : Nat := 1993131129818008920636311

theorem tailTrace_3881609 : CollatzResearch.WordTrace tailWord_3881609 prefixEnd_3881609 1993131129818008920636311 := by
  unfold tailWord_3881609
  simp only [CollatzResearch.WordTrace]
  refine ⟨141573910994600993884071881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94382607329733995922714587 141573910994600993884071881)
  ·
    refine ⟨106180433245950745413053911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141573910994600993884071881 106180433245950745413053911)
    ·
      refine ⟨159270649868926118119580867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106180433245950745413053911 159270649868926118119580867)
      ·
        refine ⟨238905974803389177179371301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159270649868926118119580867 238905974803389177179371301)
        ·
          refine ⟨44794870275635470721132119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238905974803389177179371301 44794870275635470721132119)
          ·
            refine ⟨67192305413453206081698179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44794870275635470721132119 67192305413453206081698179)
            ·
              refine ⟨100788458120179809122547269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67192305413453206081698179 100788458120179809122547269)
              ·
                refine ⟨18897835897533714210477613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100788458120179809122547269 18897835897533714210477613)
                ·
                  refine ⟨7086688461575142828929105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18897835897533714210477613 7086688461575142828929105)
                  ·
                    refine ⟨5315016346181357121696829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7086688461575142828929105 5315016346181357121696829)
                    ·
                      refine ⟨1993131129818008920636311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315016346181357121696829 1993131129818008920636311)
                      ·
                        rfl

theorem cell23_3881609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_3881609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881609 prefixEnd_3881609 := by exact prefixLift 3881609
  have htrace : WordTrace (prefixWord ++ tailWord_3881609) baseStart_3881609 baseEnd_3881609 := by
    simpa [prefixWord, tailWord_3881609, baseEnd_3881609] using wordTrace_append hprefix tailTrace_3881609
  have hstable : (prefixWord ++ tailWord_3881609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881609).length < 2 ^ (prefixWord ++ tailWord_3881609).sum := by decide
  have hdescent : baseEnd_3881609 < baseStart_3881609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881700 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_3881700 : Nat := 118140960795 + 3881700 * 2 ^ 59
def prefixEnd_3881700 : Nat := 4983230072969 + 3 ^ 40 * 3881700 * 2
def baseEnd_3881700 : Nat := 1993177856557568064598393

theorem tailTrace_3881700 : CollatzResearch.WordTrace tailWord_3881700 prefixEnd_3881700 1993177856557568064598393 := by
  unfold tailWord_3881700
  simp only [CollatzResearch.WordTrace]
  refine ⟨70788615018635658212817277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94384820024847544283756369 70788615018635658212817277)
  ·
    refine ⟨26545730631988371829806479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70788615018635658212817277 26545730631988371829806479)
    ·
      refine ⟨39818595947982557744709719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26545730631988371829806479 39818595947982557744709719)
      ·
        refine ⟨59727893921973836617064579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39818595947982557744709719 59727893921973836617064579)
        ·
          refine ⟨89591840882960754925596869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59727893921973836617064579 89591840882960754925596869)
          ·
            refine ⟨16798470165555141548549413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89591840882960754925596869 16798470165555141548549413)
            ·
              refine ⟨3149713156041589040353015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16798470165555141548549413 3149713156041589040353015)
              ·
                refine ⟨4724569734062383560529523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149713156041589040353015 4724569734062383560529523)
                ·
                  refine ⟨7086854601093575340794285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724569734062383560529523 7086854601093575340794285)
                  ·
                    refine ⟨2657570475410090752797857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7086854601093575340794285 2657570475410090752797857)
                    ·
                      refine ⟨1993177856557568064598393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657570475410090752797857 1993177856557568064598393)
                      ·
                        rfl

theorem cell23_3881700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_3881700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881700 prefixEnd_3881700 := by exact prefixLift 3881700
  have htrace : WordTrace (prefixWord ++ tailWord_3881700) baseStart_3881700 baseEnd_3881700 := by
    simpa [prefixWord, tailWord_3881700, baseEnd_3881700] using wordTrace_append hprefix tailTrace_3881700
  have hstable : (prefixWord ++ tailWord_3881700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881700).length < 2 ^ (prefixWord ++ tailWord_3881700).sum := by decide
  have hdescent : baseEnd_3881700 < baseStart_3881700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881713 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_3881713 : Nat := 118140960795 + 3881713 * 2 ^ 59
def prefixEnd_3881713 : Nat := 4983230072969 + 3 ^ 40 * 3881713 * 2
def baseEnd_3881713 : Nat := 1993184531806076513735833

theorem tailTrace_3881713 : CollatzResearch.WordTrace tailWord_3881713 prefixEnd_3881713 1993184531806076513735833 := by
  unfold tailWord_3881713
  simp only [CollatzResearch.WordTrace]
  refine ⟨141577704186224219645857793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94385136124149479763905195 141577704186224219645857793)
  ·
    refine ⟨106183278139668164734393345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141577704186224219645857793 106183278139668164734393345)
    ·
      refine ⟨79637458604751123550795009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106183278139668164734393345 79637458604751123550795009)
      ·
        refine ⟨59728093953563342663096257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79637458604751123550795009 59728093953563342663096257)
        ·
          refine ⟨44796070465172506997322193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59728093953563342663096257 44796070465172506997322193)
          ·
            refine ⟨33597052848879380247991645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44796070465172506997322193 33597052848879380247991645)
            ·
              refine ⟨12598894818329767592996867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33597052848879380247991645 12598894818329767592996867)
              ·
                refine ⟨18898342227494651389495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12598894818329767592996867 18898342227494651389495301)
                ·
                  refine ⟨3543439167655247135530369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18898342227494651389495301 3543439167655247135530369)
                  ·
                    refine ⟨2657579375741435351647777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3543439167655247135530369 2657579375741435351647777)
                    ·
                      refine ⟨1993184531806076513735833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657579375741435351647777 1993184531806076513735833)
                      ·
                        rfl

theorem cell23_3881713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_3881713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881713 prefixEnd_3881713 := by exact prefixLift 3881713
  have htrace : WordTrace (prefixWord ++ tailWord_3881713) baseStart_3881713 baseEnd_3881713 := by
    simpa [prefixWord, tailWord_3881713, baseEnd_3881713] using wordTrace_append hprefix tailTrace_3881713
  have hstable : (prefixWord ++ tailWord_3881713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881713).length < 2 ^ (prefixWord ++ tailWord_3881713).sum := by decide
  have hdescent : baseEnd_3881713 < baseStart_3881713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881730 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_3881730 : Nat := 118140960795 + 3881730 * 2 ^ 59
def prefixEnd_3881730 : Nat := 4983230072969 + 3 ^ 40 * 3881730 * 2
def baseEnd_3881730 : Nat := 1993193260977202947223255

theorem tailTrace_3881730 : CollatzResearch.WordTrace tailWord_3881730 prefixEnd_3881730 1993193260977202947223255 := by
  unfold tailWord_3881730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35394581056790657887306661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94385549484775087699484429 35394581056790657887306661)
  ·
    refine ⟨6636483948148248353869999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35394581056790657887306661 6636483948148248353869999)
    ·
      refine ⟨9954725922222372530804999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636483948148248353869999 9954725922222372530804999)
      ·
        refine ⟨14932088883333558796207499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954725922222372530804999 14932088883333558796207499)
        ·
          refine ⟨22398133325000338194311249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14932088883333558796207499 22398133325000338194311249)
          ·
            refine ⟨16798599993750253645733437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22398133325000338194311249 16798599993750253645733437)
            ·
              refine ⟨6299474997656345117150039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16798599993750253645733437 6299474997656345117150039)
              ·
                refine ⟨9449212496484517675725059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299474997656345117150039 9449212496484517675725059)
                ·
                  refine ⟨14173818744726776513587589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449212496484517675725059 14173818744726776513587589)
                  ·
                    refine ⟨2657591014636270596297673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14173818744726776513587589 2657591014636270596297673)
                    ·
                      refine ⟨1993193260977202947223255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657591014636270596297673 1993193260977202947223255)
                      ·
                        rfl

theorem cell23_3881730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_3881730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881730 prefixEnd_3881730 := by exact prefixLift 3881730
  have htrace : WordTrace (prefixWord ++ tailWord_3881730) baseStart_3881730 baseEnd_3881730 := by
    simpa [prefixWord, tailWord_3881730, baseEnd_3881730] using wordTrace_append hprefix tailTrace_3881730
  have hstable : (prefixWord ++ tailWord_3881730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881730).length < 2 ^ (prefixWord ++ tailWord_3881730).sum := by decide
  have hdescent : baseEnd_3881730 < baseStart_3881730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881749 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3881749 : Nat := 118140960795 + 3881749 * 2 ^ 59
def prefixEnd_3881749 : Nat := 4983230072969 + 3 ^ 40 * 3881749 * 2
def baseEnd_3881749 : Nat := 664401005703212790961889

theorem tailTrace_3881749 : CollatzResearch.WordTrace tailWord_3881749 prefixEnd_3881749 664401005703212790961889 := by
  unfold tailWord_3881749
  simp only [CollatzResearch.WordTrace]
  refine ⟨141579017214093797794168301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94386011476062531862778867 141579017214093797794168301)
  ·
    refine ⟨53092131455285174172813113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141579017214093797794168301 53092131455285174172813113)
    ·
      refine ⟨39819098591463880629609835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53092131455285174172813113 39819098591463880629609835)
      ·
        refine ⟨59728647887195820944414753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39819098591463880629609835 59728647887195820944414753)
        ·
          refine ⟨44796485915396865708311065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59728647887195820944414753 44796485915396865708311065)
          ·
            refine ⟨33597364436547649281233299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44796485915396865708311065 33597364436547649281233299)
            ·
              refine ⟨50396046654821473921849949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33597364436547649281233299 50396046654821473921849949)
              ·
                refine ⟨18898517495558052720693731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50396046654821473921849949 18898517495558052720693731)
                ·
                  refine ⟨28347776243337079081040597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18898517495558052720693731 28347776243337079081040597)
                  ·
                    refine ⟨664401005703212790961889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28347776243337079081040597 664401005703212790961889)
                    ·
                      rfl

theorem cell23_3881749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3881749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881749 prefixEnd_3881749 := by exact prefixLift 3881749
  have htrace : WordTrace (prefixWord ++ tailWord_3881749) baseStart_3881749 baseEnd_3881749 := by
    simpa [prefixWord, tailWord_3881749, baseEnd_3881749] using wordTrace_append hprefix tailTrace_3881749
  have hstable : (prefixWord ++ tailWord_3881749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881749).length < 2 ^ (prefixWord ++ tailWord_3881749).sum := by decide
  have hdescent : baseEnd_3881749 < baseStart_3881749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881770 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_3881770 : Nat := 118140960795 + 3881770 * 2 ^ 59
def prefixEnd_3881770 : Nat := 4983230072969 + 3 ^ 40 * 3881770 * 2
def baseEnd_3881770 : Nat := 221468200022598087858119

theorem tailTrace_3881770 : CollatzResearch.WordTrace tailWord_3881770 prefixEnd_3881770 221468200022598087858119 := by
  unfold tailWord_3881770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35394945786754429595170691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94386522098011812253788509 35394945786754429595170691)
  ·
    refine ⟨53092418680131644392756037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35394945786754429595170691 53092418680131644392756037)
    ·
      refine ⟨9954828502524683323641757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53092418680131644392756037 9954828502524683323641757)
      ·
        refine ⟨3733060688446756246365659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9954828502524683323641757 3733060688446756246365659)
        ·
          refine ⟨5599591032670134369548489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733060688446756246365659 5599591032670134369548489)
          ·
            refine ⟨4199693274502600777161367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5599591032670134369548489 4199693274502600777161367)
            ·
              refine ⟨6299539911753901165742051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199693274502600777161367 6299539911753901165742051)
              ·
                refine ⟨9449309867630851748613077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299539911753901165742051 9449309867630851748613077)
                ·
                  refine ⟨221468200022598087858119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9449309867630851748613077 221468200022598087858119)
                  ·
                    rfl

theorem cell23_3881770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_3881770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881770 prefixEnd_3881770 := by exact prefixLift 3881770
  have htrace : WordTrace (prefixWord ++ tailWord_3881770) baseStart_3881770 baseEnd_3881770 := by
    simpa [prefixWord, tailWord_3881770, baseEnd_3881770] using wordTrace_append hprefix tailTrace_3881770
  have hstable : (prefixWord ++ tailWord_3881770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881770).length < 2 ^ (prefixWord ++ tailWord_3881770).sum := by decide
  have hdescent : baseEnd_3881770 < baseStart_3881770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881799 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3881799 : Nat := 118140960795 + 3881799 * 2 ^ 59
def prefixEnd_3881799 : Nat := 4983230072969 + 3 ^ 40 * 3881799 * 2
def baseEnd_3881799 : Nat := 1993228691142363177260437

theorem tailTrace_3881799 : CollatzResearch.WordTrace tailWord_3881799 prefixEnd_3881799 1993228691142363177260437 := by
  unfold tailWord_3881799
  simp only [CollatzResearch.WordTrace]
  refine ⟨141580840863912656333488451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94387227242608437555658967 141580840863912656333488451)
  ·
    refine ⟨212371261295868984500232677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141580840863912656333488451 212371261295868984500232677)
    ·
      refine ⟨39819611492975434593793627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212371261295868984500232677 39819611492975434593793627)
      ·
        refine ⟨59729417239463151890690441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39819611492975434593793627 59729417239463151890690441)
        ·
          refine ⟨44797062929597363918017831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59729417239463151890690441 44797062929597363918017831)
          ·
            refine ⟨67195594394396045877026747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44797062929597363918017831 67195594394396045877026747)
            ·
              refine ⟨100793391591594068815540121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67195594394396045877026747 100793391591594068815540121)
              ·
                refine ⟨75595043693695551611655091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100793391591594068815540121 75595043693695551611655091)
                ·
                  refine ⟨113392565540543327417482637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75595043693695551611655091 113392565540543327417482637)
                  ·
                    refine ⟨42522212077703747781555989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113392565540543327417482637 42522212077703747781555989)
                    ·
                      refine ⟨1993228691142363177260437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42522212077703747781555989 1993228691142363177260437)
                      ·
                        rfl

theorem cell23_3881799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3881799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881799 prefixEnd_3881799 := by exact prefixLift 3881799
  have htrace : WordTrace (prefixWord ++ tailWord_3881799) baseStart_3881799 baseEnd_3881799 := by
    simpa [prefixWord, tailWord_3881799, baseEnd_3881799] using wordTrace_append hprefix tailTrace_3881799
  have hstable : (prefixWord ++ tailWord_3881799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881799).length < 2 ^ (prefixWord ++ tailWord_3881799).sum := by decide
  have hdescent : baseEnd_3881799 < baseStart_3881799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881806 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3881806 : Nat := 118140960795 + 3881806 * 2 ^ 59
def prefixEnd_3881806 : Nat := 4983230072969 + 3 ^ 40 * 3881806 * 2
def baseEnd_3881806 : Nat := 1993232285506944649872905

theorem tailTrace_3881806 : CollatzResearch.WordTrace tailWord_3881806 prefixEnd_3881806 1993232285506944649872905 := by
  unfold tailWord_3881806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697637021860912066124159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94387397449924864352662181 17697637021860912066124159)
  ·
    refine ⟨26546455532791368099186239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17697637021860912066124159 26546455532791368099186239)
    ·
      refine ⟨39819683299187052148779359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26546455532791368099186239 39819683299187052148779359)
      ·
        refine ⟨59729524948780578223169039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39819683299187052148779359 59729524948780578223169039)
        ·
          refine ⟨89594287423170867334753559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59729524948780578223169039 89594287423170867334753559)
          ·
            refine ⟨134391431134756301002130339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89594287423170867334753559 134391431134756301002130339)
            ·
              refine ⟨201587146702134451503195509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134391431134756301002130339 201587146702134451503195509)
              ·
                refine ⟨18898795003325104828424579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201587146702134451503195509 18898795003325104828424579)
                ·
                  refine ⟨28348192504987657242636869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18898795003325104828424579 28348192504987657242636869)
                  ·
                    refine ⟨5315286094685185732994413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28348192504987657242636869 5315286094685185732994413)
                    ·
                      refine ⟨1993232285506944649872905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315286094685185732994413 1993232285506944649872905)
                      ·
                        rfl

theorem cell23_3881806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3881806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881806 prefixEnd_3881806 := by exact prefixLift 3881806
  have htrace : WordTrace (prefixWord ++ tailWord_3881806) baseStart_3881806 baseEnd_3881806 := by
    simpa [prefixWord, tailWord_3881806, baseEnd_3881806] using wordTrace_append hprefix tailTrace_3881806
  have hstable : (prefixWord ++ tailWord_3881806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881806).length < 2 ^ (prefixWord ++ tailWord_3881806).sum := by decide
  have hdescent : baseEnd_3881806 < baseStart_3881806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881853 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_3881853 : Nat := 118140960795 + 3881853 * 2 ^ 59
def prefixEnd_3881853 : Nat := 4983230072969 + 3 ^ 40 * 3881853 * 2
def baseEnd_3881853 : Nat := 1993256419097705965985189

theorem tailTrace_3881853 : CollatzResearch.WordTrace tailWord_3881853 prefixEnd_3881853 1993256419097705965985189 := by
  unfold tailWord_3881853
  simp only [CollatzResearch.WordTrace]
  refine ⟨141582810405717023555954213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94388540270478015703969475 141582810405717023555954213)
  ·
    refine ⟨26546776951071941916741415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141582810405717023555954213 26546776951071941916741415)
    ·
      refine ⟨39820165426607912875112123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26546776951071941916741415 39820165426607912875112123)
      ·
        refine ⟨59730248139911869312668185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39820165426607912875112123 59730248139911869312668185)
        ·
          refine ⟨44797686104933901984501139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59730248139911869312668185 44797686104933901984501139)
          ·
            refine ⟨67196529157400852976751709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44797686104933901984501139 67196529157400852976751709)
            ·
              refine ⟨25198698434025319866281891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67196529157400852976751709 25198698434025319866281891)
              ·
                refine ⟨37798047651037979799422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25198698434025319866281891 37798047651037979799422837)
                ·
                  refine ⟨3543566967284810606195891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37798047651037979799422837 3543566967284810606195891)
                  ·
                    refine ⟨5315350450927215909293837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3543566967284810606195891 5315350450927215909293837)
                    ·
                      refine ⟨1993256419097705965985189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315350450927215909293837 1993256419097705965985189)
                      ·
                        rfl

theorem cell23_3881853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_3881853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881853 prefixEnd_3881853 := by exact prefixLift 3881853
  have htrace : WordTrace (prefixWord ++ tailWord_3881853) baseStart_3881853 baseEnd_3881853 := by
    simpa [prefixWord, tailWord_3881853, baseEnd_3881853] using wordTrace_append hprefix tailTrace_3881853
  have hstable : (prefixWord ++ tailWord_3881853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881853).length < 2 ^ (prefixWord ++ tailWord_3881853).sum := by decide
  have hdescent : baseEnd_3881853 < baseStart_3881853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881854 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3881854 : Nat := 118140960795 + 3881854 * 2 ^ 59
def prefixEnd_3881854 : Nat := 4983230072969 + 3 ^ 40 * 3881854 * 2
def baseEnd_3881854 : Nat := 1993256932578360462072685

theorem tailTrace_3881854 : CollatzResearch.WordTrace tailWord_3881854 prefixEnd_3881854 1993256932578360462072685 := by
  unfold tailWord_3881854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697855859839175090842577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94388564585808933817827077 17697855859839175090842577)
  ·
    refine ⟨13273391894879381318131933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17697855859839175090842577 13273391894879381318131933)
    ·
      refine ⟨4977521960579767994299475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13273391894879381318131933 4977521960579767994299475)
      ·
        refine ⟨7466282940869651991449213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977521960579767994299475 7466282940869651991449213)
        ·
          refine ⟨2799856102826119496793455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7466282940869651991449213 2799856102826119496793455)
          ·
            refine ⟨4199784154239179245190183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799856102826119496793455 4199784154239179245190183)
            ·
              refine ⟨6299676231358768867785275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199784154239179245190183 6299676231358768867785275)
              ·
                refine ⟨9449514347038153301677913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299676231358768867785275 9449514347038153301677913)
                ·
                  refine ⟨7087135760278614976258435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449514347038153301677913 7087135760278614976258435)
                  ·
                    refine ⟨10630703640417922464387653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087135760278614976258435 10630703640417922464387653)
                    ·
                      refine ⟨1993256932578360462072685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10630703640417922464387653 1993256932578360462072685)
                      ·
                        rfl

theorem cell23_3881854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3881854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881854 prefixEnd_3881854 := by exact prefixLift 3881854
  have htrace : WordTrace (prefixWord ++ tailWord_3881854) baseStart_3881854 baseEnd_3881854 := by
    simpa [prefixWord, tailWord_3881854, baseEnd_3881854] using wordTrace_append hprefix tailTrace_3881854
  have hstable : (prefixWord ++ tailWord_3881854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881854).length < 2 ^ (prefixWord ++ tailWord_3881854).sum := by decide
  have hdescent : baseEnd_3881854 < baseStart_3881854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881887 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 1, 1, 3]
def baseStart_3881887 : Nat := 118140960795 + 3881887 * 2 ^ 59
def prefixEnd_3881887 : Nat := 4983230072969 + 3 ^ 40 * 3881887 * 2
def baseEnd_3881887 : Nat := 1993273877439958832960033

theorem tailTrace_3881887 : CollatzResearch.WordTrace tailWord_3881887 prefixEnd_3881887 1993273877439958832960033 := by
  unfold tailWord_3881887
  simp only [CollatzResearch.WordTrace]
  refine ⟨141584050487593847362691915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94389366991729231575127943 141584050487593847362691915)
  ·
    refine ⟨212376075731390771044037873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141584050487593847362691915 212376075731390771044037873)
    ·
      refine ⟨159282056798543078283028405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212376075731390771044037873 159282056798543078283028405)
      ·
        refine ⟨14932692824863413589033913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159282056798543078283028405 14932692824863413589033913)
        ·
          refine ⟨11199519618647560191775435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932692824863413589033913 11199519618647560191775435)
          ·
            refine ⟨16799279427971340287663153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199519618647560191775435 16799279427971340287663153)
            ·
              refine ⟨12599459570978505215747365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16799279427971340287663153 12599459570978505215747365)
              ·
                refine ⟨2362398669558469727952631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12599459570978505215747365 2362398669558469727952631)
                ·
                  refine ⟨3543598004337704591928947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362398669558469727952631 3543598004337704591928947)
                  ·
                    refine ⟨5315397006506556887893421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3543598004337704591928947 5315397006506556887893421)
                    ·
                      refine ⟨1993273877439958832960033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315397006506556887893421 1993273877439958832960033)
                      ·
                        rfl

theorem cell23_3881887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_3881887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881887 prefixEnd_3881887 := by exact prefixLift 3881887
  have htrace : WordTrace (prefixWord ++ tailWord_3881887) baseStart_3881887 baseEnd_3881887 := by
    simpa [prefixWord, tailWord_3881887, baseEnd_3881887] using wordTrace_append hprefix tailTrace_3881887
  have hstable : (prefixWord ++ tailWord_3881887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881887).length < 2 ^ (prefixWord ++ tailWord_3881887).sum := by decide
  have hdescent : baseEnd_3881887 < baseStart_3881887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881953 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_3881953 : Nat := 118140960795 + 3881953 * 2 ^ 59
def prefixEnd_3881953 : Nat := 4983230072969 + 3 ^ 40 * 3881953 * 2
def baseEnd_3881953 : Nat := 1993307767163155574734729

theorem tailTrace_3881953 : CollatzResearch.WordTrace tailWord_3881953 prefixEnd_3881953 1993307767163155574734729 := by
  unfold tailWord_3881953
  simp only [CollatzResearch.WordTrace]
  refine ⟨141586457705354740634594513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94390971803569827089729675 141586457705354740634594513)
  ·
    refine ⟨106189843279016055475945885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141586457705354740634594513 106189843279016055475945885)
    ·
      refine ⟨39821191229631020803479707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106189843279016055475945885 39821191229631020803479707)
      ·
        refine ⟨59731786844446531205219561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39821191229631020803479707 59731786844446531205219561)
        ·
          refine ⟨44798840133334898403914671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59731786844446531205219561 44798840133334898403914671)
          ·
            refine ⟨67198260200002347605872007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44798840133334898403914671 67198260200002347605872007)
            ·
              refine ⟨100797390300003521408808011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67198260200002347605872007 100797390300003521408808011)
              ·
                refine ⟨151196085450005282113212017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100797390300003521408808011 151196085450005282113212017)
                ·
                  refine ⟨113397064087503961584909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151196085450005282113212017 113397064087503961584909013)
                  ·
                    refine ⟨2657743689550874099646305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 113397064087503961584909013 2657743689550874099646305)
                    ·
                      refine ⟨1993307767163155574734729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657743689550874099646305 1993307767163155574734729)
                      ·
                        rfl

theorem cell23_3881953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_3881953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881953 prefixEnd_3881953 := by exact prefixLift 3881953
  have htrace : WordTrace (prefixWord ++ tailWord_3881953) baseStart_3881953 baseEnd_3881953 := by
    simpa [prefixWord, tailWord_3881953, baseEnd_3881953] using wordTrace_append hprefix tailTrace_3881953
  have hstable : (prefixWord ++ tailWord_3881953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881953).length < 2 ^ (prefixWord ++ tailWord_3881953).sum := by decide
  have hdescent : baseEnd_3881953 < baseStart_3881953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881954 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3881954 : Nat := 118140960795 + 3881954 * 2 ^ 59
def prefixEnd_3881954 : Nat := 4983230072969 + 3 ^ 40 * 3881954 * 2
def baseEnd_3881954 : Nat := 664436093547936690274075

theorem tailTrace_3881954 : CollatzResearch.WordTrace tailWord_3881954 prefixEnd_3881954 664436093547936690274075 := by
  unfold tailWord_3881954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396623544587779451345229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94390996118900745203587277 35396623544587779451345229)
  ·
    refine ⟨13273733829220417294254461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35396623544587779451345229 13273733829220417294254461)
    ·
      refine ⟨4977650185957656485345423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13273733829220417294254461 4977650185957656485345423)
      ·
        refine ⟨7466475278936484728018135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977650185957656485345423 7466475278936484728018135)
        ·
          refine ⟨11199712918404727092027203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466475278936484728018135 11199712918404727092027203)
          ·
            refine ⟨16799569377607090638040805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199712918404727092027203 16799569377607090638040805)
            ·
              refine ⟨3149919258301329494632651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16799569377607090638040805 3149919258301329494632651)
              ·
                refine ⟨4724878887451994241948977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149919258301329494632651 4724878887451994241948977)
                ·
                  refine ⟨3543659165588995681461733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724878887451994241948977 3543659165588995681461733)
                  ·
                    refine ⟨664436093547936690274075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543659165588995681461733 664436093547936690274075)
                    ·
                      rfl

theorem cell23_3881954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3881954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881954 prefixEnd_3881954 := by exact prefixLift 3881954
  have htrace : WordTrace (prefixWord ++ tailWord_3881954) baseStart_3881954 baseEnd_3881954 := by
    simpa [prefixWord, tailWord_3881954, baseEnd_3881954] using wordTrace_append hprefix tailTrace_3881954
  have hstable : (prefixWord ++ tailWord_3881954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881954).length < 2 ^ (prefixWord ++ tailWord_3881954).sum := by decide
  have hdescent : baseEnd_3881954 < baseStart_3881954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881956 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3881956 : Nat := 118140960795 + 3881956 * 2 ^ 59
def prefixEnd_3881956 : Nat := 4983230072969 + 3 ^ 40 * 3881956 * 2
def baseEnd_3881956 : Nat := 1993309307605119062997215

theorem tailTrace_3881956 : CollatzResearch.WordTrace tailWord_3881956 prefixEnd_3881956 1993309307605119062997215 := by
  unfold tailWord_3881956
  simp only [CollatzResearch.WordTrace]
  refine ⟨70793283562171936073476861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94391044749562581431302481 70793283562171936073476861)
  ·
    refine ⟨26547481335814476027553823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70793283562171936073476861 26547481335814476027553823)
    ·
      refine ⟨39821222003721714041330735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26547481335814476027553823 39821222003721714041330735)
      ·
        refine ⟨59731833005582571061996103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39821222003721714041330735 59731833005582571061996103)
        ·
          refine ⟨89597749508373856592994155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59731833005582571061996103 89597749508373856592994155)
          ·
            refine ⟨134396624262560784889491233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89597749508373856592994155 134396624262560784889491233)
            ·
              refine ⟨100797468196920588667118425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134396624262560784889491233 100797468196920588667118425)
              ·
                refine ⟨75598101147690441500338819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100797468196920588667118425 75598101147690441500338819)
                ·
                  refine ⟨113397151721535662250508229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75598101147690441500338819 113397151721535662250508229)
                  ·
                    refine ⟨21261965947787936671970293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113397151721535662250508229 21261965947787936671970293)
                    ·
                      refine ⟨1993309307605119062997215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21261965947787936671970293 1993309307605119062997215)
                      ·
                        rfl

theorem cell23_3881956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3881956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881956 prefixEnd_3881956 := by exact prefixLift 3881956
  have htrace : WordTrace (prefixWord ++ tailWord_3881956) baseStart_3881956 baseEnd_3881956 := by
    simpa [prefixWord, tailWord_3881956, baseEnd_3881956] using wordTrace_append hprefix tailTrace_3881956
  have hstable : (prefixWord ++ tailWord_3881956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881956).length < 2 ^ (prefixWord ++ tailWord_3881956).sum := by decide
  have hdescent : baseEnd_3881956 < baseStart_3881956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3881976 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_3881976 : Nat := 118140960795 + 3881976 * 2 ^ 59
def prefixEnd_3881976 : Nat := 4983230072969 + 3 ^ 40 * 3881976 * 2
def baseEnd_3881976 : Nat := 664439859072736328249041

theorem tailTrace_3881976 : CollatzResearch.WordTrace tailWord_3881976 prefixEnd_3881976 664439859072736328249041 := by
  unfold tailWord_3881976
  simp only [CollatzResearch.WordTrace]
  refine ⟨70793648292135707781340891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94391531056180943708454521 70793648292135707781340891)
  ·
    refine ⟨106190472438203561672011337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70793648292135707781340891 106190472438203561672011337)
    ·
      refine ⟨79642854328652671254008503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106190472438203561672011337 79642854328652671254008503)
      ·
        refine ⟨119464281492979006881012755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79642854328652671254008503 119464281492979006881012755)
        ·
          refine ⟨179196422239468510321519133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119464281492979006881012755 179196422239468510321519133)
          ·
            refine ⟨67198658339800691370569675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179196422239468510321519133 67198658339800691370569675)
            ·
              refine ⟨100797987509701037055854513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67198658339800691370569675 100797987509701037055854513)
              ·
                refine ⟨75598490632275777791890885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100797987509701037055854513 75598490632275777791890885)
                ·
                  refine ⟨14174716993551708335979541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75598490632275777791890885 14174716993551708335979541)
                  ·
                    refine ⟨664439859072736328249041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14174716993551708335979541 664439859072736328249041)
                    ·
                      rfl

theorem cell23_3881976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_3881976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3881976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3881976 prefixEnd_3881976 := by exact prefixLift 3881976
  have htrace : WordTrace (prefixWord ++ tailWord_3881976) baseStart_3881976 baseEnd_3881976 := by
    simpa [prefixWord, tailWord_3881976, baseEnd_3881976] using wordTrace_append hprefix tailTrace_3881976
  have hstable : (prefixWord ++ tailWord_3881976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3881976).length < 2 ^ (prefixWord ++ tailWord_3881976).sum := by decide
  have hdescent : baseEnd_3881976 < baseStart_3881976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3881976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882017 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3882017 : Nat := 118140960795 + 3882017 * 2 ^ 59
def prefixEnd_3882017 : Nat := 4983230072969 + 3 ^ 40 * 3882017 * 2
def baseEnd_3882017 : Nat := 1993340629925043324334435

theorem tailTrace_3882017 : CollatzResearch.WordTrace tailWord_3882017 prefixEnd_3882017 1993340629925043324334435 := by
  unfold tailWord_3882017
  simp only [CollatzResearch.WordTrace]
  refine ⟨141588791977122879564924305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94392527984748586376616203 141588791977122879564924305)
  ·
    refine ⟨106191593982842159673693229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141588791977122879564924305 106191593982842159673693229)
    ·
      refine ⟨39821847743565809877634961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106191593982842159673693229 39821847743565809877634961)
      ·
        refine ⟨29866385807674357408226221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39821847743565809877634961 29866385807674357408226221)
        ·
          refine ⟨11199894677877884028084833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29866385807674357408226221 11199894677877884028084833)
          ·
            refine ⟨8399921008408413021063625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199894677877884028084833 8399921008408413021063625)
            ·
              refine ⟨6299940756306309765797719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399921008408413021063625 6299940756306309765797719)
              ·
                refine ⟨9449911134459464648696579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299940756306309765797719 9449911134459464648696579)
                ·
                  refine ⟨14174866701689196973044869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449911134459464648696579 14174866701689196973044869)
                  ·
                    refine ⟨2657787506566724432445913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14174866701689196973044869 2657787506566724432445913)
                    ·
                      refine ⟨1993340629925043324334435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657787506566724432445913 1993340629925043324334435)
                      ·
                        rfl

theorem cell23_3882017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3882017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882017 prefixEnd_3882017 := by exact prefixLift 3882017
  have htrace : WordTrace (prefixWord ++ tailWord_3882017) baseStart_3882017 baseEnd_3882017 := by
    simpa [prefixWord, tailWord_3882017, baseEnd_3882017] using wordTrace_append hprefix tailTrace_3882017
  have hstable : (prefixWord ++ tailWord_3882017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882017).length < 2 ^ (prefixWord ++ tailWord_3882017).sum := by decide
  have hdescent : baseEnd_3882017 < baseStart_3882017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882033 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3882033 : Nat := 118140960795 + 3882033 * 2 ^ 59
def prefixEnd_3882033 : Nat := 4983230072969 + 3 ^ 40 * 3882033 * 2
def baseEnd_3882033 : Nat := 1993348845615515261734361

theorem tailTrace_3882033 : CollatzResearch.WordTrace tailWord_3882033 prefixEnd_3882033 1993348845615515261734361 := by
  unfold tailWord_3882033
  simp only [CollatzResearch.WordTrace]
  refine ⟨141589375545064914297506753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94392917030043276198337835 141589375545064914297506753)
  ·
    refine ⟨106192031658798685723130065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141589375545064914297506753 106192031658798685723130065)
    ·
      refine ⟨79644023744099014292347549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106192031658798685723130065 79644023744099014292347549)
      ·
        refine ⟨29866508904037130359630331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79644023744099014292347549 29866508904037130359630331)
        ·
          refine ⟨44799763356055695539445497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29866508904037130359630331 44799763356055695539445497)
          ·
            refine ⟨33599822517041771654584123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44799763356055695539445497 33599822517041771654584123)
            ·
              refine ⟨50399733775562657481876185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33599822517041771654584123 50399733775562657481876185)
              ·
                refine ⟨37799800331671993111407139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50399733775562657481876185 37799800331671993111407139)
                ·
                  refine ⟨56699700497507989667110709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37799800331671993111407139 56699700497507989667110709)
                  ·
                    refine ⟨5315596921641374031291629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56699700497507989667110709 5315596921641374031291629)
                    ·
                      refine ⟨1993348845615515261734361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5315596921641374031291629 1993348845615515261734361)
                      ·
                        rfl

theorem cell23_3882033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3882033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882033 prefixEnd_3882033 := by exact prefixLift 3882033
  have htrace : WordTrace (prefixWord ++ tailWord_3882033) baseStart_3882033 baseEnd_3882033 := by
    simpa [prefixWord, tailWord_3882033, baseEnd_3882033] using wordTrace_append hprefix tailTrace_3882033
  have hstable : (prefixWord ++ tailWord_3882033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882033).length < 2 ^ (prefixWord ++ tailWord_3882033).sum := by decide
  have hdescent : baseEnd_3882033 < baseStart_3882033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882040 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 5]
def baseStart_3882040 : Nat := 118140960795 + 3882040 * 2 ^ 59
def prefixEnd_3882040 : Nat := 4983230072969 + 3 ^ 40 * 3882040 * 2
def baseEnd_3882040 : Nat := 221483604442232970482981

theorem tailTrace_3882040 : CollatzResearch.WordTrace tailWord_3882040 prefixEnd_3882040 221483604442232970482981 := by
  unfold tailWord_3882040
  simp only [CollatzResearch.WordTrace]
  refine ⟨70794815428019777246505787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94393087237359702995341049 70794815428019777246505787)
  ·
    refine ⟨106192223142029665869758681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70794815428019777246505787 106192223142029665869758681)
    ·
      refine ⟨79644167356522249402319011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106192223142029665869758681 79644167356522249402319011)
      ·
        refine ⟨119466251034783374103478517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79644167356522249402319011 119466251034783374103478517)
        ·
          refine ⟨11199961034510941322201111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119466251034783374103478517 11199961034510941322201111)
          ·
            refine ⟨16799941551766411983301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199961034510941322201111 16799941551766411983301667)
            ·
              refine ⟨25199912327649617974952501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16799941551766411983301667 25199912327649617974952501)
              ·
                refine ⟨2362491780717151685151797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25199912327649617974952501 2362491780717151685151797)
                ·
                  refine ⟨221483604442232970482981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362491780717151685151797 221483604442232970482981)
                  ·
                    rfl

theorem cell23_3882040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 5].length) (baseStart_3882040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882040 prefixEnd_3882040 := by exact prefixLift 3882040
  have htrace : WordTrace (prefixWord ++ tailWord_3882040) baseStart_3882040 baseEnd_3882040 := by
    simpa [prefixWord, tailWord_3882040, baseEnd_3882040] using wordTrace_append hprefix tailTrace_3882040
  have hstable : (prefixWord ++ tailWord_3882040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882040).length < 2 ^ (prefixWord ++ tailWord_3882040).sum := by decide
  have hdescent : baseEnd_3882040 < baseStart_3882040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882053 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3882053 : Nat := 118140960795 + 3882053 * 2 ^ 59
def prefixEnd_3882053 : Nat := 4983230072969 + 3 ^ 40 * 3882053 * 2
def baseEnd_3882053 : Nat := 664453038409535061161423

theorem tailTrace_3882053 : CollatzResearch.WordTrace tailWord_3882053 prefixEnd_3882053 664453038409535061161423 := by
  unfold tailWord_3882053
  simp only [CollatzResearch.WordTrace]
  refine ⟨141590105004992457713234813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94393403336661638475489875 141590105004992457713234813)
  ·
    refine ⟨53096289376872171642463055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141590105004992457713234813 53096289376872171642463055)
    ·
      refine ⟨79644434065308257463694583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53096289376872171642463055 79644434065308257463694583)
      ·
        refine ⟨119466651097962386195541875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79644434065308257463694583 119466651097962386195541875)
        ·
          refine ⟨179199976646943579293312813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119466651097962386195541875 179199976646943579293312813)
          ·
            refine ⟨67199991242603842234992305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179199976646943579293312813 67199991242603842234992305)
            ·
              refine ⟨50399993431952881676244229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67199991242603842234992305 50399993431952881676244229)
              ·
                refine ⟨9449998768491165314295793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50399993431952881676244229 9449998768491165314295793)
                ·
                  refine ⟨7087499076368373985721845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9449998768491165314295793 7087499076368373985721845)
                  ·
                    refine ⟨664453038409535061161423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7087499076368373985721845 664453038409535061161423)
                    ·
                      rfl

theorem cell23_3882053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3882053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882053 prefixEnd_3882053 := by exact prefixLift 3882053
  have htrace : WordTrace (prefixWord ++ tailWord_3882053) baseStart_3882053 baseEnd_3882053 := by
    simpa [prefixWord, tailWord_3882053, baseEnd_3882053] using wordTrace_append hprefix tailTrace_3882053
  have hstable : (prefixWord ++ tailWord_3882053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882053).length < 2 ^ (prefixWord ++ tailWord_3882053).sum := by decide
  have hdescent : baseEnd_3882053 < baseStart_3882053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882073 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_3882073 : Nat := 118140960795 + 3882073 * 2 ^ 59
def prefixEnd_3882073 : Nat := 4983230072969 + 3 ^ 40 * 3882073 * 2
def baseEnd_3882073 : Nat := 1993369384841695105234177

theorem tailTrace_3882073 : CollatzResearch.WordTrace tailWord_3882073 prefixEnd_3882073 1993369384841695105234177 := by
  unfold tailWord_3882073
  simp only [CollatzResearch.WordTrace]
  refine ⟨141590834464920001128962873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94393889643280000752641915 141590834464920001128962873)
  ·
    refine ⟨106193125848690000846722155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141590834464920001128962873 106193125848690000846722155)
    ·
      refine ⟨159289688773035001270083233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106193125848690000846722155 159289688773035001270083233)
      ·
        refine ⟨119467266579776250952562425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159289688773035001270083233 119467266579776250952562425)
        ·
          refine ⟨89600449934832188214421819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119467266579776250952562425 89600449934832188214421819)
          ·
            refine ⟨134400674902248282321632729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89600449934832188214421819 134400674902248282321632729)
            ·
              refine ⟨100800506176686211741224547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134400674902248282321632729 100800506176686211741224547)
              ·
                refine ⟨151200759265029317611836821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100800506176686211741224547 151200759265029317611836821)
                ·
                  refine ⟨7087535590548249263054851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151200759265029317611836821 7087535590548249263054851)
                  ·
                    refine ⟨10631303385822373894582277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087535590548249263054851 10631303385822373894582277)
                    ·
                      refine ⟨1993369384841695105234177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10631303385822373894582277 1993369384841695105234177)
                      ·
                        rfl

theorem cell23_3882073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_3882073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882073 prefixEnd_3882073 := by exact prefixLift 3882073
  have htrace : WordTrace (prefixWord ++ tailWord_3882073) baseStart_3882073 baseEnd_3882073 := by
    simpa [prefixWord, tailWord_3882073, baseEnd_3882073] using wordTrace_append hprefix tailTrace_3882073
  have hstable : (prefixWord ++ tailWord_3882073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882073).length < 2 ^ (prefixWord ++ tailWord_3882073).sum := by decide
  have hdescent : baseEnd_3882073 < baseStart_3882073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882090 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3882090 : Nat := 118140960795 + 3882090 * 2 ^ 59
def prefixEnd_3882090 : Nat := 4983230072969 + 3 ^ 40 * 3882090 * 2
def baseEnd_3882090 : Nat := 1993378114012821538721599

theorem tailTrace_3882090 : CollatzResearch.WordTrace tailWord_3882090 prefixEnd_3882090 1993378114012821538721599 := by
  unfold tailWord_3882090
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397863626464603258082931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94394303003905608688221149 35397863626464603258082931)
  ·
    refine ⟨53096795439696904887124397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35397863626464603258082931 53096795439696904887124397)
    ·
      refine ⟨19911298289886339332671649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53096795439696904887124397 19911298289886339332671649)
      ·
        refine ⟨14933473717414754499503737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19911298289886339332671649 14933473717414754499503737)
        ·
          refine ⟨11200105288061065874627803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14933473717414754499503737 11200105288061065874627803)
          ·
            refine ⟨16800157932091598811941705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200105288061065874627803 16800157932091598811941705)
            ·
              refine ⟨12600118449068699108956279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16800157932091598811941705 12600118449068699108956279)
              ·
                refine ⟨18900177673603048663434419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600118449068699108956279 18900177673603048663434419)
                ·
                  refine ⟨28350266510404572995151629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18900177673603048663434419 28350266510404572995151629)
                  ·
                    refine ⟨10631349941401714873181861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28350266510404572995151629 10631349941401714873181861)
                    ·
                      refine ⟨1993378114012821538721599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10631349941401714873181861 1993378114012821538721599)
                      ·
                        rfl

theorem cell23_3882090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3882090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882090 prefixEnd_3882090 := by exact prefixLift 3882090
  have htrace : WordTrace (prefixWord ++ tailWord_3882090) baseStart_3882090 baseEnd_3882090 := by
    simpa [prefixWord, tailWord_3882090, baseEnd_3882090] using wordTrace_append hprefix tailTrace_3882090
  have hstable : (prefixWord ++ tailWord_3882090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882090).length < 2 ^ (prefixWord ++ tailWord_3882090).sum := by decide
  have hdescent : baseEnd_3882090 < baseStart_3882090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882167 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_3882167 : Nat := 118140960795 + 3882167 * 2 ^ 59
def prefixEnd_3882167 : Nat := 4983230072969 + 3 ^ 40 * 3882167 * 2
def baseEnd_3882167 : Nat := 1993417652023217737458745

theorem tailTrace_3882167 : CollatzResearch.WordTrace tailWord_3882167 prefixEnd_3882167 1993417652023217737458745 := by
  unfold tailWord_3882167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141594262926579455182884755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94396175284386303455256503 141594262926579455182884755)
  ·
    refine ⟨212391394389869182774327133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141594262926579455182884755 212391394389869182774327133)
    ·
      refine ⟨79646772896200943540372675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212391394389869182774327133 79646772896200943540372675)
      ·
        refine ⟨119470159344301415310559013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79646772896200943540372675 119470159344301415310559013)
        ·
          refine ⟨22400654877056515370729815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119470159344301415310559013 22400654877056515370729815)
          ·
            refine ⟨33600982315584773056094723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22400654877056515370729815 33600982315584773056094723)
            ·
              refine ⟨50401473473377159584142085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33600982315584773056094723 50401473473377159584142085)
              ·
                refine ⟨9450276276258217422026641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50401473473377159584142085 9450276276258217422026641)
                ·
                  refine ⟨7087707207193663066519981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9450276276258217422026641 7087707207193663066519981)
                  ·
                    refine ⟨2657890202697623649944993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7087707207193663066519981 2657890202697623649944993)
                    ·
                      refine ⟨1993417652023217737458745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657890202697623649944993 1993417652023217737458745)
                      ·
                        rfl

theorem cell23_3882167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_3882167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882167 prefixEnd_3882167 := by exact prefixLift 3882167
  have htrace : WordTrace (prefixWord ++ tailWord_3882167) baseStart_3882167 baseEnd_3882167 := by
    simpa [prefixWord, tailWord_3882167, baseEnd_3882167] using wordTrace_append hprefix tailTrace_3882167
  have hstable : (prefixWord ++ tailWord_3882167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882167).length < 2 ^ (prefixWord ++ tailWord_3882167).sum := by decide
  have hdescent : baseEnd_3882167 < baseStart_3882167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882177 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3882177 : Nat := 118140960795 + 3882177 * 2 ^ 59
def prefixEnd_3882177 : Nat := 4983230072969 + 3 ^ 40 * 3882177 * 2
def baseEnd_3882177 : Nat := 664474262276587566111233

theorem tailTrace_3882177 : CollatzResearch.WordTrace tailWord_3882177 prefixEnd_3882177 664474262276587566111233 := by
  unfold tailWord_3882177
  simp only [CollatzResearch.WordTrace]
  refine ⟨141594627656543226890748785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94396418437695484593832523 141594627656543226890748785)
  ·
    refine ⟨106195970742407420168061589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141594627656543226890748785 106195970742407420168061589)
    ·
      refine ⟨4977936128550347820377887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106195970742407420168061589 4977936128550347820377887)
      ·
        refine ⟨7466904192825521730566831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977936128550347820377887 7466904192825521730566831)
        ·
          refine ⟨11200356289238282595850247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466904192825521730566831 11200356289238282595850247)
          ·
            refine ⟨16800534433857423893775371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200356289238282595850247 16800534433857423893775371)
            ·
              refine ⟨25200801650786135840663057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800534433857423893775371 25200801650786135840663057)
              ·
                refine ⟨18900601238089601880497293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25200801650786135840663057 18900601238089601880497293)
                ·
                  refine ⟨7087725464283600705186485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18900601238089601880497293 7087725464283600705186485)
                  ·
                    refine ⟨664474262276587566111233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7087725464283600705186485 664474262276587566111233)
                    ·
                      rfl

theorem cell23_3882177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3882177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882177 prefixEnd_3882177 := by exact prefixLift 3882177
  have htrace : WordTrace (prefixWord ++ tailWord_3882177) baseStart_3882177 baseEnd_3882177 := by
    simpa [prefixWord, tailWord_3882177, baseEnd_3882177] using wordTrace_append hprefix tailTrace_3882177
  have hstable : (prefixWord ++ tailWord_3882177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882177).length < 2 ^ (prefixWord ++ tailWord_3882177).sum := by decide
  have hdescent : baseEnd_3882177 < baseStart_3882177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882197 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3882197 : Nat := 118140960795 + 3882197 * 2 ^ 59
def prefixEnd_3882197 : Nat := 4983230072969 + 3 ^ 40 * 3882197 * 2
def baseEnd_3882197 : Nat := 1993433056442852620083607

theorem tailTrace_3882197 : CollatzResearch.WordTrace tailWord_3882197 prefixEnd_3882197 1993433056442852620083607 := by
  unfold tailWord_3882197
  simp only [CollatzResearch.WordTrace]
  refine ⟨141595357116470770306476845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94396904744313846870984563 141595357116470770306476845)
  ·
    refine ⟨53098258918676538864928817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141595357116470770306476845 53098258918676538864928817)
    ·
      refine ⟨39823694189007404148696613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53098258918676538864928817 39823694189007404148696613)
      ·
        refine ⟨7466942660438888277880615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39823694189007404148696613 7466942660438888277880615)
        ·
          refine ⟨11200413990658332416820923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466942660438888277880615 11200413990658332416820923)
          ·
            refine ⟨16800620985987498625231385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200413990658332416820923 16800620985987498625231385)
            ·
              refine ⟨12600465739490623968923539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16800620985987498625231385 12600465739490623968923539)
              ·
                refine ⟨18900698609235935953385309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600465739490623968923539 18900698609235935953385309)
                ·
                  refine ⟨7087761978463475982519491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18900698609235935953385309 7087761978463475982519491)
                  ·
                    refine ⟨10631642967695213973779237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087761978463475982519491 10631642967695213973779237)
                    ·
                      refine ⟨1993433056442852620083607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10631642967695213973779237 1993433056442852620083607)
                      ·
                        rfl

theorem cell23_3882197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3882197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882197 prefixEnd_3882197 := by exact prefixLift 3882197
  have htrace : WordTrace (prefixWord ++ tailWord_3882197) baseStart_3882197 baseEnd_3882197 := by
    simpa [prefixWord, tailWord_3882197, baseEnd_3882197] using wordTrace_append hprefix tailTrace_3882197
  have hstable : (prefixWord ++ tailWord_3882197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882197).length < 2 ^ (prefixWord ++ tailWord_3882197).sum := by decide
  have hdescent : baseEnd_3882197 < baseStart_3882197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3882230 : Nat := 118140960795 + 3882230 * 2 ^ 59
def prefixEnd_3882230 : Nat := 4983230072969 + 3 ^ 40 * 3882230 * 2
def baseEnd_3882230 : Nat := 1993450001304450990970955

theorem tailTrace_3882230 : CollatzResearch.WordTrace tailWord_3882230 prefixEnd_3882230 1993450001304450990970955 := by
  unfold tailWord_3882230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849785045334451058901759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94397707150234144628285429 8849785045334451058901759)
  ·
    refine ⟨13274677568001676588352639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8849785045334451058901759 13274677568001676588352639)
    ·
      refine ⟨19912016352002514882528959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274677568001676588352639 19912016352002514882528959)
      ·
        refine ⟨29868024528003772323793439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19912016352002514882528959 29868024528003772323793439)
        ·
          refine ⟨44802036792005658485690159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29868024528003772323793439 44802036792005658485690159)
          ·
            refine ⟨67203055188008487728535239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44802036792005658485690159 67203055188008487728535239)
            ·
              refine ⟨100804582782012731592802859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67203055188008487728535239 100804582782012731592802859)
              ·
                refine ⟨151206874173019097389204289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100804582782012731592802859 151206874173019097389204289)
                ·
                  refine ⟨113405155629764323041903217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151206874173019097389204289 113405155629764323041903217)
                  ·
                    refine ⟨85053866722323242281427413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113405155629764323041903217 85053866722323242281427413)
                    ·
                      refine ⟨1993450001304450990970955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85053866722323242281427413 1993450001304450990970955)
                      ·
                        rfl

theorem cell23_3882230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3882230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882230 prefixEnd_3882230 := by exact prefixLift 3882230
  have htrace : WordTrace (prefixWord ++ tailWord_3882230) baseStart_3882230 baseEnd_3882230 := by
    simpa [prefixWord, tailWord_3882230, baseEnd_3882230] using wordTrace_append hprefix tailTrace_3882230
  have hstable : (prefixWord ++ tailWord_3882230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882230).length < 2 ^ (prefixWord ++ tailWord_3882230).sum := by decide
  have hdescent : baseEnd_3882230 < baseStart_3882230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882244 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3882244 : Nat := 118140960795 + 3882244 * 2 ^ 59
def prefixEnd_3882244 : Nat := 4983230072969 + 3 ^ 40 * 3882244 * 2
def baseEnd_3882244 : Nat := 1993457190033613936195891

theorem tailTrace_3882244 : CollatzResearch.WordTrace tailWord_3882244 prefixEnd_3882244 1993457190033613936195891 := by
  unfold tailWord_3882244
  simp only [CollatzResearch.WordTrace]
  refine ⟨70798535673650248666718893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94398047564866998222291857 70798535673650248666718893)
  ·
    refine ⟨26549450877618843250019585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70798535673650248666718893 26549450877618843250019585)
    ·
      refine ⟨19912088158214132437514689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26549450877618843250019585 19912088158214132437514689)
      ·
        refine ⟨14934066118660599328136017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19912088158214132437514689 14934066118660599328136017)
        ·
          refine ⟨11200549588995449496102013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14934066118660599328136017 11200549588995449496102013)
          ·
            refine ⟨4200206095873293561038255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11200549588995449496102013 4200206095873293561038255)
            ·
              refine ⟨6300309143809940341557383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200206095873293561038255 6300309143809940341557383)
              ·
                refine ⟨9450463715714910512336075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300309143809940341557383 9450463715714910512336075)
                ·
                  refine ⟨14175695573572365768504113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9450463715714910512336075 14175695573572365768504113)
                  ·
                    refine ⟨10631771680179274326378085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14175695573572365768504113 10631771680179274326378085)
                    ·
                      refine ⟨1993457190033613936195891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10631771680179274326378085 1993457190033613936195891)
                      ·
                        rfl

theorem cell23_3882244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3882244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882244 prefixEnd_3882244 := by exact prefixLift 3882244
  have htrace : WordTrace (prefixWord ++ tailWord_3882244) baseStart_3882244 baseEnd_3882244 := by
    simpa [prefixWord, tailWord_3882244, baseEnd_3882244] using wordTrace_append hprefix tailTrace_3882244
  have hstable : (prefixWord ++ tailWord_3882244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882244).length < 2 ^ (prefixWord ++ tailWord_3882244).sum := by decide
  have hdescent : baseEnd_3882244 < baseStart_3882244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882308 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3882308 : Nat := 118140960795 + 3882308 * 2 ^ 59
def prefixEnd_3882308 : Nat := 4983230072969 + 3 ^ 40 * 3882308 * 2
def baseEnd_3882308 : Nat := 1993490052795501685795597

theorem tailTrace_3882308 : CollatzResearch.WordTrace tailWord_3882308 prefixEnd_3882308 1993490052795501685795597 := by
  unfold tailWord_3882308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70799702809534318131883789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94399603746045757509178385 70799702809534318131883789)
  ·
    refine ⟨26549888553575369299456421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70799702809534318131883789 26549888553575369299456421)
    ·
      refine ⟨4978104103795381743648079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26549888553575369299456421 4978104103795381743648079)
      ·
        refine ⟨7467156155693072615472119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978104103795381743648079 7467156155693072615472119)
        ·
          refine ⟨11200734233539608923208179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467156155693072615472119 11200734233539608923208179)
          ·
            refine ⟨16801101350309413384812269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200734233539608923208179 16801101350309413384812269)
            ·
              refine ⟨6300413006366030019304601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16801101350309413384812269 6300413006366030019304601)
              ·
                refine ⟨4725309754774522514478451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300413006366030019304601 4725309754774522514478451)
                ·
                  refine ⟨7087964632161783771717677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725309754774522514478451 7087964632161783771717677)
                  ·
                    refine ⟨2657986737060668914394129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7087964632161783771717677 2657986737060668914394129)
                    ·
                      refine ⟨1993490052795501685795597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2657986737060668914394129 1993490052795501685795597)
                      ·
                        rfl

theorem cell23_3882308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3882308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882308 prefixEnd_3882308 := by exact prefixLift 3882308
  have htrace : WordTrace (prefixWord ++ tailWord_3882308) baseStart_3882308 baseEnd_3882308 := by
    simpa [prefixWord, tailWord_3882308, baseEnd_3882308] using wordTrace_append hprefix tailTrace_3882308
  have hstable : (prefixWord ++ tailWord_3882308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882308).length < 2 ^ (prefixWord ++ tailWord_3882308).sum := by decide
  have hdescent : baseEnd_3882308 < baseStart_3882308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882338 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3882338 : Nat := 118140960795 + 3882338 * 2 ^ 59
def prefixEnd_3882338 : Nat := 4983230072969 + 3 ^ 40 * 3882338 * 2
def baseEnd_3882338 : Nat := 1993505457215136568420459

theorem tailTrace_3882338 : CollatzResearch.WordTrace tailWord_3882338 prefixEnd_3882338 1993505457215136568420459 := by
  unfold tailWord_3882338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400124952239987846839917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94400333205973300924906445 35400124952239987846839917)
  ·
    refine ⟨13275046857089995442564969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35400124952239987846839917 13275046857089995442564969)
    ·
      refine ⟨9956285142817496581923727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13275046857089995442564969 9956285142817496581923727)
      ·
        refine ⟨14934427714226244872885591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956285142817496581923727 14934427714226244872885591)
        ·
          refine ⟨22401641571339367309328387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934427714226244872885591 22401641571339367309328387)
          ·
            refine ⟨33602462357009050963992581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22401641571339367309328387 33602462357009050963992581)
            ·
              refine ⟨6300461691939197055748609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33602462357009050963992581 6300461691939197055748609)
              ·
                refine ⟨4725346268954397791811457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300461691939197055748609 4725346268954397791811457)
                ·
                  refine ⟨3544009701715798343858593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725346268954397791811457 3544009701715798343858593)
                  ·
                    refine ⟨2658007276286848757893945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3544009701715798343858593 2658007276286848757893945)
                    ·
                      refine ⟨1993505457215136568420459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658007276286848757893945 1993505457215136568420459)
                      ·
                        rfl

theorem cell23_3882338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3882338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882338 prefixEnd_3882338 := by exact prefixLift 3882338
  have htrace : WordTrace (prefixWord ++ tailWord_3882338) baseStart_3882338 baseEnd_3882338 := by
    simpa [prefixWord, tailWord_3882338, baseEnd_3882338] using wordTrace_append hprefix tailTrace_3882338
  have hstable : (prefixWord ++ tailWord_3882338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882338).length < 2 ^ (prefixWord ++ tailWord_3882338).sum := by decide
  have hdescent : baseEnd_3882338 < baseStart_3882338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882394 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3882394 : Nat := 118140960795 + 3882394 * 2 ^ 59
def prefixEnd_3882394 : Nat := 4983230072969 + 3 ^ 40 * 3882394 * 2
def baseEnd_3882394 : Nat := 1993534212131788349320201

theorem tailTrace_3882394 : CollatzResearch.WordTrace tailWord_3882394 prefixEnd_3882394 1993534212131788349320201 := by
  unfold tailWord_3882394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400635574189268237849559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94401694864504715300932157 35400635574189268237849559)
  ·
    refine ⟨53100953361283902356774339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35400635574189268237849559 53100953361283902356774339)
    ·
      refine ⟨79651430041925853535161509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53100953361283902356774339 79651430041925853535161509)
      ·
        refine ⟨14934643132861097537842783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79651430041925853535161509 14934643132861097537842783)
        ·
          refine ⟨22401964699291646306764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934643132861097537842783 22401964699291646306764175)
          ·
            refine ⟨33602947048937469460146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22401964699291646306764175 33602947048937469460146263)
            ·
              refine ⟨50404420573406204190219395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33602947048937469460146263 50404420573406204190219395)
              ·
                refine ⟨75606630860109306285329093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50404420573406204190219395 75606630860109306285329093)
                ·
                  refine ⟨14176243286270494928499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75606630860109306285329093 14176243286270494928499205)
                  ·
                    refine ⟨2658045616175717799093601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14176243286270494928499205 2658045616175717799093601)
                    ·
                      refine ⟨1993534212131788349320201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658045616175717799093601 1993534212131788349320201)
                      ·
                        rfl

theorem cell23_3882394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3882394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882394 prefixEnd_3882394 := by exact prefixLift 3882394
  have htrace : WordTrace (prefixWord ++ tailWord_3882394) baseStart_3882394 baseEnd_3882394 := by
    simpa [prefixWord, tailWord_3882394, baseEnd_3882394] using wordTrace_append hprefix tailTrace_3882394
  have hstable : (prefixWord ++ tailWord_3882394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882394).length < 2 ^ (prefixWord ++ tailWord_3882394).sum := by decide
  have hdescent : baseEnd_3882394 < baseStart_3882394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882407 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3882407 : Nat := 118140960795 + 3882407 * 2 ^ 59
def prefixEnd_3882407 : Nat := 4983230072969 + 3 ^ 40 * 3882407 * 2
def baseEnd_3882407 : Nat := 1993540887380296798457641

theorem tailTrace_3882407 : CollatzResearch.WordTrace tailWord_3882407 prefixEnd_3882407 1993540887380296798457641 := by
  unfold tailWord_3882407
  simp only [CollatzResearch.WordTrace]
  refine ⟨141603016445709976171621475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94402010963806650781080983 141603016445709976171621475)
  ·
    refine ⟨212404524668564964257432213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141603016445709976171621475 212404524668564964257432213)
    ·
      refine ⟨9956462093838982699567135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212404524668564964257432213 9956462093838982699567135)
      ·
        refine ⟨14934693140758474049350703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956462093838982699567135 14934693140758474049350703)
        ·
          refine ⟨22402039711137711074026055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934693140758474049350703 22402039711137711074026055)
          ·
            refine ⟨33603059566706566611039083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402039711137711074026055 33603059566706566611039083)
            ·
              refine ⟨50404589350059849916558625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33603059566706566611039083 50404589350059849916558625)
              ·
                refine ⟨37803442012544887437418969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50404589350059849916558625 37803442012544887437418969)
                ·
                  refine ⟨28352581509408665578064227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37803442012544887437418969 28352581509408665578064227)
                  ·
                    refine ⟨42528872264112998367096341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28352581509408665578064227 42528872264112998367096341)
                    ·
                      refine ⟨1993540887380296798457641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42528872264112998367096341 1993540887380296798457641)
                      ·
                        rfl

theorem cell23_3882407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3882407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882407 prefixEnd_3882407 := by exact prefixLift 3882407
  have htrace : WordTrace (prefixWord ++ tailWord_3882407) baseStart_3882407 baseEnd_3882407 := by
    simpa [prefixWord, tailWord_3882407, baseEnd_3882407] using wordTrace_append hprefix tailTrace_3882407
  have hstable : (prefixWord ++ tailWord_3882407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882407).length < 2 ^ (prefixWord ++ tailWord_3882407).sum := by decide
  have hdescent : baseEnd_3882407 < baseStart_3882407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882481 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_3882481 : Nat := 118140960795 + 3882481 * 2 ^ 59
def prefixEnd_3882481 : Nat := 4983230072969 + 3 ^ 40 * 3882481 * 2
def baseEnd_3882481 : Nat := 664526294982909836310767

theorem tailTrace_3882481 : CollatzResearch.WordTrace tailWord_3882481 prefixEnd_3882481 664526294982909836310767 := by
  unfold tailWord_3882481
  simp only [CollatzResearch.WordTrace]
  refine ⟨141605715447441886809815297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94403810298294591206543531 141605715447441886809815297)
  ·
    refine ⟨106204286585581415107361473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141605715447441886809815297 106204286585581415107361473)
    ·
      refine ⟨79653214939186061330521105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106204286585581415107361473 79653214939186061330521105)
      ·
        refine ⟨59739911204389545997890829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79653214939186061330521105 59739911204389545997890829)
        ·
          refine ⟨22402466701646079749209061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59739911204389545997890829 22402466701646079749209061)
          ·
            refine ⟨4200462506558639952976699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22402466701646079749209061 4200462506558639952976699)
            ·
              refine ⟨6300693759837959929465049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200462506558639952976699 6300693759837959929465049)
              ·
                refine ⟨4725520319878469947098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300693759837959929465049 4725520319878469947098787)
                ·
                  refine ⟨7088280479817704920648181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725520319878469947098787 7088280479817704920648181)
                  ·
                    refine ⟨664526294982909836310767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7088280479817704920648181 664526294982909836310767)
                    ·
                      rfl

theorem cell23_3882481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_3882481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882481 prefixEnd_3882481 := by exact prefixLift 3882481
  have htrace : WordTrace (prefixWord ++ tailWord_3882481) baseStart_3882481 baseEnd_3882481 := by
    simpa [prefixWord, tailWord_3882481, baseEnd_3882481] using wordTrace_append hprefix tailTrace_3882481
  have hstable : (prefixWord ++ tailWord_3882481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882481).length < 2 ^ (prefixWord ++ tailWord_3882481).sum := by decide
  have hdescent : baseEnd_3882481 < baseStart_3882481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882504 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3882504 : Nat := 118140960795 + 3882504 * 2 ^ 59
def prefixEnd_3882504 : Nat := 4983230072969 + 3 ^ 40 * 3882504 * 2
def baseEnd_3882504 : Nat := 1993590695003782918944695

theorem tailTrace_3882504 : CollatzResearch.WordTrace tailWord_3882504 prefixEnd_3882504 1993590695003782918944695 := by
  unfold tailWord_3882504
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803277163179280868951283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94404369550905707825268377 70803277163179280868951283)
  ·
    refine ⟨106204915744768921303426925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70803277163179280868951283 106204915744768921303426925)
    ·
      refine ⟨39826843404288345488785097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106204915744768921303426925 39826843404288345488785097)
      ·
        refine ⟨29870132553216259116588823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39826843404288345488785097 29870132553216259116588823)
        ·
          refine ⟨44805198829824388674883235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29870132553216259116588823 44805198829824388674883235)
          ·
            refine ⟨67207798244736583012324853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44805198829824388674883235 67207798244736583012324853)
            ·
              refine ⟨6300731085444054657405455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67207798244736583012324853 6300731085444054657405455)
              ·
                refine ⟨9451096628166081986108183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300731085444054657405455 9451096628166081986108183)
                ·
                  refine ⟨14176644942249122979162275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451096628166081986108183 14176644942249122979162275)
                  ·
                    refine ⟨21264967413373684468743413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14176644942249122979162275 21264967413373684468743413)
                    ·
                      refine ⟨1993590695003782918944695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21264967413373684468743413 1993590695003782918944695)
                      ·
                        rfl

theorem cell23_3882504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3882504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882504 prefixEnd_3882504 := by exact prefixLift 3882504
  have htrace : WordTrace (prefixWord ++ tailWord_3882504) baseStart_3882504 baseEnd_3882504 := by
    simpa [prefixWord, tailWord_3882504, baseEnd_3882504] using wordTrace_append hprefix tailTrace_3882504
  have hstable : (prefixWord ++ tailWord_3882504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882504).length < 2 ^ (prefixWord ++ tailWord_3882504).sum := by decide
  have hdescent : baseEnd_3882504 < baseStart_3882504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882507 : List Nat := [1, 1, 1, 1, 8, 11]
def baseStart_3882507 : Nat := 118140960795 + 3882507 * 2 ^ 59
def prefixEnd_3882507 : Nat := 4983230072969 + 3 ^ 40 * 3882507 * 2
def baseEnd_3882507 : Nat := 8204083273439285626367

theorem tailTrace_3882507 : CollatzResearch.WordTrace tailWord_3882507 prefixEnd_3882507 8204083273439285626367 := by
  unfold tailWord_3882507
  simp only [CollatzResearch.WordTrace]
  refine ⟨141606663745347693250261775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94404442496898462166841183 141606663745347693250261775)
  ·
    refine ⟨212409995618021539875392663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141606663745347693250261775 212409995618021539875392663)
    ·
      refine ⟨318614993427032309813088995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212409995618021539875392663 318614993427032309813088995)
      ·
        refine ⟨477922490140548464719633493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318614993427032309813088995 477922490140548464719633493)
        ·
          refine ⟨5600654181334552320933205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 477922490140548464719633493 5600654181334552320933205)
          ·
            refine ⟨8204083273439285626367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5600654181334552320933205 8204083273439285626367)
            ·
              rfl

theorem cell23_3882507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 11].length) (baseStart_3882507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882507 prefixEnd_3882507 := by exact prefixLift 3882507
  have htrace : WordTrace (prefixWord ++ tailWord_3882507) baseStart_3882507 baseEnd_3882507 := by
    simpa [prefixWord, tailWord_3882507, baseEnd_3882507] using wordTrace_append hprefix tailTrace_3882507
  have hstable : (prefixWord ++ tailWord_3882507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882507).length < 2 ^ (prefixWord ++ tailWord_3882507).sum := by decide
  have hdescent : baseEnd_3882507 < baseStart_3882507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882527 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3882527 : Nat := 118140960795 + 3882527 * 2 ^ 59
def prefixEnd_3882527 : Nat := 4983230072969 + 3 ^ 40 * 3882527 * 2
def baseEnd_3882527 : Nat := 1993602505058836328957089

theorem tailTrace_3882527 : CollatzResearch.WordTrace tailWord_3882527 prefixEnd_3882527 1993602505058836328957089 := by
  unfold tailWord_3882527
  simp only [CollatzResearch.WordTrace]
  refine ⟨141607393205275236665989835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94404928803516824443993223 141607393205275236665989835)
  ·
    refine ⟨212411089807912854998984753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141607393205275236665989835 212411089807912854998984753)
    ·
      refine ⟨159308317355934641249238565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212411089807912854998984753 159308317355934641249238565)
      ·
        refine ⟨29870309504237745234232231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159308317355934641249238565 29870309504237745234232231)
        ·
          refine ⟨44805464256356617851348347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29870309504237745234232231 44805464256356617851348347)
          ·
            refine ⟨67208196384534926777022521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44805464256356617851348347 67208196384534926777022521)
            ·
              refine ⟨50406147288401195082766891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67208196384534926777022521 50406147288401195082766891)
              ·
                refine ⟨75609220932601792624150337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50406147288401195082766891 75609220932601792624150337)
                ·
                  refine ⟨56706915699451344468112753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75609220932601792624150337 56706915699451344468112753)
                  ·
                    refine ⟨42530186774588508351084565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56706915699451344468112753 42530186774588508351084565)
                    ·
                      refine ⟨1993602505058836328957089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42530186774588508351084565 1993602505058836328957089)
                      ·
                        rfl

theorem cell23_3882527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3882527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882527 prefixEnd_3882527 := by exact prefixLift 3882527
  have htrace : WordTrace (prefixWord ++ tailWord_3882527) baseStart_3882527 baseEnd_3882527 := by
    simpa [prefixWord, tailWord_3882527, baseEnd_3882527] using wordTrace_append hprefix tailTrace_3882527
  have hstable : (prefixWord ++ tailWord_3882527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882527).length < 2 ^ (prefixWord ++ tailWord_3882527).sum := by decide
  have hdescent : baseEnd_3882527 < baseStart_3882527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882531 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4]
def baseStart_3882531 : Nat := 118140960795 + 3882531 * 2 ^ 59
def prefixEnd_3882531 : Nat := 4983230072969 + 3 ^ 40 * 3882531 * 2
def baseEnd_3882531 : Nat := 1993604558981454313307071

theorem tailTrace_3882531 : CollatzResearch.WordTrace tailWord_3882531 prefixEnd_3882531 1993604558981454313307071 := by
  unfold tailWord_3882531
  simp only [CollatzResearch.WordTrace]
  refine ⟨141607539097260745349135447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94405026064840496899423631 141607539097260745349135447)
  ·
    refine ⟨212411308645891118023703171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141607539097260745349135447 212411308645891118023703171)
    ·
      refine ⟨318616962968836677035554757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212411308645891118023703171 318616962968836677035554757)
      ·
        refine ⟨59740680556656876944166517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318616962968836677035554757 59740680556656876944166517)
        ·
          refine ⟨5600688802186582213515611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59740680556656876944166517 5600688802186582213515611)
          ·
            refine ⟨8401033203279873320273417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600688802186582213515611 8401033203279873320273417)
            ·
              refine ⟨6300774902459904990205063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401033203279873320273417 6300774902459904990205063)
              ·
                refine ⟨9451162353689857485307595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300774902459904990205063 9451162353689857485307595)
                ·
                  refine ⟨14176743530534786227961393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451162353689857485307595 14176743530534786227961393)
                  ·
                    refine ⟨10632557647901089670971045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14176743530534786227961393 10632557647901089670971045)
                    ·
                      refine ⟨1993604558981454313307071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10632557647901089670971045 1993604558981454313307071)
                      ·
                        rfl

theorem cell23_3882531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_3882531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882531 prefixEnd_3882531 := by exact prefixLift 3882531
  have htrace : WordTrace (prefixWord ++ tailWord_3882531) baseStart_3882531 baseEnd_3882531 := by
    simpa [prefixWord, tailWord_3882531, baseEnd_3882531] using wordTrace_append hprefix tailTrace_3882531
  have hstable : (prefixWord ++ tailWord_3882531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882531).length < 2 ^ (prefixWord ++ tailWord_3882531).sum := by decide
  have hdescent : baseEnd_3882531 < baseStart_3882531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882582 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3882582 : Nat := 118140960795 + 3882582 * 2 ^ 59
def prefixEnd_3882582 : Nat := 4983230072969 + 3 ^ 40 * 3882582 * 2
def baseEnd_3882582 : Nat := 1993630746494833613769337

theorem tailTrace_3882582 : CollatzResearch.WordTrace tailWord_3882582 prefixEnd_3882582 1993630746494833613769337 := by
  unfold tailWord_3882582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850587451254748816202625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94406266146717320706161333 8850587451254748816202625)
  ·
    refine ⟨6637940588441061612151969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850587451254748816202625 6637940588441061612151969)
    ·
      refine ⟨4978455441330796209113977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637940588441061612151969 4978455441330796209113977)
      ·
        refine ⟨3733841580998097156835483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4978455441330796209113977 3733841580998097156835483)
        ·
          refine ⟨5600762371497145735253225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733841580998097156835483 5600762371497145735253225)
          ·
            refine ⟨4200571778622859301439919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600762371497145735253225 4200571778622859301439919)
            ·
              refine ⟨6300857667934288952159879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200571778622859301439919 6300857667934288952159879)
              ·
                refine ⟨9451286501901433428239819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300857667934288952159879 9451286501901433428239819)
                ·
                  refine ⟨14176929752852150142359729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451286501901433428239819 14176929752852150142359729)
                  ·
                    refine ⟨10632697314639112606769797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14176929752852150142359729 10632697314639112606769797)
                    ·
                      refine ⟨1993630746494833613769337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10632697314639112606769797 1993630746494833613769337)
                      ·
                        rfl

theorem cell23_3882582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3882582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882582 prefixEnd_3882582 := by exact prefixLift 3882582
  have htrace : WordTrace (prefixWord ++ tailWord_3882582) baseStart_3882582 baseEnd_3882582 := by
    simpa [prefixWord, tailWord_3882582, baseEnd_3882582] using wordTrace_append hprefix tailTrace_3882582
  have hstable : (prefixWord ++ tailWord_3882582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882582).length < 2 ^ (prefixWord ++ tailWord_3882582).sum := by decide
  have hdescent : baseEnd_3882582 < baseStart_3882582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882608 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2]
def baseStart_3882608 : Nat := 118140960795 + 3882608 * 2 ^ 59
def prefixEnd_3882608 : Nat := 4983230072969 + 3 ^ 40 * 3882608 * 2
def baseEnd_3882608 : Nat := 1993644096991850512044217

theorem tailTrace_3882608 : CollatzResearch.WordTrace tailWord_3882608 prefixEnd_3882608 1993644096991850512044217 := by
  unfold tailWord_3882608
  simp only [CollatzResearch.WordTrace]
  refine ⟨70805173758990893749844239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94406898345321191666458985 70805173758990893749844239)
  ·
    refine ⟨106207760638486340624766359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70805173758990893749844239 106207760638486340624766359)
    ·
      refine ⟨159311640957729510937149539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106207760638486340624766359 159311640957729510937149539)
      ·
        refine ⟨238967461436594266405724309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159311640957729510937149539 238967461436594266405724309)
        ·
          refine ⟨11201599754840356237768327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 238967461436594266405724309 11201599754840356237768327)
          ·
            refine ⟨16802399632260534356652491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201599754840356237768327 16802399632260534356652491)
            ·
              refine ⟨25203599448390801534978737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16802399632260534356652491 25203599448390801534978737)
              ·
                refine ⟨18902699586293101151234053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25203599448390801534978737 18902699586293101151234053)
                ·
                  refine ⟨3544256172429956465856385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18902699586293101151234053 3544256172429956465856385)
                  ·
                    refine ⟨2658192129322467349392289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3544256172429956465856385 2658192129322467349392289)
                    ·
                      refine ⟨1993644096991850512044217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658192129322467349392289 1993644096991850512044217)
                      ·
                        rfl

theorem cell23_3882608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2].length) (baseStart_3882608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882608 prefixEnd_3882608 := by exact prefixLift 3882608
  have htrace : WordTrace (prefixWord ++ tailWord_3882608) baseStart_3882608 baseEnd_3882608 := by
    simpa [prefixWord, tailWord_3882608, baseEnd_3882608] using wordTrace_append hprefix tailTrace_3882608
  have hstable : (prefixWord ++ tailWord_3882608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882608).length < 2 ^ (prefixWord ++ tailWord_3882608).sum := by decide
  have hdescent : baseEnd_3882608 < baseStart_3882608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882631 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 7]
def baseStart_3882631 : Nat := 118140960795 + 3882631 * 2 ^ 59
def prefixEnd_3882631 : Nat := 4983230072969 + 3 ^ 40 * 3882631 * 2
def baseEnd_3882631 : Nat := 221517323005211546895179

theorem tailTrace_3882631 : CollatzResearch.WordTrace tailWord_3882631 prefixEnd_3882631 221517323005211546895179 := by
  unfold tailWord_3882631
  simp only [CollatzResearch.WordTrace]
  refine ⟨141611186396898462427775747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94407457597932308285183831 141611186396898462427775747)
  ·
    refine ⟨212416779595347693641663621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141611186396898462427775747 212416779595347693641663621)
    ·
      refine ⟨39828146174127692557811929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212416779595347693641663621 39828146174127692557811929)
      ·
        refine ⟨29871109630595769418358947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39828146174127692557811929 29871109630595769418358947)
        ·
          refine ⟨44806664445893654127538421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29871109630595769418358947 44806664445893654127538421)
          ·
            refine ⟨4200624791802530074456727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44806664445893654127538421 4200624791802530074456727)
            ·
              refine ⟨6300937187703795111685091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200624791802530074456727 6300937187703795111685091)
              ·
                refine ⟨9451405781555692667527637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300937187703795111685091 9451405781555692667527637)
                ·
                  refine ⟨221517323005211546895179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9451405781555692667527637 221517323005211546895179)
                  ·
                    rfl

theorem cell23_3882631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 7].length) (baseStart_3882631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882631 prefixEnd_3882631 := by exact prefixLift 3882631
  have htrace : WordTrace (prefixWord ++ tailWord_3882631) baseStart_3882631 baseEnd_3882631 := by
    simpa [prefixWord, tailWord_3882631, baseEnd_3882631] using wordTrace_append hprefix tailTrace_3882631
  have hstable : (prefixWord ++ tailWord_3882631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882631).length < 2 ^ (prefixWord ++ tailWord_3882631).sum := by decide
  have hdescent : baseEnd_3882631 < baseStart_3882631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882642 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3882642 : Nat := 118140960795 + 3882642 * 2 ^ 59
def prefixEnd_3882642 : Nat := 4983230072969 + 3 ^ 40 * 3882642 * 2
def baseEnd_3882642 : Nat := 1993661555334103379019061

theorem tailTrace_3882642 : CollatzResearch.WordTrace tailWord_3882642 prefixEnd_3882642 1993661555334103379019061 := by
  unfold tailWord_3882642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35402896899964652826606545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94407725066572407537617453 35402896899964652826606545)
  ·
    refine ⟨26552172674973489619954909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35402896899964652826606545 26552172674973489619954909)
    ·
      refine ⟨9957064753115058607483091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26552172674973489619954909 9957064753115058607483091)
      ·
        refine ⟨14935597129672587911224637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957064753115058607483091 14935597129672587911224637)
        ·
          refine ⟨5600848923627220466709239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14935597129672587911224637 5600848923627220466709239)
          ·
            refine ⟨8401273385440830700063859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600848923627220466709239 8401273385440830700063859)
            ·
              refine ⟨12601910078161246050095789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401273385440830700063859 12601910078161246050095789)
              ·
                refine ⟨4725716279310467268785921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12601910078161246050095789 4725716279310467268785921)
                ·
                  refine ⟨3544287209482850451589441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725716279310467268785921 3544287209482850451589441)
                  ·
                    refine ⟨2658215407112137838692081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3544287209482850451589441 2658215407112137838692081)
                    ·
                      refine ⟨1993661555334103379019061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658215407112137838692081 1993661555334103379019061)
                      ·
                        rfl

theorem cell23_3882642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3882642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882642 prefixEnd_3882642 := by exact prefixLift 3882642
  have htrace : WordTrace (prefixWord ++ tailWord_3882642) baseStart_3882642 baseEnd_3882642 := by
    simpa [prefixWord, tailWord_3882642, baseEnd_3882642] using wordTrace_append hprefix tailTrace_3882642
  have hstable : (prefixWord ++ tailWord_3882642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882642).length < 2 ^ (prefixWord ++ tailWord_3882642).sum := by decide
  have hdescent : baseEnd_3882642 < baseStart_3882642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882681 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3882681 : Nat := 118140960795 + 3882681 * 2 ^ 59
def prefixEnd_3882681 : Nat := 4983230072969 + 3 ^ 40 * 3882681 * 2
def baseEnd_3882681 : Nat := 1993681581079628726431381

theorem tailTrace_3882681 : CollatzResearch.WordTrace tailWord_3882681 prefixEnd_3882681 1993681581079628726431381 := by
  unfold tailWord_3882681
  simp only [CollatzResearch.WordTrace]
  refine ⟨141613010046717320967095897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94408673364478213978063931 141613010046717320967095897)
  ·
    refine ⟨106209757535037990725321923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141613010046717320967095897 106209757535037990725321923)
    ·
      refine ⟨159314636302556986087982885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106209757535037990725321923 159314636302556986087982885)
      ·
        refine ⟨29871494306729434891496791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159314636302556986087982885 29871494306729434891496791)
        ·
          refine ⟨44807241460094152337245187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29871494306729434891496791 44807241460094152337245187)
          ·
            refine ⟨67210862190141228505867781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44807241460094152337245187 67210862190141228505867781)
            ·
              refine ⟨12602036660651480344850209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67210862190141228505867781 12602036660651480344850209)
              ·
                refine ⟨9451527495488610258637657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12602036660651480344850209 9451527495488610258637657)
                ·
                  refine ⟨7088645621616457693978243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9451527495488610258637657 7088645621616457693978243)
                  ·
                    refine ⟨10632968432424686540967365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7088645621616457693978243 10632968432424686540967365)
                    ·
                      refine ⟨1993681581079628726431381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10632968432424686540967365 1993681581079628726431381)
                      ·
                        rfl

theorem cell23_3882681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3882681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882681 prefixEnd_3882681 := by exact prefixLift 3882681
  have htrace : WordTrace (prefixWord ++ tailWord_3882681) baseStart_3882681 baseEnd_3882681 := by
    simpa [prefixWord, tailWord_3882681, baseEnd_3882681] using wordTrace_append hprefix tailTrace_3882681
  have hstable : (prefixWord ++ tailWord_3882681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882681).length < 2 ^ (prefixWord ++ tailWord_3882681).sum := by decide
  have hdescent : baseEnd_3882681 < baseStart_3882681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882708 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3882708 : Nat := 118140960795 + 3882708 * 2 ^ 59
def prefixEnd_3882708 : Nat := 4983230072969 + 3 ^ 40 * 3882708 * 2
def baseEnd_3882708 : Nat := 664565148352433373597919

theorem tailTrace_3882708 : CollatzResearch.WordTrace tailWord_3882708 prefixEnd_3882708 664565148352433373597919 := by
  unfold tailWord_3882708
  simp only [CollatzResearch.WordTrace]
  refine ⟨70806997408809752289164389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94409329878413003052219185 70806997408809752289164389)
  ·
    refine ⟨13276312014151828554218323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70806997408809752289164389 13276312014151828554218323)
    ·
      refine ⟨19914468021227742831327485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13276312014151828554218323 19914468021227742831327485)
      ·
        refine ⟨7467925507960403561747807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19914468021227742831327485 7467925507960403561747807)
        ·
          refine ⟨11201888261940605342621711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467925507960403561747807 11201888261940605342621711)
          ·
            refine ⟨16802832392910908013932567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201888261940605342621711 16802832392910908013932567)
            ·
              refine ⟨25204248589366362020898851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16802832392910908013932567 25204248589366362020898851)
              ·
                refine ⟨37806372884049543031348277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25204248589366362020898851 37806372884049543031348277)
                ·
                  refine ⟨3544347457879644659188901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37806372884049543031348277 3544347457879644659188901)
                  ·
                    refine ⟨664565148352433373597919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544347457879644659188901 664565148352433373597919)
                    ·
                      rfl

theorem cell23_3882708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3882708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882708 prefixEnd_3882708 := by exact prefixLift 3882708
  have htrace : WordTrace (prefixWord ++ tailWord_3882708) baseStart_3882708 baseEnd_3882708 := by
    simpa [prefixWord, tailWord_3882708, baseEnd_3882708] using wordTrace_append hprefix tailTrace_3882708
  have hstable : (prefixWord ++ tailWord_3882708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882708).length < 2 ^ (prefixWord ++ tailWord_3882708).sum := by decide
  have hdescent : baseEnd_3882708 < baseStart_3882708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882725 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_3882725 : Nat := 118140960795 + 3882725 * 2 ^ 59
def prefixEnd_3882725 : Nat := 4983230072969 + 3 ^ 40 * 3882725 * 2
def baseEnd_3882725 : Nat := 664568058076142184760393

theorem tailTrace_3882725 : CollatzResearch.WordTrace tailWord_3882725 prefixEnd_3882725 664568058076142184760393 := by
  unfold tailWord_3882725
  simp only [CollatzResearch.WordTrace]
  refine ⟨141614614858557916481697629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94409743239038610987798419 141614614858557916481697629)
  ·
    refine ⟨53105480571959218680636611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141614614858557916481697629 53105480571959218680636611)
    ·
      refine ⟨79658220857938828020954917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53105480571959218680636611 79658220857938828020954917)
      ·
        refine ⟨14935916410863530253929047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79658220857938828020954917 14935916410863530253929047)
        ·
          refine ⟨22403874616295295380893571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14935916410863530253929047 22403874616295295380893571)
          ·
            refine ⟨33605811924442943071340357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22403874616295295380893571 33605811924442943071340357)
            ·
              refine ⟨6301089735833051825876317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33605811924442943071340357 6301089735833051825876317)
              ·
                refine ⟨2362908650937394434703619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6301089735833051825876317 2362908650937394434703619)
                ·
                  refine ⟨3544362976406091652055429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362908650937394434703619 3544362976406091652055429)
                  ·
                    refine ⟨664568058076142184760393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544362976406091652055429 664568058076142184760393)
                    ·
                      rfl

theorem cell23_3882725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_3882725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882725 prefixEnd_3882725 := by exact prefixLift 3882725
  have htrace : WordTrace (prefixWord ++ tailWord_3882725) baseStart_3882725 baseEnd_3882725 := by
    simpa [prefixWord, tailWord_3882725, baseEnd_3882725] using wordTrace_append hprefix tailTrace_3882725
  have hstable : (prefixWord ++ tailWord_3882725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882725).length < 2 ^ (prefixWord ++ tailWord_3882725).sum := by decide
  have hdescent : baseEnd_3882725 < baseStart_3882725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882744 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_3882744 : Nat := 118140960795 + 3882744 * 2 ^ 59
def prefixEnd_3882744 : Nat := 4983230072969 + 3 ^ 40 * 3882744 * 2
def baseEnd_3882744 : Nat := 1993713930360861979943591

theorem tailTrace_3882744 : CollatzResearch.WordTrace tailWord_3882744 prefixEnd_3882744 1993713930360861979943591 := by
  unfold tailWord_3882744
  simp only [CollatzResearch.WordTrace]
  refine ⟨70807653922744541363319643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94410205230326055151092857 70807653922744541363319643)
  ·
    refine ⟨106211480884116812044979465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70807653922744541363319643 106211480884116812044979465)
    ·
      refine ⟨79658610663087609033734599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106211480884116812044979465 79658610663087609033734599)
      ·
        refine ⟨119487915994631413550601899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79658610663087609033734599 119487915994631413550601899)
        ·
          refine ⟨179231873991947120325902849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119487915994631413550601899 179231873991947120325902849)
          ·
            refine ⟨134423905493960340244427137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179231873991947120325902849 134423905493960340244427137)
            ·
              refine ⟨100817929120470255183320353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134423905493960340244427137 100817929120470255183320353)
              ·
                refine ⟨75613446840352691387490265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100817929120470255183320353 75613446840352691387490265)
                ·
                  refine ⟨56710085130264518540617699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75613446840352691387490265 56710085130264518540617699)
                  ·
                    refine ⟨85065127695396777810926549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56710085130264518540617699 85065127695396777810926549)
                    ·
                      refine ⟨1993713930360861979943591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85065127695396777810926549 1993713930360861979943591)
                      ·
                        rfl

theorem cell23_3882744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_3882744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882744 prefixEnd_3882744 := by exact prefixLift 3882744
  have htrace : WordTrace (prefixWord ++ tailWord_3882744) baseStart_3882744 baseEnd_3882744 := by
    simpa [prefixWord, tailWord_3882744, baseEnd_3882744] using wordTrace_append hprefix tailTrace_3882744
  have hstable : (prefixWord ++ tailWord_3882744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882744).length < 2 ^ (prefixWord ++ tailWord_3882744).sum := by decide
  have hdescent : baseEnd_3882744 < baseStart_3882744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882801 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3882801 : Nat := 118140960795 + 3882801 * 2 ^ 59
def prefixEnd_3882801 : Nat := 4983230072969 + 3 ^ 40 * 3882801 * 2
def baseEnd_3882801 : Nat := 1993743198758168256930829

theorem tailTrace_3882801 : CollatzResearch.WordTrace tailWord_3882801 prefixEnd_3882801 1993743198758168256930829 := by
  unfold tailWord_3882801
  simp only [CollatzResearch.WordTrace]
  refine ⟨141617386806282581461464257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94411591204188387640976171 141617386806282581461464257)
  ·
    refine ⟨106213040104711936096098193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141617386806282581461464257 106213040104711936096098193)
    ·
      refine ⟨79659780078533952072073645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106213040104711936096098193 79659780078533952072073645)
      ·
        refine ⟨29872417529450232027027617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79659780078533952072073645 29872417529450232027027617)
        ·
          refine ⟨22404313147087674020270713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29872417529450232027027617 22404313147087674020270713)
          ·
            refine ⟨16803234860315755515203035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22404313147087674020270713 16803234860315755515203035)
            ·
              refine ⟨25204852290473633272804553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803234860315755515203035 25204852290473633272804553)
              ·
                refine ⟨18903639217855224954603415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25204852290473633272804553 18903639217855224954603415)
                ·
                  refine ⟨28355458826782837431905123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18903639217855224954603415 28355458826782837431905123)
                  ·
                    refine ⟨42533188240174256147857685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28355458826782837431905123 42533188240174256147857685)
                    ·
                      refine ⟨1993743198758168256930829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42533188240174256147857685 1993743198758168256930829)
                      ·
                        rfl

theorem cell23_3882801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3882801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882801 prefixEnd_3882801 := by exact prefixLift 3882801
  have htrace : WordTrace (prefixWord ++ tailWord_3882801) baseStart_3882801 baseEnd_3882801 := by
    simpa [prefixWord, tailWord_3882801, baseEnd_3882801] using wordTrace_append hprefix tailTrace_3882801
  have hstable : (prefixWord ++ tailWord_3882801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882801).length < 2 ^ (prefixWord ++ tailWord_3882801).sum := by decide
  have hdescent : baseEnd_3882801 < baseStart_3882801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882815 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 2, 4]
def baseStart_3882815 : Nat := 118140960795 + 3882815 * 2 ^ 59
def prefixEnd_3882815 : Nat := 4983230072969 + 3 ^ 40 * 3882815 * 2
def baseEnd_3882815 : Nat := 664583462495777067385255

theorem tailTrace_3882815 : CollatzResearch.WordTrace tailWord_3882815 prefixEnd_3882815 664583462495777067385255 := by
  unfold tailWord_3882815
  simp only [CollatzResearch.WordTrace]
  refine ⟨141617897428231861852473899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94411931618821241234982599 141617897428231861852473899)
  ·
    refine ⟨212426846142347792778710849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141617897428231861852473899 212426846142347792778710849)
    ·
      refine ⟨159320134606760844584033137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212426846142347792778710849 159320134606760844584033137)
      ·
        refine ⟨119490100955070633438024853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159320134606760844584033137 119490100955070633438024853)
        ·
          refine ⟨5601098482268935942407415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119490100955070633438024853 5601098482268935942407415)
          ·
            refine ⟨8401647723403403913611123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601098482268935942407415 8401647723403403913611123)
            ·
              refine ⟨12602471585105105870416685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401647723403403913611123 12602471585105105870416685)
              ·
                refine ⟨4725926844414414701406257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12602471585105105870416685 4725926844414414701406257)
                ·
                  refine ⟨3544445133310811026054693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725926844414414701406257 3544445133310811026054693)
                  ·
                    refine ⟨664583462495777067385255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544445133310811026054693 664583462495777067385255)
                    ·
                      rfl

theorem cell23_3882815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_3882815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882815 prefixEnd_3882815 := by exact prefixLift 3882815
  have htrace : WordTrace (prefixWord ++ tailWord_3882815) baseStart_3882815 baseEnd_3882815 := by
    simpa [prefixWord, tailWord_3882815, baseEnd_3882815] using wordTrace_append hprefix tailTrace_3882815
  have hstable : (prefixWord ++ tailWord_3882815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882815).length < 2 ^ (prefixWord ++ tailWord_3882815).sum := by decide
  have hdescent : baseEnd_3882815 < baseStart_3882815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882822 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3882822 : Nat := 118140960795 + 3882822 * 2 ^ 59
def prefixEnd_3882822 : Nat := 4983230072969 + 3 ^ 40 * 3882822 * 2
def baseEnd_3882822 : Nat := 1993753981851912674768233

theorem tailTrace_3882822 : CollatzResearch.WordTrace tailWord_3882822 prefixEnd_3882822 1993753981851912674768233 := by
  unfold tailWord_3882822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425567273100203188999335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94412101826137668031985813 4425567273100203188999335)
  ·
    refine ⟨6638350909650304783499003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425567273100203188999335 6638350909650304783499003)
    ·
      refine ⟨9957526364475457175248505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638350909650304783499003 9957526364475457175248505)
      ·
        refine ⟨7468144773356592881436379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9957526364475457175248505 7468144773356592881436379)
        ·
          refine ⟨11202217160034889322154569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468144773356592881436379 11202217160034889322154569)
          ·
            refine ⟨8401662870026166991615927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202217160034889322154569 8401662870026166991615927)
            ·
              refine ⟨12602494305039250487423891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401662870026166991615927 12602494305039250487423891)
              ·
                refine ⟨18903741457558875731135837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12602494305039250487423891 18903741457558875731135837)
                ·
                  refine ⟨7088903046584578399175939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18903741457558875731135837 7088903046584578399175939)
                  ·
                    refine ⟨10633354569876867598763909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7088903046584578399175939 10633354569876867598763909)
                    ·
                      refine ⟨1993753981851912674768233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10633354569876867598763909 1993753981851912674768233)
                      ·
                        rfl

theorem cell23_3882822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3882822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882822 prefixEnd_3882822 := by exact prefixLift 3882822
  have htrace : WordTrace (prefixWord ++ tailWord_3882822) baseStart_3882822 baseEnd_3882822 := by
    simpa [prefixWord, tailWord_3882822, baseEnd_3882822] using wordTrace_append hprefix tailTrace_3882822
  have hstable : (prefixWord ++ tailWord_3882822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882822).length < 2 ^ (prefixWord ++ tailWord_3882822).sum := by decide
  have hdescent : baseEnd_3882822 < baseStart_3882822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882891 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_3882891 : Nat := 118140960795 + 3882891 * 2 ^ 59
def prefixEnd_3882891 : Nat := 4983230072969 + 3 ^ 40 * 3882891 * 2
def baseEnd_3882891 : Nat := 1993789412017072904805415

theorem tailTrace_3882891 : CollatzResearch.WordTrace tailWord_3882891 prefixEnd_3882891 1993789412017072904805415 := by
  unfold tailWord_3882891
  simp only [CollatzResearch.WordTrace]
  refine ⟨141620669375956526832240527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94413779583971017888160351 141620669375956526832240527)
  ·
    refine ⟨212431004063934790248360791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141620669375956526832240527 212431004063934790248360791)
    ·
      refine ⟨318646506095902185372541187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212431004063934790248360791 318646506095902185372541187)
      ·
        refine ⟨477969759143853278058811781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318646506095902185372541187 477969759143853278058811781)
        ·
          refine ⟨89619329839472489636027209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477969759143853278058811781 89619329839472489636027209)
          ·
            refine ⟨67214497379604367227020407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89619329839472489636027209 67214497379604367227020407)
            ·
              refine ⟨100821746069406550840530611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67214497379604367227020407 100821746069406550840530611)
              ·
                refine ⟨151232619104109826260795917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100821746069406550840530611 151232619104109826260795917)
                ·
                  refine ⟨56712232164041184847798469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151232619104109826260795917 56712232164041184847798469)
                  ·
                    refine ⟨10633543530757722158962213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56712232164041184847798469 10633543530757722158962213)
                    ·
                      refine ⟨1993789412017072904805415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10633543530757722158962213 1993789412017072904805415)
                      ·
                        rfl

theorem cell23_3882891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_3882891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882891 prefixEnd_3882891 := by exact prefixLift 3882891
  have htrace : WordTrace (prefixWord ++ tailWord_3882891) baseStart_3882891 baseEnd_3882891 := by
    simpa [prefixWord, tailWord_3882891, baseEnd_3882891] using wordTrace_append hprefix tailTrace_3882891
  have hstable : (prefixWord ++ tailWord_3882891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882891).length < 2 ^ (prefixWord ++ tailWord_3882891).sum := by decide
  have hdescent : baseEnd_3882891 < baseStart_3882891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882901 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 9]
def baseStart_3882901 : Nat := 118140960795 + 3882901 * 2 ^ 59
def prefixEnd_3882901 : Nat := 4983230072969 + 3 ^ 40 * 3882901 * 2
def baseEnd_3882901 : Nat := 221532727424846429520041

theorem tailTrace_3882901 : CollatzResearch.WordTrace tailWord_3882901 prefixEnd_3882901 221532727424846429520041 := by
  unfold tailWord_3882901
  simp only [CollatzResearch.WordTrace]
  refine ⟨141621034105920298540104557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94414022737280199026736371 141621034105920298540104557)
  ·
    refine ⟨53107887789720111952539209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141621034105920298540104557 53107887789720111952539209)
    ·
      refine ⟨39830915842290083964404407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53107887789720111952539209 39830915842290083964404407)
      ·
        refine ⟨59746373763435125946606611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39830915842290083964404407 59746373763435125946606611)
        ·
          refine ⟨89619560645152688919909917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59746373763435125946606611 89619560645152688919909917)
          ·
            refine ⟨33607335241932258344966219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89619560645152688919909917 33607335241932258344966219)
            ·
              refine ⟨50411002862898387517449329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33607335241932258344966219 50411002862898387517449329)
              ·
                refine ⟨37808252147173790638086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50411002862898387517449329 37808252147173790638086997)
                ·
                  refine ⟨221532727424846429520041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37808252147173790638086997 221532727424846429520041)
                  ·
                    rfl

theorem cell23_3882901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_3882901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882901 prefixEnd_3882901 := by exact prefixLift 3882901
  have htrace : WordTrace (prefixWord ++ tailWord_3882901) baseStart_3882901 baseEnd_3882901 := by
    simpa [prefixWord, tailWord_3882901, baseEnd_3882901] using wordTrace_append hprefix tailTrace_3882901
  have hstable : (prefixWord ++ tailWord_3882901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882901).length < 2 ^ (prefixWord ++ tailWord_3882901).sum := by decide
  have hdescent : baseEnd_3882901 < baseStart_3882901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882931 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 7]
def baseStart_3882931 : Nat := 118140960795 + 3882931 * 2 ^ 59
def prefixEnd_3882931 : Nat := 4983230072969 + 3 ^ 40 * 3882931 * 2
def baseEnd_3882931 : Nat := 664603317081084249435077

theorem tailTrace_3882931 : CollatzResearch.WordTrace tailWord_3882931 prefixEnd_3882931 664603317081084249435077 := by
  unfold tailWord_3882931
  simp only [CollatzResearch.WordTrace]
  refine ⟨141622128295811613663696647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94414752197207742442464431 141622128295811613663696647)
  ·
    refine ⟨212433192443717420495544971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141622128295811613663696647 212433192443717420495544971)
    ·
      refine ⟨318649788665576130743317457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212433192443717420495544971 318649788665576130743317457)
      ·
        refine ⟨238987341499182098057488093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318649788665576130743317457 238987341499182098057488093)
        ·
          refine ⟨89620253062193286771558035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238987341499182098057488093 89620253062193286771558035)
          ·
            refine ⟨134430379593289930157337053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89620253062193286771558035 134430379593289930157337053)
            ·
              refine ⟨50411392347483723809001395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134430379593289930157337053 50411392347483723809001395)
              ·
                refine ⟨75617088521225585713502093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50411392347483723809001395 75617088521225585713502093)
                ·
                  refine ⟨28356408195459594642563285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75617088521225585713502093 28356408195459594642563285)
                  ·
                    refine ⟨664603317081084249435077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28356408195459594642563285 664603317081084249435077)
                    ·
                      rfl

theorem cell23_3882931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_3882931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882931 prefixEnd_3882931 := by exact prefixLift 3882931
  have htrace : WordTrace (prefixWord ++ tailWord_3882931) baseStart_3882931 baseEnd_3882931 := by
    simpa [prefixWord, tailWord_3882931, baseEnd_3882931] using wordTrace_append hprefix tailTrace_3882931
  have hstable : (prefixWord ++ tailWord_3882931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882931).length < 2 ^ (prefixWord ++ tailWord_3882931).sum := by decide
  have hdescent : baseEnd_3882931 < baseStart_3882931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882952 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 5]
def baseStart_3882952 : Nat := 118140960795 + 3882952 * 2 ^ 59
def prefixEnd_3882952 : Nat := 4983230072969 + 3 ^ 40 * 3882952 * 2
def baseEnd_3882952 : Nat := 221535637148555240682515

theorem tailTrace_3882952 : CollatzResearch.WordTrace tailWord_3882952 prefixEnd_3882952 221535637148555240682515 := by
  unfold tailWord_3882952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70811447114367767125105555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94415262819157022833474073 70811447114367767125105555)
  ·
    refine ⟨106217170671551650687658333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70811447114367767125105555 106217170671551650687658333)
    ·
      refine ⟨39831439001831869007871875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106217170671551650687658333 39831439001831869007871875)
      ·
        refine ⟨59747158502747803511807813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39831439001831869007871875 59747158502747803511807813)
        ·
          refine ⟨11202592219265213158463965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59747158502747803511807813 11202592219265213158463965)
          ·
            refine ⟨4200972082224454934423987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11202592219265213158463965 4200972082224454934423987)
            ·
              refine ⟨6301458123336682401635981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200972082224454934423987 6301458123336682401635981)
              ·
                refine ⟨2363046796251255900613493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6301458123336682401635981 2363046796251255900613493)
                ·
                  refine ⟨221535637148555240682515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2363046796251255900613493 221535637148555240682515)
                  ·
                    rfl

theorem cell23_3882952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 5].length) (baseStart_3882952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882952 prefixEnd_3882952 := by exact prefixLift 3882952
  have htrace : WordTrace (prefixWord ++ tailWord_3882952) baseStart_3882952 baseEnd_3882952 := by
    simpa [prefixWord, tailWord_3882952, baseEnd_3882952] using wordTrace_append hprefix tailTrace_3882952
  have hstable : (prefixWord ++ tailWord_3882952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882952).length < 2 ^ (prefixWord ++ tailWord_3882952).sum := by decide
  have hdescent : baseEnd_3882952 < baseStart_3882952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882958 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3882958 : Nat := 118140960795 + 3882958 * 2 ^ 59
def prefixEnd_3882958 : Nat := 4983230072969 + 3 ^ 40 * 3882958 * 2
def baseEnd_3882958 : Nat := 1993823815220924142667607

theorem tailTrace_3882958 : CollatzResearch.WordTrace tailWord_3882958 prefixEnd_3882958 1993823815220924142667607 := by
  unfold tailWord_3882958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702889133339224659366191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94415408711142531516619685 17702889133339224659366191)
  ·
    refine ⟨26554333700008836989049287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702889133339224659366191 26554333700008836989049287)
    ·
      refine ⟨39831500550013255483573931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26554333700008836989049287 39831500550013255483573931)
      ·
        refine ⟨59747250825019883225360897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39831500550013255483573931 59747250825019883225360897)
        ·
          refine ⟨44810438118764912419020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59747250825019883225360897 44810438118764912419020673)
          ·
            refine ⟨33607828589073684314265505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44810438118764912419020673 33607828589073684314265505)
            ·
              refine ⟨25205871441805263235699129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33607828589073684314265505 25205871441805263235699129)
              ·
                refine ⟨18904403581353947426774347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25205871441805263235699129 18904403581353947426774347)
                ·
                  refine ⟨28356605372030921140161521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18904403581353947426774347 28356605372030921140161521)
                  ·
                    refine ⟨21267454029023190855121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28356605372030921140161521 21267454029023190855121141)
                    ·
                      refine ⟨1993823815220924142667607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21267454029023190855121141 1993823815220924142667607)
                      ·
                        rfl

theorem cell23_3882958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3882958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882958 prefixEnd_3882958 := by exact prefixLift 3882958
  have htrace : WordTrace (prefixWord ++ tailWord_3882958) baseStart_3882958 baseEnd_3882958 := by
    simpa [prefixWord, tailWord_3882958, baseEnd_3882958] using wordTrace_append hprefix tailTrace_3882958
  have hstable : (prefixWord ++ tailWord_3882958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882958).length < 2 ^ (prefixWord ++ tailWord_3882958).sum := by decide
  have hdescent : baseEnd_3882958 < baseStart_3882958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882965 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3882965 : Nat := 118140960795 + 3882965 * 2 ^ 59
def prefixEnd_3882965 : Nat := 4983230072969 + 3 ^ 40 * 3882965 * 2
def baseEnd_3882965 : Nat := 664609136528501871760025

theorem tailTrace_3882965 : CollatzResearch.WordTrace tailWord_3882965 prefixEnd_3882965 664609136528501871760025 := by
  unfold tailWord_3882965
  simp only [CollatzResearch.WordTrace]
  refine ⟨141623368377688437470434349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94415578918458958313622899 141623368377688437470434349)
  ·
    refine ⟨53108763141633164051412881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141623368377688437470434349 53108763141633164051412881)
    ·
      refine ⟨39831572356224873038559661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53108763141633164051412881 39831572356224873038559661)
      ·
        refine ⟨14936839633584327389459873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39831572356224873038559661 14936839633584327389459873)
        ·
          refine ⟨11202629725188245542094905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14936839633584327389459873 11202629725188245542094905)
          ·
            refine ⟨8401972293891184156571179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202629725188245542094905 8401972293891184156571179)
            ·
              refine ⟨12602958440836776234856769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401972293891184156571179 12602958440836776234856769)
              ·
                refine ⟨9452218830627582176142577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12602958440836776234856769 9452218830627582176142577)
                ·
                  refine ⟨7089164122970686632106933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9452218830627582176142577 7089164122970686632106933)
                  ·
                    refine ⟨664609136528501871760025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7089164122970686632106933 664609136528501871760025)
                    ·
                      rfl

theorem cell23_3882965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3882965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882965 prefixEnd_3882965 := by exact prefixLift 3882965
  have htrace : WordTrace (prefixWord ++ tailWord_3882965) baseStart_3882965 baseEnd_3882965 := by
    simpa [prefixWord, tailWord_3882965, baseEnd_3882965] using wordTrace_append hprefix tailTrace_3882965
  have hstable : (prefixWord ++ tailWord_3882965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882965).length < 2 ^ (prefixWord ++ tailWord_3882965).sum := by decide
  have hdescent : baseEnd_3882965 < baseStart_3882965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3882988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_3882988 : Nat := 118140960795 + 3882988 * 2 ^ 59
def prefixEnd_3882988 : Nat := 4983230072969 + 3 ^ 40 * 3882988 * 2
def baseEnd_3882988 : Nat := 1993839219640559025292469

theorem tailTrace_3882988 : CollatzResearch.WordTrace tailWord_3882988 prefixEnd_3882988 1993839219640559025292469 := by
  unfold tailWord_3882988
  simp only [CollatzResearch.WordTrace]
  refine ⟨70812103628302556199260809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94416138171070074932347745 70812103628302556199260809)
  ·
    refine ⟨53109077721226917149445607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70812103628302556199260809 53109077721226917149445607)
    ·
      refine ⟨79663616581840375724168411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53109077721226917149445607 79663616581840375724168411)
      ·
        refine ⟨119495424872760563586252617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79663616581840375724168411 119495424872760563586252617)
        ·
          refine ⟨89621568654570422689689463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119495424872760563586252617 89621568654570422689689463)
          ·
            refine ⟨134432352981855634034534195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89621568654570422689689463 134432352981855634034534195)
            ·
              refine ⟨201648529472783451051801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134432352981855634034534195 201648529472783451051801293)
              ·
                refine ⟨75618198552293794144425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201648529472783451051801293 75618198552293794144425485)
                ·
                  refine ⟨28356824457110172804159557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75618198552293794144425485 28356824457110172804159557)
                  ·
                    refine ⟨5316904585708157400779917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28356824457110172804159557 5316904585708157400779917)
                    ·
                      refine ⟨1993839219640559025292469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5316904585708157400779917 1993839219640559025292469)
                      ·
                        rfl

theorem cell23_3882988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_3882988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3882988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3882988 prefixEnd_3882988 := by exact prefixLift 3882988
  have htrace : WordTrace (prefixWord ++ tailWord_3882988) baseStart_3882988 baseEnd_3882988 := by
    simpa [prefixWord, tailWord_3882988, baseEnd_3882988] using wordTrace_append hprefix tailTrace_3882988
  have hstable : (prefixWord ++ tailWord_3882988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3882988).length < 2 ^ (prefixWord ++ tailWord_3882988).sum := by decide
  have hdescent : baseEnd_3882988 < baseStart_3882988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3882988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883005 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_3883005 : Nat := 118140960795 + 3883005 * 2 ^ 59
def prefixEnd_3883005 : Nat := 4983230072969 + 3 ^ 40 * 3883005 * 2
def baseEnd_3883005 : Nat := 1993847948811685458779891

theorem tailTrace_3883005 : CollatzResearch.WordTrace tailWord_3883005 prefixEnd_3883005 1993847948811685458779891 := by
  unfold tailWord_3883005
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624827297543524301890469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94416551531695682867926979 141624827297543524301890469)
  ·
    refine ⟨26554655118289410806604463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141624827297543524301890469 26554655118289410806604463)
    ·
      refine ⟨39831982677434116209906695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26554655118289410806604463 39831982677434116209906695)
      ·
        refine ⟨59747974016151174314860043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39831982677434116209906695 59747974016151174314860043)
        ·
          refine ⟨89621961024226761472290065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59747974016151174314860043 89621961024226761472290065)
          ·
            refine ⟨67216470768170071104217549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89621961024226761472290065 67216470768170071104217549)
            ·
              refine ⟨25206176538063776664081581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67216470768170071104217549 25206176538063776664081581)
              ·
                refine ⟨9452316201773916249030593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25206176538063776664081581 9452316201773916249030593)
                ·
                  refine ⟨7089237151330437186772945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9452316201773916249030593 7089237151330437186772945)
                  ·
                    refine ⟨5316927863497827890079709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089237151330437186772945 5316927863497827890079709)
                    ·
                      refine ⟨1993847948811685458779891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5316927863497827890079709 1993847948811685458779891)
                      ·
                        rfl

theorem cell23_3883005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_3883005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883005 prefixEnd_3883005 := by exact prefixLift 3883005
  have htrace : WordTrace (prefixWord ++ tailWord_3883005) baseStart_3883005 baseEnd_3883005 := by
    simpa [prefixWord, tailWord_3883005, baseEnd_3883005] using wordTrace_append hprefix tailTrace_3883005
  have hstable : (prefixWord ++ tailWord_3883005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883005).length < 2 ^ (prefixWord ++ tailWord_3883005).sum := by decide
  have hdescent : baseEnd_3883005 < baseStart_3883005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883029 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3883029 : Nat := 118140960795 + 3883029 * 2 ^ 59
def prefixEnd_3883029 : Nat := 4983230072969 + 3 ^ 40 * 3883029 * 2
def baseEnd_3883029 : Nat := 664620090782464454959927

theorem tailTrace_3883029 : CollatzResearch.WordTrace tailWord_3883029 prefixEnd_3883029 664620090782464454959927 := by
  unfold tailWord_3883029
  simp only [CollatzResearch.WordTrace]
  refine ⟨141625702649456576400764141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94417135099637717600509427 141625702649456576400764141)
  ·
    refine ⟨53109638493546216150286553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141625702649456576400764141 53109638493546216150286553)
    ·
      refine ⟨39832228870159662112714915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53109638493546216150286553 39832228870159662112714915)
      ·
        refine ⟨59748343305239493169072373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39832228870159662112714915 59748343305239493169072373)
        ·
          refine ⟨5601407184866202484600535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59748343305239493169072373 5601407184866202484600535)
          ·
            refine ⟨8402110777299303726900803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601407184866202484600535 8402110777299303726900803)
            ·
              refine ⟨12603166165948955590351205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402110777299303726900803 12603166165948955590351205)
              ·
                refine ⟨2363093656115429173190851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12603166165948955590351205 2363093656115429173190851)
                ·
                  refine ⟨3544640484173143759786277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363093656115429173190851 3544640484173143759786277)
                  ·
                    refine ⟨664620090782464454959927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544640484173143759786277 664620090782464454959927)
                    ·
                      rfl

theorem cell23_3883029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3883029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883029 prefixEnd_3883029 := by exact prefixLift 3883029
  have htrace : WordTrace (prefixWord ++ tailWord_3883029) baseStart_3883029 baseEnd_3883029 := by
    simpa [prefixWord, tailWord_3883029, baseEnd_3883029] using wordTrace_append hprefix tailTrace_3883029
  have hstable : (prefixWord ++ tailWord_3883029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883029).length < 2 ^ (prefixWord ++ tailWord_3883029).sum := by decide
  have hdescent : baseEnd_3883029 < baseStart_3883029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883072 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_3883072 : Nat := 118140960795 + 3883072 * 2 ^ 59
def prefixEnd_3883072 : Nat := 4983230072969 + 3 ^ 40 * 3883072 * 2
def baseEnd_3883072 : Nat := 664627450671845565547361

theorem tailTrace_3883072 : CollatzResearch.WordTrace tailWord_3883072 prefixEnd_3883072 664627450671845565547361 := by
  unfold tailWord_3883072
  simp only [CollatzResearch.WordTrace]
  refine ⟨70813635494150397372289735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94418180658867196496386313 70813635494150397372289735)
  ·
    refine ⟨106220453241225596058434603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70813635494150397372289735 106220453241225596058434603)
    ·
      refine ⟨159330679861838394087651905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106220453241225596058434603 159330679861838394087651905)
      ·
        refine ⟨119498009896378795565738929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159330679861838394087651905 119498009896378795565738929)
        ·
          refine ⟨89623507422284096674304197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119498009896378795565738929 89623507422284096674304197)
          ·
            refine ⟨16804407641678268126432037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89623507422284096674304197 16804407641678268126432037)
            ·
              refine ⟨3150826432814675273706007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16804407641678268126432037 3150826432814675273706007)
              ·
                refine ⟨4726239649222012910559011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150826432814675273706007 4726239649222012910559011)
                ·
                  refine ⟨7089359473833019365838517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726239649222012910559011 7089359473833019365838517)
                  ·
                    refine ⟨664627450671845565547361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7089359473833019365838517 664627450671845565547361)
                    ·
                      rfl

theorem cell23_3883072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_3883072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883072 prefixEnd_3883072 := by exact prefixLift 3883072
  have htrace : WordTrace (prefixWord ++ tailWord_3883072) baseStart_3883072 baseEnd_3883072 := by
    simpa [prefixWord, tailWord_3883072, baseEnd_3883072] using wordTrace_append hprefix tailTrace_3883072
  have hstable : (prefixWord ++ tailWord_3883072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883072).length < 2 ^ (prefixWord ++ tailWord_3883072).sum := by decide
  have hdescent : baseEnd_3883072 < baseStart_3883072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883088 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_3883088 : Nat := 118140960795 + 3883088 * 2 ^ 59
def prefixEnd_3883088 : Nat := 4983230072969 + 3 ^ 40 * 3883088 * 2
def baseEnd_3883088 : Nat := 1993890567706008634042009

theorem tailTrace_3883088 : CollatzResearch.WordTrace tailWord_3883088 prefixEnd_3883088 1993890567706008634042009 := by
  unfold tailWord_3883088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70813927278121414738580959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94418569704161886318107945 70813927278121414738580959)
  ·
    refine ⟨106220890917182122107871439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70813927278121414738580959 106220890917182122107871439)
    ·
      refine ⟨159331336375773183161807159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106220890917182122107871439 159331336375773183161807159)
      ·
        refine ⟨238997004563659774742710739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159331336375773183161807159 238997004563659774742710739)
        ·
          refine ⟨358495506845489662114066109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238997004563659774742710739 358495506845489662114066109)
          ·
            refine ⟨134435815067058623292774791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358495506845489662114066109 134435815067058623292774791)
            ·
              refine ⟨201653722600587934939162187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134435815067058623292774791 201653722600587934939162187)
              ·
                refine ⟨302480583900881902408743281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201653722600587934939162187 302480583900881902408743281)
                ·
                  refine ⟨226860437925661426806557461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302480583900881902408743281 226860437925661426806557461)
                  ·
                    refine ⟨10634083027765379381557381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226860437925661426806557461 10634083027765379381557381)
                    ·
                      refine ⟨1993890567706008634042009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10634083027765379381557381 1993890567706008634042009)
                      ·
                        rfl

theorem cell23_3883088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_3883088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883088 prefixEnd_3883088 := by exact prefixLift 3883088
  have htrace : WordTrace (prefixWord ++ tailWord_3883088) baseStart_3883088 baseEnd_3883088 := by
    simpa [prefixWord, tailWord_3883088, baseEnd_3883088] using wordTrace_append hprefix tailTrace_3883088
  have hstable : (prefixWord ++ tailWord_3883088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883088).length < 2 ^ (prefixWord ++ tailWord_3883088).sum := by decide
  have hdescent : baseEnd_3883088 < baseStart_3883088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883095 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_3883095 : Nat := 118140960795 + 3883095 * 2 ^ 59
def prefixEnd_3883095 : Nat := 4983230072969 + 3 ^ 40 * 3883095 * 2
def baseEnd_3883095 : Nat := 1993894162070590106654477

theorem tailTrace_3883095 : CollatzResearch.WordTrace tailWord_3883095 prefixEnd_3883095 1993894162070590106654477 := by
  unfold tailWord_3883095
  simp only [CollatzResearch.WordTrace]
  refine ⟨141628109867217469672666739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94418739911478313115111159 141628109867217469672666739)
  ·
    refine ⟨212442164800826204509000109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141628109867217469672666739 212442164800826204509000109)
    ·
      refine ⟨79665811800309826690875041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212442164800826204509000109 79665811800309826690875041)
      ·
        refine ⟨59749358850232370018156281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79665811800309826690875041 59749358850232370018156281)
        ·
          refine ⟨44812019137674277513617211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59749358850232370018156281 44812019137674277513617211)
          ·
            refine ⟨67218028706511416270425817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44812019137674277513617211 67218028706511416270425817)
            ·
              refine ⟨50413521529883562202819363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67218028706511416270425817 50413521529883562202819363)
              ·
                refine ⟨75620282294825343304229045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50413521529883562202819363 75620282294825343304229045)
                ·
                  refine ⟨7089401465139875934771473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75620282294825343304229045 7089401465139875934771473)
                  ·
                    refine ⟨5317051098854906951078605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089401465139875934771473 5317051098854906951078605)
                    ·
                      refine ⟨1993894162070590106654477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317051098854906951078605 1993894162070590106654477)
                      ·
                        rfl

theorem cell23_3883095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_3883095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883095 prefixEnd_3883095 := by exact prefixLift 3883095
  have htrace : WordTrace (prefixWord ++ tailWord_3883095) baseStart_3883095 baseEnd_3883095 := by
    simpa [prefixWord, tailWord_3883095, baseEnd_3883095] using wordTrace_append hprefix tailTrace_3883095
  have hstable : (prefixWord ++ tailWord_3883095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883095).length < 2 ^ (prefixWord ++ tailWord_3883095).sum := by decide
  have hdescent : baseEnd_3883095 < baseStart_3883095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883098 : List Nat := [3, 1, 1, 2, 1, 1, 4, 10]
def baseStart_3883098 : Nat := 118140960795 + 3883098 * 2 ^ 59
def prefixEnd_3883098 : Nat := 4983230072969 + 3 ^ 40 * 3883098 * 2
def baseEnd_3883098 : Nat := 73847988981946429441369

theorem tailTrace_3883098 : CollatzResearch.WordTrace tailWord_3883098 prefixEnd_3883098 73847988981946429441369 := by
  unfold tailWord_3883098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407054821551650296256487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94418812857471067456683965 35407054821551650296256487)
  ·
    refine ⟨53110582232327475444384731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35407054821551650296256487 53110582232327475444384731)
    ·
      refine ⟨79665873348491213166577097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53110582232327475444384731 79665873348491213166577097)
      ·
        refine ⟨59749405011368409874932823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79665873348491213166577097 59749405011368409874932823)
        ·
          refine ⟨89624107517052614812399235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59749405011368409874932823 89624107517052614812399235)
          ·
            refine ⟨134436161275578922218598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89624107517052614812399235 134436161275578922218598853)
            ·
              refine ⟨25206780239171047915987285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134436161275578922218598853 25206780239171047915987285)
              ·
                refine ⟨73847988981946429441369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25206780239171047915987285 73847988981946429441369)
                ·
                  rfl

theorem cell23_3883098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_3883098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883098 prefixEnd_3883098 := by exact prefixLift 3883098
  have htrace : WordTrace (prefixWord ++ tailWord_3883098) baseStart_3883098 baseEnd_3883098 := by
    simpa [prefixWord, tailWord_3883098, baseEnd_3883098] using wordTrace_append hprefix tailTrace_3883098
  have hstable : (prefixWord ++ tailWord_3883098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883098).length < 2 ^ (prefixWord ++ tailWord_3883098).sum := by decide
  have hdescent : baseEnd_3883098 < baseStart_3883098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883109 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_3883109 : Nat := 118140960795 + 3883109 * 2 ^ 59
def prefixEnd_3883109 : Nat := 4983230072969 + 3 ^ 40 * 3883109 * 2
def baseEnd_3883109 : Nat := 1993901350799753051879413

theorem tailTrace_3883109 : CollatzResearch.WordTrace tailWord_3883109 prefixEnd_3883109 1993901350799753051879413 := by
  unfold tailWord_3883109
  simp only [CollatzResearch.WordTrace]
  refine ⟨141628620489166750063676381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94419080326111166709117587 141628620489166750063676381)
  ·
    refine ⟨53110732683437531273878643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141628620489166750063676381 53110732683437531273878643)
    ·
      refine ⟨79666099025156296910817965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53110732683437531273878643 79666099025156296910817965)
      ·
        refine ⟨29874787134433611341556737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79666099025156296910817965 29874787134433611341556737)
        ·
          refine ⟨22406090350825208506167553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29874787134433611341556737 22406090350825208506167553)
          ·
            refine ⟨16804567763118906379625665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22406090350825208506167553 16804567763118906379625665)
            ·
              refine ⟨12603425822339179784719249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16804567763118906379625665 12603425822339179784719249)
              ·
                refine ⟨9452569366754384838539437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12603425822339179784719249 9452569366754384838539437)
                ·
                  refine ⟨3544713512532894314452289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9452569366754384838539437 3544713512532894314452289)
                  ·
                    refine ⟨2658535134399670735839217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3544713512532894314452289 2658535134399670735839217)
                    ·
                      refine ⟨1993901350799753051879413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658535134399670735839217 1993901350799753051879413)
                      ·
                        rfl

theorem cell23_3883109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_3883109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883109 prefixEnd_3883109 := by exact prefixLift 3883109
  have htrace : WordTrace (prefixWord ++ tailWord_3883109) baseStart_3883109 baseEnd_3883109 := by
    simpa [prefixWord, tailWord_3883109, baseEnd_3883109] using wordTrace_append hprefix tailTrace_3883109
  have hstable : (prefixWord ++ tailWord_3883109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883109).length < 2 ^ (prefixWord ++ tailWord_3883109).sum := by decide
  have hdescent : baseEnd_3883109 < baseStart_3883109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883128 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_3883128 : Nat := 118140960795 + 3883128 * 2 ^ 59
def prefixEnd_3883128 : Nat := 4983230072969 + 3 ^ 40 * 3883128 * 2
def baseEnd_3883128 : Nat := 664637035644062825847275

theorem tailTrace_3883128 : CollatzResearch.WordTrace tailWord_3883128 prefixEnd_3883128 664637035644062825847275 := by
  unfold tailWord_3883128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70814656738048958154309019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94419542317398610872412025 70814656738048958154309019)
  ·
    refine ⟨106221985107073437231463529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70814656738048958154309019 106221985107073437231463529)
    ·
      refine ⟨79666488830305077923597647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106221985107073437231463529 79666488830305077923597647)
      ·
        refine ⟨119499733245457616885396471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79666488830305077923597647 119499733245457616885396471)
        ·
          refine ⟨179249599868186425328094707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119499733245457616885396471 179249599868186425328094707)
          ·
            refine ⟨268874399802279637992142061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179249599868186425328094707 268874399802279637992142061)
            ·
              refine ⟨100827899925854864247053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268874399802279637992142061 100827899925854864247053273)
              ·
                refine ⟨75620924944391148185289955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100827899925854864247053273 75620924944391148185289955)
                ·
                  refine ⟨113431387416586722277934933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75620924944391148185289955 113431387416586722277934933)
                  ·
                    refine ⟨664637035644062825847275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113431387416586722277934933 664637035644062825847275)
                    ·
                      rfl

theorem cell23_3883128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_3883128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883128 prefixEnd_3883128 := by exact prefixLift 3883128
  have htrace : WordTrace (prefixWord ++ tailWord_3883128) baseStart_3883128 baseEnd_3883128 := by
    simpa [prefixWord, tailWord_3883128, baseEnd_3883128] using wordTrace_append hprefix tailTrace_3883128
  have hstable : (prefixWord ++ tailWord_3883128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883128).length < 2 ^ (prefixWord ++ tailWord_3883128).sum := by decide
  have hdescent : baseEnd_3883128 < baseStart_3883128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883152 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2]
def baseStart_3883152 : Nat := 118140960795 + 3883152 * 2 ^ 59
def prefixEnd_3883152 : Nat := 4983230072969 + 3 ^ 40 * 3883152 * 2
def baseEnd_3883152 : Nat := 1993923430467896383641715

theorem tailTrace_3883152 : CollatzResearch.WordTrace tailWord_3883152 prefixEnd_3883152 1993923430467896383641715 := by
  unfold tailWord_3883152
  simp only [CollatzResearch.WordTrace]
  refine ⟨70815094414005484203745855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94420125885340645604994473 70815094414005484203745855)
  ·
    refine ⟨106222641621008226305618783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70815094414005484203745855 106222641621008226305618783)
    ·
      refine ⟨159333962431512339458428175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106222641621008226305618783 159333962431512339458428175)
      ·
        refine ⟨239000943647268509187642263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159333962431512339458428175 239000943647268509187642263)
        ·
          refine ⟨358501415470902763781463395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239000943647268509187642263 358501415470902763781463395)
          ·
            refine ⟨537752123206354145672195093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358501415470902763781463395 537752123206354145672195093)
            ·
              refine ⟨25207130775297850578384145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 537752123206354145672195093 25207130775297850578384145)
              ·
                refine ⟨18905348081473387933788109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25207130775297850578384145 18905348081473387933788109)
                ·
                  refine ⟨7089505530552520475170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18905348081473387933788109 7089505530552520475170541)
                  ·
                    refine ⟨2658564573957195178188953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7089505530552520475170541 2658564573957195178188953)
                    ·
                      refine ⟨1993923430467896383641715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658564573957195178188953 1993923430467896383641715)
                      ·
                        rfl

theorem cell23_3883152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2].length) (baseStart_3883152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883152 prefixEnd_3883152 := by exact prefixLift 3883152
  have htrace : WordTrace (prefixWord ++ tailWord_3883152) baseStart_3883152 baseEnd_3883152 := by
    simpa [prefixWord, tailWord_3883152, baseEnd_3883152] using wordTrace_append hprefix tailTrace_3883152
  have hstable : (prefixWord ++ tailWord_3883152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883152).length < 2 ^ (prefixWord ++ tailWord_3883152).sum := by decide
  have hdescent : baseEnd_3883152 < baseStart_3883152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883169 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3883169 : Nat := 118140960795 + 3883169 * 2 ^ 59
def prefixEnd_3883169 : Nat := 4983230072969 + 3 ^ 40 * 3883169 * 2
def baseEnd_3883169 : Nat := 1993932159639022817129137

theorem tailTrace_3883169 : CollatzResearch.WordTrace tailWord_3883169 prefixEnd_3883169 1993932159639022817129137 := by
  unfold tailWord_3883169
  simp only [CollatzResearch.WordTrace]
  refine ⟨141630808868949380310860561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94420539245966253540573707 141630808868949380310860561)
  ·
    refine ⟨106223106651712035233145421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141630808868949380310860561 106223106651712035233145421)
    ·
      refine ⟨39833664994392013212429533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106223106651712035233145421 39833664994392013212429533)
      ·
        refine ⟨14937624372897004954661075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39833664994392013212429533 14937624372897004954661075)
        ·
          refine ⟨22406436559345507431991613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14937624372897004954661075 22406436559345507431991613)
          ·
            refine ⟨8402413709754565286996855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22406436559345507431991613 8402413709754565286996855)
            ·
              refine ⟨12603620564631847930495283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402413709754565286996855 12603620564631847930495283)
              ·
                refine ⟨18905430846947771895742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603620564631847930495283 18905430846947771895742925)
                ·
                  refine ⟨7089536567605414460903597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18905430846947771895742925 7089536567605414460903597)
                  ·
                    refine ⟨2658576212852030422838849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7089536567605414460903597 2658576212852030422838849)
                    ·
                      refine ⟨1993932159639022817129137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658576212852030422838849 1993932159639022817129137)
                      ·
                        rfl

theorem cell23_3883169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3883169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883169 prefixEnd_3883169 := by exact prefixLift 3883169
  have htrace : WordTrace (prefixWord ++ tailWord_3883169) baseStart_3883169 baseEnd_3883169 := by
    simpa [prefixWord, tailWord_3883169, baseEnd_3883169] using wordTrace_append hprefix tailTrace_3883169
  have hstable : (prefixWord ++ tailWord_3883169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883169).length < 2 ^ (prefixWord ++ tailWord_3883169).sum := by decide
  have hdescent : baseEnd_3883169 < baseStart_3883169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883186 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_3883186 : Nat := 118140960795 + 3883186 * 2 ^ 59
def prefixEnd_3883186 : Nat := 4983230072969 + 3 ^ 40 * 3883186 * 2
def baseEnd_3883186 : Nat := 1993940888810149250616559

theorem tailTrace_3883186 : CollatzResearch.WordTrace tailWord_3883186 prefixEnd_3883186 1993940888810149250616559 := by
  unfold tailWord_3883186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407857227471948053557353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94420952606591861476152941 35407857227471948053557353)
  ·
    refine ⟨26555892920603961040168015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35407857227471948053557353 26555892920603961040168015)
    ·
      refine ⟨39833839380905941560252023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26555892920603961040168015 39833839380905941560252023)
      ·
        refine ⟨59750759071358912340378035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39833839380905941560252023 59750759071358912340378035)
        ·
          refine ⟨89626138607038368510567053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59750759071358912340378035 89626138607038368510567053)
          ·
            refine ⟨33609801977639388191462645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89626138607038368510567053 33609801977639388191462645)
            ·
              refine ⟨3150918935403692642949623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33609801977639388191462645 3150918935403692642949623)
              ·
                refine ⟨4726378403105538964424435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150918935403692642949623 4726378403105538964424435)
                ·
                  refine ⟨7089567604658308446636653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726378403105538964424435 7089567604658308446636653)
                  ·
                    refine ⟨2658587851746865667488745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7089567604658308446636653 2658587851746865667488745)
                    ·
                      refine ⟨1993940888810149250616559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658587851746865667488745 1993940888810149250616559)
                      ·
                        rfl

theorem cell23_3883186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_3883186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883186 prefixEnd_3883186 := by exact prefixLift 3883186
  have htrace : WordTrace (prefixWord ++ tailWord_3883186) baseStart_3883186 baseEnd_3883186 := by
    simpa [prefixWord, tailWord_3883186, baseEnd_3883186] using wordTrace_append hprefix tailTrace_3883186
  have hstable : (prefixWord ++ tailWord_3883186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883186).length < 2 ^ (prefixWord ++ tailWord_3883186).sum := by decide
  have hdescent : baseEnd_3883186 < baseStart_3883186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883195 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_3883195 : Nat := 118140960795 + 3883195 * 2 ^ 59
def prefixEnd_3883195 : Nat := 4983230072969 + 3 ^ 40 * 3883195 * 2
def baseEnd_3883195 : Nat := 1993945510136039715404017

theorem tailTrace_3883195 : CollatzResearch.WordTrace tailWord_3883195 prefixEnd_3883195 1993945510136039715404017 := by
  unfold tailWord_3883195
  simp only [CollatzResearch.WordTrace]
  refine ⟨141631757166855186751307039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94421171444570124500871359 141631757166855186751307039)
  ·
    refine ⟨212447635750282780126960559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141631757166855186751307039 212447635750282780126960559)
    ·
      refine ⟨318671453625424170190440839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212447635750282780126960559 318671453625424170190440839)
      ·
        refine ⟨478007180438136255285661259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318671453625424170190440839 478007180438136255285661259)
        ·
          refine ⟨717010770657204382928491889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478007180438136255285661259 717010770657204382928491889)
          ·
            refine ⟨537758077992903287196368917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717010770657204382928491889 537758077992903287196368917)
            ·
              refine ⟨25207409905917341587329793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 537758077992903287196368917 25207409905917341587329793)
              ·
                refine ⟨18905557429438006190497345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25207409905917341587329793 18905557429438006190497345)
                ·
                  refine ⟨14179168072078504642873009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18905557429438006190497345 14179168072078504642873009)
                  ·
                    refine ⟨10634376054058878482154757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14179168072078504642873009 10634376054058878482154757)
                    ·
                      refine ⟨1993945510136039715404017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10634376054058878482154757 1993945510136039715404017)
                      ·
                        rfl

theorem cell23_3883195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_3883195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883195 prefixEnd_3883195 := by exact prefixLift 3883195
  have htrace : WordTrace (prefixWord ++ tailWord_3883195) baseStart_3883195 baseEnd_3883195 := by
    simpa [prefixWord, tailWord_3883195, baseEnd_3883195] using wordTrace_append hprefix tailTrace_3883195
  have hstable : (prefixWord ++ tailWord_3883195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883195).length < 2 ^ (prefixWord ++ tailWord_3883195).sum := by decide
  have hdescent : baseEnd_3883195 < baseStart_3883195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883239 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 5]
def baseStart_3883239 : Nat := 118140960795 + 3883239 * 2 ^ 59
def prefixEnd_3883239 : Nat := 4983230072969 + 3 ^ 40 * 3883239 * 2
def baseEnd_3883239 : Nat := 221552011476093060361535

theorem tailTrace_3883239 : CollatzResearch.WordTrace tailWord_3883239 prefixEnd_3883239 221552011476093060361535 := by
  unfold tailWord_3883239
  simp only [CollatzResearch.WordTrace]
  refine ⟨141633361978695782265908771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94422241319130521510605847 141633361978695782265908771)
  ·
    refine ⟨212450042968043673398863157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141633361978695782265908771 212450042968043673398863157)
    ·
      refine ⟨19917191528254094381143421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212450042968043673398863157 19917191528254094381143421)
      ·
        refine ⟨7468946823095285392928783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19917191528254094381143421 7468946823095285392928783)
        ·
          refine ⟨11203420234642928089393175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468946823095285392928783 11203420234642928089393175)
          ·
            refine ⟨16805130351964392134089763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203420234642928089393175 16805130351964392134089763)
            ·
              refine ⟨25207695527946588201134645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805130351964392134089763 25207695527946588201134645)
              ·
                refine ⟨2363221455744992643856373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25207695527946588201134645 2363221455744992643856373)
                ·
                  refine ⟨221552011476093060361535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2363221455744992643856373 221552011476093060361535)
                  ·
                    rfl

theorem cell23_3883239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 5].length) (baseStart_3883239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883239 prefixEnd_3883239 := by exact prefixLift 3883239
  have htrace : WordTrace (prefixWord ++ tailWord_3883239) baseStart_3883239 baseEnd_3883239 := by
    simpa [prefixWord, tailWord_3883239, baseEnd_3883239] using wordTrace_append hprefix tailTrace_3883239
  have hstable : (prefixWord ++ tailWord_3883239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883239).length < 2 ^ (prefixWord ++ tailWord_3883239).sum := by decide
  have hdescent : baseEnd_3883239 < baseStart_3883239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883255 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_3883255 : Nat := 118140960795 + 3883255 * 2 ^ 59
def prefixEnd_3883255 : Nat := 4983230072969 + 3 ^ 40 * 3883255 * 2
def baseEnd_3883255 : Nat := 1993976318975309480653741

theorem tailTrace_3883255 : CollatzResearch.WordTrace tailWord_3883255 prefixEnd_3883255 1993976318975309480653741 := by
  unfold tailWord_3883255
  simp only [CollatzResearch.WordTrace]
  refine ⟨141633945546637816998491219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94422630364425211332327479 141633945546637816998491219)
  ·
    refine ⟨212450918319956725497736829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141633945546637816998491219 212450918319956725497736829)
    ·
      refine ⟨79669094369983772061651311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212450918319956725497736829 79669094369983772061651311)
      ·
        refine ⟨119503641554975658092476967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79669094369983772061651311 119503641554975658092476967)
        ·
          refine ⟨179255462332463487138715451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119503641554975658092476967 179255462332463487138715451)
          ·
            refine ⟨268883193498695230708073177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179255462332463487138715451 268883193498695230708073177)
            ·
              refine ⟨201662395124021423031054883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268883193498695230708073177 201662395124021423031054883)
              ·
                refine ⟨302493592686032134546582325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201662395124021423031054883 302493592686032134546582325)
                ·
                  refine ⟨28358774314315512613742093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302493592686032134546582325 28358774314315512613742093)
                  ·
                    refine ⟨10634540367868317230153285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28358774314315512613742093 10634540367868317230153285)
                    ·
                      refine ⟨1993976318975309480653741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10634540367868317230153285 1993976318975309480653741)
                      ·
                        rfl

theorem cell23_3883255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_3883255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883255 prefixEnd_3883255 := by exact prefixLift 3883255
  have htrace : WordTrace (prefixWord ++ tailWord_3883255) baseStart_3883255 baseEnd_3883255 := by
    simpa [prefixWord, tailWord_3883255, baseEnd_3883255] using wordTrace_append hprefix tailTrace_3883255
  have hstable : (prefixWord ++ tailWord_3883255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883255).length < 2 ^ (prefixWord ++ tailWord_3883255).sum := by decide
  have hdescent : baseEnd_3883255 < baseStart_3883255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883262 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3883262 : Nat := 118140960795 + 3883262 * 2 ^ 59
def prefixEnd_3883262 : Nat := 4983230072969 + 3 ^ 40 * 3883262 * 2
def baseEnd_3883262 : Nat := 1993979913339890953266209

theorem tailTrace_3883262 : CollatzResearch.WordTrace tailWord_3883262 prefixEnd_3883262 1993979913339890953266209 := by
  unfold tailWord_3883262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704275107201557149249505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94422800571741638129330693 17704275107201557149249505)
  ·
    refine ⟨13278206330401167861937129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17704275107201557149249505 13278206330401167861937129)
    ·
      refine ⟨9958654747800875896452847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13278206330401167861937129 9958654747800875896452847)
      ·
        refine ⟨14937982121701313844679271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9958654747800875896452847 14937982121701313844679271)
        ·
          refine ⟨22406973182551970767018907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14937982121701313844679271 22406973182551970767018907)
          ·
            refine ⟨33610459773827956150528361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22406973182551970767018907 33610459773827956150528361)
            ·
              refine ⟨25207844830370967112896271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33610459773827956150528361 25207844830370967112896271)
              ·
                refine ⟨37811767245556450669344407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25207844830370967112896271 37811767245556450669344407)
                ·
                  refine ⟨56717650868334676004016611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37811767245556450669344407 56717650868334676004016611)
                  ·
                    refine ⟨85076476302502014006024917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56717650868334676004016611 85076476302502014006024917)
                    ·
                      refine ⟨1993979913339890953266209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85076476302502014006024917 1993979913339890953266209)
                      ·
                        rfl

theorem cell23_3883262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3883262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883262 prefixEnd_3883262 := by exact prefixLift 3883262
  have htrace : WordTrace (prefixWord ++ tailWord_3883262) baseStart_3883262 baseEnd_3883262 := by
    simpa [prefixWord, tailWord_3883262, baseEnd_3883262] using wordTrace_append hprefix tailTrace_3883262
  have hstable : (prefixWord ++ tailWord_3883262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883262).length < 2 ^ (prefixWord ++ tailWord_3883262).sum := by decide
  have hdescent : baseEnd_3883262 < baseStart_3883262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883272 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3883272 : Nat := 118140960795 + 3883272 * 2 ^ 59
def prefixEnd_3883272 : Nat := 4983230072969 + 3 ^ 40 * 3883272 * 2
def baseEnd_3883272 : Nat := 1993985048146435914141163

theorem tailTrace_3883272 : CollatzResearch.WordTrace tailWord_3883272 prefixEnd_3883272 1993985048146435914141163 := by
  unfold tailWord_3883272
  simp only [CollatzResearch.WordTrace]
  refine ⟨70817282793788114450930035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94423043725050819267906713 70817282793788114450930035)
  ·
    refine ⟨106225924190682171676395053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70817282793788114450930035 106225924190682171676395053)
    ·
      refine ⟨39834721571505814378648145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106225924190682171676395053 39834721571505814378648145)
      ·
        refine ⟨29876041178629360783986109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39834721571505814378648145 29876041178629360783986109)
        ·
          refine ⟨11203515441986010293994791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29876041178629360783986109 11203515441986010293994791)
          ·
            refine ⟨16805273162979015440992187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203515441986010293994791 16805273162979015440992187)
            ·
              refine ⟨25207909744468523161488281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805273162979015440992187 25207909744468523161488281)
              ·
                refine ⟨18905932308351392371116211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25207909744468523161488281 18905932308351392371116211)
                ·
                  refine ⟨28358898462527088556674317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18905932308351392371116211 28358898462527088556674317)
                  ·
                    refine ⟨10634586923447658208752869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28358898462527088556674317 10634586923447658208752869)
                    ·
                      refine ⟨1993985048146435914141163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10634586923447658208752869 1993985048146435914141163)
                      ·
                        rfl

theorem cell23_3883272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3883272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883272 prefixEnd_3883272 := by exact prefixLift 3883272
  have htrace : WordTrace (prefixWord ++ tailWord_3883272) baseStart_3883272 baseEnd_3883272 := by
    simpa [prefixWord, tailWord_3883272, baseEnd_3883272] using wordTrace_append hprefix tailTrace_3883272
  have hstable : (prefixWord ++ tailWord_3883272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883272).length < 2 ^ (prefixWord ++ tailWord_3883272).sum := by decide
  have hdescent : baseEnd_3883272 < baseStart_3883272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883303 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3883303 : Nat := 118140960795 + 3883303 * 2 ^ 59
def prefixEnd_3883303 : Nat := 4983230072969 + 3 ^ 40 * 3883303 * 2
def baseEnd_3883303 : Nat := 664666988682241764284507

theorem tailTrace_3883303 : CollatzResearch.WordTrace tailWord_3883303 prefixEnd_3883303 664666988682241764284507 := by
  unfold tailWord_3883303
  simp only [CollatzResearch.WordTrace]
  refine ⟨141635696250463921196238563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94423797500309280797492375 141635696250463921196238563)
  ·
    refine ⟨212453544375695881794357845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141635696250463921196238563 212453544375695881794357845)
    ·
      refine ⟨2489689973152686114777631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 212453544375695881794357845 2489689973152686114777631)
      ·
        refine ⟨3734534959729029172166447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489689973152686114777631 3734534959729029172166447)
        ·
          refine ⟨5601802439593543758249671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734534959729029172166447 5601802439593543758249671)
          ·
            refine ⟨8402703659390315637374507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601802439593543758249671 8402703659390315637374507)
            ·
              refine ⟨12604055489085473456061761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402703659390315637374507 12604055489085473456061761)
              ·
                refine ⟨9453041616814105092046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604055489085473456061761 9453041616814105092046321)
                ·
                  refine ⟨7089781212610578819034741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453041616814105092046321 7089781212610578819034741)
                  ·
                    refine ⟨664666988682241764284507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7089781212610578819034741 664666988682241764284507)
                    ·
                      rfl

theorem cell23_3883303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3883303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883303 prefixEnd_3883303 := by exact prefixLift 3883303
  have htrace : WordTrace (prefixWord ++ tailWord_3883303) baseStart_3883303 baseEnd_3883303 := by
    simpa [prefixWord, tailWord_3883303, baseEnd_3883303] using wordTrace_append hprefix tailTrace_3883303
  have hstable : (prefixWord ++ tailWord_3883303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883303).length < 2 ^ (prefixWord ++ tailWord_3883303).sum := by decide
  have hdescent : baseEnd_3883303 < baseStart_3883303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883306 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3883306 : Nat := 118140960795 + 3883306 * 2 ^ 59
def prefixEnd_3883306 : Nat := 4983230072969 + 3 ^ 40 * 3883306 * 2
def baseEnd_3883306 : Nat := 1994002506488688781116007

theorem tailTrace_3883306 : CollatzResearch.WordTrace tailWord_3883306 prefixEnd_3883306 1994002506488688781116007 := by
  unfold tailWord_3883306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35408951417363263177149443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94423870446302035139065181 35408951417363263177149443)
  ·
    refine ⟨53113427126044894765724165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35408951417363263177149443 53113427126044894765724165)
    ·
      refine ⟨9958767586133417768573281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53113427126044894765724165 9958767586133417768573281)
      ·
        refine ⟨7469075689600063326429961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9958767586133417768573281 7469075689600063326429961)
        ·
          refine ⟨5601806767200047494822471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469075689600063326429961 5601806767200047494822471)
          ·
            refine ⟨8402710150800071242233707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601806767200047494822471 8402710150800071242233707)
            ·
              refine ⟨12604065226200106863350561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402710150800071242233707 12604065226200106863350561)
              ·
                refine ⟨9453048919650080147512921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604065226200106863350561 9453048919650080147512921)
                ·
                  refine ⟨7089786689737560110634691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453048919650080147512921 7089786689737560110634691)
                  ·
                    refine ⟨10634680034606340165952037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7089786689737560110634691 10634680034606340165952037)
                    ·
                      refine ⟨1994002506488688781116007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10634680034606340165952037 1994002506488688781116007)
                      ·
                        rfl

theorem cell23_3883306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3883306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883306 prefixEnd_3883306 := by exact prefixLift 3883306
  have htrace : WordTrace (prefixWord ++ tailWord_3883306) baseStart_3883306 baseEnd_3883306 := by
    simpa [prefixWord, tailWord_3883306, baseEnd_3883306] using wordTrace_append hprefix tailTrace_3883306
  have hstable : (prefixWord ++ tailWord_3883306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883306).length < 2 ^ (prefixWord ++ tailWord_3883306).sum := by decide
  have hdescent : baseEnd_3883306 < baseStart_3883306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883316 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3883316 : Nat := 118140960795 + 3883316 * 2 ^ 59
def prefixEnd_3883316 : Nat := 4983230072969 + 3 ^ 40 * 3883316 * 2
def baseEnd_3883316 : Nat := 664669213765077913996987

theorem tailTrace_3883316 : CollatzResearch.WordTrace tailWord_3883316 prefixEnd_3883316 664669213765077913996987 := by
  unfold tailWord_3883316
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818085199708412208230901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94424113599611216277641201 70818085199708412208230901)
  ·
    refine ⟨6639195487472663644521647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70818085199708412208230901 6639195487472663644521647)
    ·
      refine ⟨9958793231208995466782471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639195487472663644521647 9958793231208995466782471)
      ·
        refine ⟨14938189846813493200173707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9958793231208995466782471 14938189846813493200173707)
        ·
          refine ⟨22407284770220239800260561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14938189846813493200173707 22407284770220239800260561)
          ·
            refine ⟨16805463577665179850195421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22407284770220239800260561 16805463577665179850195421)
            ·
              refine ⟨6302048841624442443823283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16805463577665179850195421 6302048841624442443823283)
              ·
                refine ⟨9453073262436663665734925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302048841624442443823283 9453073262436663665734925)
                ·
                  refine ⟨3544902473413748874650597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9453073262436663665734925 3544902473413748874650597)
                  ·
                    refine ⟨664669213765077913996987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544902473413748874650597 664669213765077913996987)
                    ·
                      rfl

theorem cell23_3883316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3883316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883316 prefixEnd_3883316 := by exact prefixLift 3883316
  have htrace : WordTrace (prefixWord ++ tailWord_3883316) baseStart_3883316 baseEnd_3883316 := by
    simpa [prefixWord, tailWord_3883316, baseEnd_3883316] using wordTrace_append hprefix tailTrace_3883316
  have hstable : (prefixWord ++ tailWord_3883316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883316).length < 2 ^ (prefixWord ++ tailWord_3883316).sum := by decide
  have hdescent : baseEnd_3883316 < baseStart_3883316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883373 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3883373 : Nat := 118140960795 + 3883373 * 2 ^ 59
def prefixEnd_3883373 : Nat := 4983230072969 + 3 ^ 40 * 3883373 * 2
def baseEnd_3883373 : Nat := 1994036909692540018978199

theorem tailTrace_3883373 : CollatzResearch.WordTrace tailWord_3883373 prefixEnd_3883373 1994036909692540018978199 := by
  unfold tailWord_3883373
  simp only [CollatzResearch.WordTrace]
  refine ⟨141638249360210323151286773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94425499573473548767524515 141638249360210323151286773)
  ·
    refine ⟨13278585877519717795433135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141638249360210323151286773 13278585877519717795433135)
    ·
      refine ⟨19917878816279576693149703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13278585877519717795433135 19917878816279576693149703)
      ·
        refine ⟨29876818224419365039724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19917878816279576693149703 29876818224419365039724555)
        ·
          refine ⟨44815227336629047559586833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29876818224419365039724555 44815227336629047559586833)
          ·
            refine ⟨33611420502471785669690125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44815227336629047559586833 33611420502471785669690125)
            ·
              refine ⟨12604282688426919626133797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33611420502471785669690125 12604282688426919626133797)
              ·
                refine ⟨2363303004080047429900087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12604282688426919626133797 2363303004080047429900087)
                ·
                  refine ⟨3544954506120071144850131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363303004080047429900087 3544954506120071144850131)
                  ·
                    refine ⟨5317431759180106717275197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3544954506120071144850131 5317431759180106717275197)
                    ·
                      refine ⟨1994036909692540018978199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317431759180106717275197 1994036909692540018978199)
                      ·
                        rfl

theorem cell23_3883373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3883373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883373 prefixEnd_3883373 := by exact prefixLift 3883373
  have htrace : WordTrace (prefixWord ++ tailWord_3883373) baseStart_3883373 baseEnd_3883373 := by
    simpa [prefixWord, tailWord_3883373, baseEnd_3883373] using wordTrace_append hprefix tailTrace_3883373
  have hstable : (prefixWord ++ tailWord_3883373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883373).length < 2 ^ (prefixWord ++ tailWord_3883373).sum := by decide
  have hdescent : baseEnd_3883373 < baseStart_3883373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883389 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3883389 : Nat := 118140960795 + 3883389 * 2 ^ 59
def prefixEnd_3883389 : Nat := 4983230072969 + 3 ^ 40 * 3883389 * 2
def baseEnd_3883389 : Nat := 664681708461003985459375

theorem tailTrace_3883389 : CollatzResearch.WordTrace tailWord_3883389 prefixEnd_3883389 664681708461003985459375 := by
  unfold tailWord_3883389
  simp only [CollatzResearch.WordTrace]
  refine ⟨141638832928152357883869221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94425888618768238589246147 141638832928152357883869221)
  ·
    refine ⟨26557281174028567103225479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141638832928152357883869221 26557281174028567103225479)
    ·
      refine ⟨39835921761042850654838219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26557281174028567103225479 39835921761042850654838219)
      ·
        refine ⟨59753882641564275982257329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39835921761042850654838219 59753882641564275982257329)
        ·
          refine ⟨44815411981173206986692997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59753882641564275982257329 44815411981173206986692997)
          ·
            refine ⟨8402889746469976310004937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44815411981173206986692997 8402889746469976310004937)
            ·
              refine ⟨6302167309852482232503703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8402889746469976310004937 6302167309852482232503703)
              ·
                refine ⟨9453250964778723348755555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302167309852482232503703 9453250964778723348755555)
                ·
                  refine ⟨14179876447168085023133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9453250964778723348755555 14179876447168085023133333)
                  ·
                    refine ⟨664681708461003985459375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14179876447168085023133333 664681708461003985459375)
                    ·
                      rfl

theorem cell23_3883389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3883389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883389 prefixEnd_3883389 := by exact prefixLift 3883389
  have htrace : WordTrace (prefixWord ++ tailWord_3883389) baseStart_3883389 baseEnd_3883389 := by
    simpa [prefixWord, tailWord_3883389, baseEnd_3883389] using wordTrace_append hprefix tailTrace_3883389
  have hstable : (prefixWord ++ tailWord_3883389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883389).length < 2 ^ (prefixWord ++ tailWord_3883389).sum := by decide
  have hdescent : baseEnd_3883389 < baseStart_3883389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883399 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3883399 : Nat := 118140960795 + 3883399 * 2 ^ 59
def prefixEnd_3883399 : Nat := 4983230072969 + 3 ^ 40 * 3883399 * 2
def baseEnd_3883399 : Nat := 1994050260189556917253079

theorem tailTrace_3883399 : CollatzResearch.WordTrace tailWord_3883399 prefixEnd_3883399 1994050260189556917253079 := by
  unfold tailWord_3883399
  simp only [CollatzResearch.WordTrace]
  refine ⟨141639197658116129591733251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94426131772077419727822167 141639197658116129591733251)
  ·
    refine ⟨212458796487174194387599877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141639197658116129591733251 212458796487174194387599877)
    ·
      refine ⟨39836024341345161447674977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212458796487174194387599877 39836024341345161447674977)
      ·
        refine ⟨29877018256008871085756233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39836024341345161447674977 29877018256008871085756233)
        ·
          refine ⟨22407763692006653314317175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29877018256008871085756233 22407763692006653314317175)
          ·
            refine ⟨33611645538009979971475763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407763692006653314317175 33611645538009979971475763)
            ·
              refine ⟨50417468307014969957213645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33611645538009979971475763 50417468307014969957213645)
              ·
                refine ⟨18906550615130613733955117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50417468307014969957213645 18906550615130613733955117)
                ·
                  refine ⟨7089956480673980150233169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18906550615130613733955117 7089956480673980150233169)
                  ·
                    refine ⟨5317467360505485112674877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089956480673980150233169 5317467360505485112674877)
                    ·
                      refine ⟨1994050260189556917253079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317467360505485112674877 1994050260189556917253079)
                      ·
                        rfl

theorem cell23_3883399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3883399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883399 prefixEnd_3883399 := by exact prefixLift 3883399
  have htrace : WordTrace (prefixWord ++ tailWord_3883399) baseStart_3883399 baseEnd_3883399 := by
    simpa [prefixWord, tailWord_3883399, baseEnd_3883399] using wordTrace_append hprefix tailTrace_3883399
  have hstable : (prefixWord ++ tailWord_3883399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883399).length < 2 ^ (prefixWord ++ tailWord_3883399).sum := by decide
  have hdescent : baseEnd_3883399 < baseStart_3883399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883489 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3883489 : Nat := 118140960795 + 3883489 * 2 ^ 59
def prefixEnd_3883489 : Nat := 4983230072969 + 3 ^ 40 * 3883489 * 2
def baseEnd_3883489 : Nat := 1994096473448461565127665

theorem tailTrace_3883489 : CollatzResearch.WordTrace tailWord_3883489 prefixEnd_3883489 1994096473448461565127665 := by
  unfold tailWord_3883489
  simp only [CollatzResearch.WordTrace]
  refine ⟨141642480227790074962509521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94428320151860049975006347 141642480227790074962509521)
  ·
    refine ⟨106231860170842556221882141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141642480227790074962509521 106231860170842556221882141)
    ·
      refine ⟨39836947564065958583205803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106231860170842556221882141 39836947564065958583205803)
      ·
        refine ⟨59755421346098937874808705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39836947564065958583205803 59755421346098937874808705)
        ·
          refine ⟨44816566009574203406106529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59755421346098937874808705 44816566009574203406106529)
          ·
            refine ⟨33612424507180652554579897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44816566009574203406106529 33612424507180652554579897)
            ·
              refine ⟨25209318380385489415934923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33612424507180652554579897 25209318380385489415934923)
              ·
                refine ⟨37813977570578234123902385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25209318380385489415934923 37813977570578234123902385)
                ·
                  refine ⟨28360483177933675592926789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37813977570578234123902385 28360483177933675592926789)
                  ·
                    refine ⟨5317590595862564173673773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28360483177933675592926789 5317590595862564173673773)
                    ·
                      refine ⟨1994096473448461565127665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317590595862564173673773 1994096473448461565127665)
                      ·
                        rfl

theorem cell23_3883489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3883489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883489 prefixEnd_3883489 := by exact prefixLift 3883489
  have htrace : WordTrace (prefixWord ++ tailWord_3883489) baseStart_3883489 baseEnd_3883489 := by
    simpa [prefixWord, tailWord_3883489, baseEnd_3883489] using wordTrace_append hprefix tailTrace_3883489
  have hstable : (prefixWord ++ tailWord_3883489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883489).length < 2 ^ (prefixWord ++ tailWord_3883489).sum := by decide
  have hdescent : baseEnd_3883489 < baseStart_3883489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883539 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 2, 5]
def baseStart_3883539 : Nat := 118140960795 + 3883539 * 2 ^ 59
def prefixEnd_3883539 : Nat := 4983230072969 + 3 ^ 40 * 3883539 * 2
def baseEnd_3883539 : Nat := 664707382493728789834145

theorem tailTrace_3883539 : CollatzResearch.WordTrace tailWord_3883539 prefixEnd_3883539 664707382493728789834145 := by
  unfold tailWord_3883539
  simp only [CollatzResearch.WordTrace]
  refine ⟨141644303877608933501829671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94429535918405955667886447 141644303877608933501829671)
  ·
    refine ⟨212466455816413400252744507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141644303877608933501829671 212466455816413400252744507)
    ·
      refine ⟨318699683724620100379116761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212466455816413400252744507 318699683724620100379116761)
      ·
        refine ⟨239024762793465075284337571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318699683724620100379116761 239024762793465075284337571)
        ·
          refine ⟨358537144190197612926506357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239024762793465075284337571 358537144190197612926506357)
          ·
            refine ⟨33612857267831026211859971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358537144190197612926506357 33612857267831026211859971)
            ·
              refine ⟨50419285901746539317789957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33612857267831026211859971 50419285901746539317789957)
              ·
                refine ⟨9453616106577476122085617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50419285901746539317789957 9453616106577476122085617)
                ·
                  refine ⟨7090212079933107091564213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453616106577476122085617 7090212079933107091564213)
                  ·
                    refine ⟨664707382493728789834145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7090212079933107091564213 664707382493728789834145)
                    ·
                      rfl

theorem cell23_3883539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 5].length) (baseStart_3883539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883539 prefixEnd_3883539 := by exact prefixLift 3883539
  have htrace : WordTrace (prefixWord ++ tailWord_3883539) baseStart_3883539 baseEnd_3883539 := by
    simpa [prefixWord, tailWord_3883539, baseEnd_3883539] using wordTrace_append hprefix tailTrace_3883539
  have hstable : (prefixWord ++ tailWord_3883539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883539).length < 2 ^ (prefixWord ++ tailWord_3883539).sum := by decide
  have hdescent : baseEnd_3883539 < baseStart_3883539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883546 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_3883546 : Nat := 118140960795 + 3883546 * 2 ^ 59
def prefixEnd_3883546 : Nat := 4983230072969 + 3 ^ 40 * 3883546 * 2
def baseEnd_3883546 : Nat := 1994125741845767842114903

theorem tailTrace_3883546 : CollatzResearch.WordTrace tailWord_3883546 prefixEnd_3883546 1994125741845767842114903 := by
  unfold tailWord_3883546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411139797145893424333623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94429706125722382464889661 35411139797145893424333623)
  ·
    refine ⟨53116709695718840136500435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35411139797145893424333623 53116709695718840136500435)
    ·
      refine ⟨79675064543578260204750653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53116709695718840136500435 79675064543578260204750653)
      ·
        refine ⟨29878149203841847576781495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79675064543578260204750653 29878149203841847576781495)
        ·
          refine ⟨44817223805762771365172243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29878149203841847576781495 44817223805762771365172243)
          ·
            refine ⟨67225835708644157047758365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44817223805762771365172243 67225835708644157047758365)
            ·
              refine ⟨25209688390741558892909387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67225835708644157047758365 25209688390741558892909387)
              ·
                refine ⟨37814532586112338339364081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25209688390741558892909387 37814532586112338339364081)
                ·
                  refine ⟨28360899439584253754523061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37814532586112338339364081 28360899439584253754523061)
                  ·
                    refine ⟨2658834322461023789486537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28360899439584253754523061 2658834322461023789486537)
                    ·
                      refine ⟨1994125741845767842114903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658834322461023789486537 1994125741845767842114903)
                      ·
                        rfl

theorem cell23_3883546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_3883546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883546 prefixEnd_3883546 := by exact prefixLift 3883546
  have htrace : WordTrace (prefixWord ++ tailWord_3883546) baseStart_3883546 baseEnd_3883546 := by
    simpa [prefixWord, tailWord_3883546, baseEnd_3883546] using wordTrace_append hprefix tailTrace_3883546
  have hstable : (prefixWord ++ tailWord_3883546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883546).length < 2 ^ (prefixWord ++ tailWord_3883546).sum := by decide
  have hdescent : baseEnd_3883546 < baseStart_3883546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883576 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_3883576 : Nat := 118140960795 + 3883576 * 2 ^ 59
def prefixEnd_3883576 : Nat := 4983230072969 + 3 ^ 40 * 3883576 * 2
def baseEnd_3883576 : Nat := 1994141146265402724739765

theorem tailTrace_3883576 : CollatzResearch.WordTrace tailWord_3883576 prefixEnd_3883576 1994141146265402724739765 := by
  unfold tailWord_3883576
  simp only [CollatzResearch.WordTrace]
  refine ⟨70822826689237444410463291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94430435585649925880617721 70822826689237444410463291)
  ·
    refine ⟨106234240033856166615694937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70822826689237444410463291 106234240033856166615694937)
    ·
      refine ⟨79675680025392124961771203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106234240033856166615694937 79675680025392124961771203)
      ·
        refine ⟨119513520038088187442656805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79675680025392124961771203 119513520038088187442656805)
        ·
          refine ⟨22408785007141535145498151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119513520038088187442656805 22408785007141535145498151)
          ·
            refine ⟨33613177510712302718247227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22408785007141535145498151 33613177510712302718247227)
            ·
              refine ⟨50419766266068454077370841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613177510712302718247227 50419766266068454077370841)
              ·
                refine ⟨37814824699551340558028131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50419766266068454077370841 37814824699551340558028131)
                ·
                  refine ⟨56722237049327010837042197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37814824699551340558028131 56722237049327010837042197)
                  ·
                    refine ⟨2658854861687203632986353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56722237049327010837042197 2658854861687203632986353)
                    ·
                      refine ⟨1994141146265402724739765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658854861687203632986353 1994141146265402724739765)
                      ·
                        rfl

theorem cell23_3883576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_3883576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883576 prefixEnd_3883576 := by exact prefixLift 3883576
  have htrace : WordTrace (prefixWord ++ tailWord_3883576) baseStart_3883576 baseEnd_3883576 := by
    simpa [prefixWord, tailWord_3883576, baseEnd_3883576] using wordTrace_append hprefix tailTrace_3883576
  have hstable : (prefixWord ++ tailWord_3883576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883576).length < 2 ^ (prefixWord ++ tailWord_3883576).sum := by decide
  have hdescent : baseEnd_3883576 < baseStart_3883576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883588 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3883588 : Nat := 118140960795 + 3883588 * 2 ^ 59
def prefixEnd_3883588 : Nat := 4983230072969 + 3 ^ 40 * 3883588 * 2
def baseEnd_3883588 : Nat := 1994147308033256677789711

theorem tailTrace_3883588 : CollatzResearch.WordTrace tailWord_3883588 prefixEnd_3883588 1994147308033256677789711 := by
  unfold tailWord_3883588
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823045527215707435181709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94430727369620943246908945 70823045527215707435181709)
  ·
    refine ⟨26558642072705890288193141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70823045527215707435181709 26558642072705890288193141)
    ·
      refine ⟨2489872694316177214518107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26558642072705890288193141 2489872694316177214518107)
      ·
        refine ⟨3734809041474265821777161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489872694316177214518107 3734809041474265821777161)
        ·
          refine ⟨2801106781105699366332871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3734809041474265821777161 2801106781105699366332871)
          ·
            refine ⟨4201660171658549049499307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801106781105699366332871 4201660171658549049499307)
            ·
              refine ⟨6302490257487823574248961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201660171658549049499307 6302490257487823574248961)
              ·
                refine ⟨4726867693115867680686721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302490257487823574248961 4726867693115867680686721)
                ·
                  refine ⟨3545150769836900760515041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726867693115867680686721 3545150769836900760515041)
                  ·
                    refine ⟨2658863077377675570386281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545150769836900760515041 2658863077377675570386281)
                    ·
                      refine ⟨1994147308033256677789711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658863077377675570386281 1994147308033256677789711)
                      ·
                        rfl

theorem cell23_3883588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3883588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883588 prefixEnd_3883588 := by exact prefixLift 3883588
  have htrace : WordTrace (prefixWord ++ tailWord_3883588) baseStart_3883588 baseEnd_3883588 := by
    simpa [prefixWord, tailWord_3883588, baseEnd_3883588] using wordTrace_append hprefix tailTrace_3883588
  have hstable : (prefixWord ++ tailWord_3883588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883588).length < 2 ^ (prefixWord ++ tailWord_3883588).sum := by decide
  have hdescent : baseEnd_3883588 < baseStart_3883588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883589 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3883589 : Nat := 118140960795 + 3883589 * 2 ^ 59
def prefixEnd_3883589 : Nat := 4983230072969 + 3 ^ 40 * 3883589 * 2
def baseEnd_3883589 : Nat := 1994147821513911173877205

theorem tailTrace_3883589 : CollatzResearch.WordTrace tailWord_3883589 prefixEnd_3883589 1994147821513911173877205 := by
  unfold tailWord_3883589
  simp only [CollatzResearch.WordTrace]
  refine ⟨141646127527427792041149821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94430751684951861360766547 141646127527427792041149821)
  ·
    refine ⟨53117297822785422015431183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141646127527427792041149821 53117297822785422015431183)
    ·
      refine ⟨79675946734178133023146775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53117297822785422015431183 79675946734178133023146775)
      ·
        refine ⟨119513920101267199534720163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79675946734178133023146775 119513920101267199534720163)
        ·
          refine ⟨179270880151900799302080245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119513920101267199534720163 179270880151900799302080245)
          ·
            refine ⟨16806645014240699934570023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179270880151900799302080245 16806645014240699934570023)
            ·
              refine ⟨25209967521361049901855035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16806645014240699934570023 25209967521361049901855035)
              ·
                refine ⟨37814951282041574852782553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25209967521361049901855035 37814951282041574852782553)
                ·
                  refine ⟨28361213461531181139586915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37814951282041574852782553 28361213461531181139586915)
                  ·
                    refine ⟨42541820192296771709380373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28361213461531181139586915 42541820192296771709380373)
                    ·
                      refine ⟨1994147821513911173877205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42541820192296771709380373 1994147821513911173877205)
                      ·
                        rfl

theorem cell23_3883589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3883589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883589 prefixEnd_3883589 := by exact prefixLift 3883589
  have htrace : WordTrace (prefixWord ++ tailWord_3883589) baseStart_3883589 baseEnd_3883589 := by
    simpa [prefixWord, tailWord_3883589, baseEnd_3883589] using wordTrace_append hprefix tailTrace_3883589
  have hstable : (prefixWord ++ tailWord_3883589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883589).length < 2 ^ (prefixWord ++ tailWord_3883589).sum := by decide
  have hdescent : baseEnd_3883589 < baseStart_3883589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883596 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3883596 : Nat := 118140960795 + 3883596 * 2 ^ 59
def prefixEnd_3883596 : Nat := 4983230072969 + 3 ^ 40 * 3883596 * 2
def baseEnd_3883596 : Nat := 1994151415878492646489673

theorem tailTrace_3883596 : CollatzResearch.WordTrace tailWord_3883596 prefixEnd_3883596 1994151415878492646489673 := by
  unfold tailWord_3883596
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823191419201216118327321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94430921892268288157769761 70823191419201216118327321)
  ·
    refine ⟨53117393564400912088745491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70823191419201216118327321 53117393564400912088745491)
    ·
      refine ⟨79676090346601368133118237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53117393564400912088745491 79676090346601368133118237)
      ·
        refine ⟨29878533879975513049919339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79676090346601368133118237 29878533879975513049919339)
        ·
          refine ⟨44817800819963269574879009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29878533879975513049919339 44817800819963269574879009)
          ·
            refine ⟨33613350614972452181159257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44817800819963269574879009 33613350614972452181159257)
            ·
              refine ⟨25210012961229339135869443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33613350614972452181159257 25210012961229339135869443)
              ·
                refine ⟨37815019441844008703804165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210012961229339135869443 37815019441844008703804165)
                ·
                  refine ⟨7090316145345751631963281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37815019441844008703804165 7090316145345751631963281)
                  ·
                    refine ⟨5317737109009313723972461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7090316145345751631963281 5317737109009313723972461)
                    ·
                      refine ⟨1994151415878492646489673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317737109009313723972461 1994151415878492646489673)
                      ·
                        rfl

theorem cell23_3883596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3883596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883596 prefixEnd_3883596 := by exact prefixLift 3883596
  have htrace : WordTrace (prefixWord ++ tailWord_3883596) baseStart_3883596 baseEnd_3883596 := by
    simpa [prefixWord, tailWord_3883596, baseEnd_3883596] using wordTrace_append hprefix tailTrace_3883596
  have hstable : (prefixWord ++ tailWord_3883596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883596).length < 2 ^ (prefixWord ++ tailWord_3883596).sum := by decide
  have hdescent : baseEnd_3883596 < baseStart_3883596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883619 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3883619 : Nat := 118140960795 + 3883619 * 2 ^ 59
def prefixEnd_3883619 : Nat := 4983230072969 + 3 ^ 40 * 3883619 * 2
def baseEnd_3883619 : Nat := 1994163225933546056502067

theorem tailTrace_3883619 : CollatzResearch.WordTrace tailWord_3883619 prefixEnd_3883619 1994163225933546056502067 := by
  unfold tailWord_3883619
  simp only [CollatzResearch.WordTrace]
  refine ⟨141647221717319107164741911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94431481144879404776494607 141647221717319107164741911)
  ·
    refine ⟨212470832575978660747112867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141647221717319107164741911 212470832575978660747112867)
    ·
      refine ⟨318706248863967991120669301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212470832575978660747112867 318706248863967991120669301)
      ·
        refine ⟨29878710830996999167562747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318706248863967991120669301 29878710830996999167562747)
        ·
          refine ⟨44818066246495498751344121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29878710830996999167562747 44818066246495498751344121)
          ·
            refine ⟨33613549684871624063508091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44818066246495498751344121 33613549684871624063508091)
            ·
              refine ⟨50420324527307436095262137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613549684871624063508091 50420324527307436095262137)
              ·
                refine ⟨37815243395480577071446603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50420324527307436095262137 37815243395480577071446603)
                ·
                  refine ⟨56722865093220865607169905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37815243395480577071446603 56722865093220865607169905)
                  ·
                    refine ⟨42542148819915649205377429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56722865093220865607169905 42542148819915649205377429)
                    ·
                      refine ⟨1994163225933546056502067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42542148819915649205377429 1994163225933546056502067)
                      ·
                        rfl

theorem cell23_3883619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3883619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883619 prefixEnd_3883619 := by exact prefixLift 3883619
  have htrace : WordTrace (prefixWord ++ tailWord_3883619) baseStart_3883619 baseEnd_3883619 := by
    simpa [prefixWord, tailWord_3883619, baseEnd_3883619] using wordTrace_append hprefix tailTrace_3883619
  have hstable : (prefixWord ++ tailWord_3883619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883619).length < 2 ^ (prefixWord ++ tailWord_3883619).sum := by decide
  have hdescent : baseEnd_3883619 < baseStart_3883619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883626 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3883626 : Nat := 118140960795 + 3883626 * 2 ^ 59
def prefixEnd_3883626 : Nat := 4983230072969 + 3 ^ 40 * 3883626 * 2
def baseEnd_3883626 : Nat := 1994166820298127529114535

theorem tailTrace_3883626 : CollatzResearch.WordTrace tailWord_3883626 prefixEnd_3883626 1994166820298127529114535 := by
  unfold tailWord_3883626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411869257073436840061683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94431651352195831573497821 35411869257073436840061683)
  ·
    refine ⟨53117803885610155260092525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35411869257073436840061683 53117803885610155260092525)
    ·
      refine ⟨19919176457103808222534697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53117803885610155260092525 19919176457103808222534697)
      ·
        refine ⟨14939382342827856166901023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19919176457103808222534697 14939382342827856166901023)
        ·
          refine ⟨22409073514241784250351535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939382342827856166901023 22409073514241784250351535)
          ·
            refine ⟨33613610271362676375527303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22409073514241784250351535 33613610271362676375527303)
            ·
              refine ⟨50420415407044014563290955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613610271362676375527303 50420415407044014563290955)
              ·
                refine ⟨75630623110566021844936433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50420415407044014563290955 75630623110566021844936433)
                ·
                  refine ⟨56722967332924516383702325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75630623110566021844936433 56722967332924516383702325)
                  ·
                    refine ⟨5317778187461673410972093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56722967332924516383702325 5317778187461673410972093)
                    ·
                      refine ⟨1994166820298127529114535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5317778187461673410972093 1994166820298127529114535)
                      ·
                        rfl

theorem cell23_3883626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3883626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883626 prefixEnd_3883626 := by exact prefixLift 3883626
  have htrace : WordTrace (prefixWord ++ tailWord_3883626) baseStart_3883626 baseEnd_3883626 := by
    simpa [prefixWord, tailWord_3883626, baseEnd_3883626] using wordTrace_append hprefix tailTrace_3883626
  have hstable : (prefixWord ++ tailWord_3883626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883626).length < 2 ^ (prefixWord ++ tailWord_3883626).sum := by decide
  have hdescent : baseEnd_3883626 < baseStart_3883626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883653 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_3883653 : Nat := 118140960795 + 3883653 * 2 ^ 59
def prefixEnd_3883653 : Nat := 4983230072969 + 3 ^ 40 * 3883653 * 2
def baseEnd_3883653 : Nat := 1994180684275798923476911

theorem tailTrace_3883653 : CollatzResearch.WordTrace tailWord_3883653 prefixEnd_3883653 1994180684275798923476911 := by
  unfold tailWord_3883653
  simp only [CollatzResearch.WordTrace]
  refine ⟨141648461799195930971479613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94432307866130620647653075 141648461799195930971479613)
  ·
    refine ⟨53118173174698474114304855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141648461799195930971479613 53118173174698474114304855)
    ·
      refine ⟨79677259762047711171457283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53118173174698474114304855 79677259762047711171457283)
      ·
        refine ⟨119515889643071566757185925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79677259762047711171457283 119515889643071566757185925)
        ·
          refine ⟨22409229308075918766972361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119515889643071566757185925 22409229308075918766972361)
          ·
            refine ⟨16806921981056939075229271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22409229308075918766972361 16806921981056939075229271)
            ·
              refine ⟨25210382971585408612843907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16806921981056939075229271 25210382971585408612843907)
              ·
                refine ⟨37815574457378112919265861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210382971585408612843907 37815574457378112919265861)
                ·
                  refine ⟨7090420210758396172362349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37815574457378112919265861 7090420210758396172362349)
                  ·
                    refine ⟨2658907579034398564635881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7090420210758396172362349 2658907579034398564635881)
                    ·
                      refine ⟨1994180684275798923476911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658907579034398564635881 1994180684275798923476911)
                      ·
                        rfl

theorem cell23_3883653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_3883653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883653 prefixEnd_3883653 := by exact prefixLift 3883653
  have htrace : WordTrace (prefixWord ++ tailWord_3883653) baseStart_3883653 baseEnd_3883653 := by
    simpa [prefixWord, tailWord_3883653, baseEnd_3883653] using wordTrace_append hprefix tailTrace_3883653
  have hstable : (prefixWord ++ tailWord_3883653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883653).length < 2 ^ (prefixWord ++ tailWord_3883653).sum := by decide
  have hdescent : baseEnd_3883653 < baseStart_3883653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883659 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 6]
def baseStart_3883659 : Nat := 118140960795 + 3883659 * 2 ^ 59
def prefixEnd_3883659 : Nat := 4983230072969 + 3 ^ 40 * 3883659 * 2
def baseEnd_3883659 : Nat := 664727921719908633333961

theorem tailTrace_3883659 : CollatzResearch.WordTrace tailWord_3883659 prefixEnd_3883659 664727921719908633333961 := by
  unfold tailWord_3883659
  simp only [CollatzResearch.WordTrace]
  refine ⟨141648680637174193996198031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94432453758116129330798687 141648680637174193996198031)
  ·
    refine ⟨212473020955761290994297047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141648680637174193996198031 212473020955761290994297047)
    ·
      refine ⟨318709531433641936491445571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212473020955761290994297047 318709531433641936491445571)
      ·
        refine ⟨478064297150462904737168357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318709531433641936491445571 478064297150462904737168357)
        ·
          refine ⟨89637055715711794638219067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478064297150462904737168357 89637055715711794638219067)
          ·
            refine ⟨134455583573567691957328601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89637055715711794638219067 134455583573567691957328601)
            ·
              refine ⟨100841687680175768967996451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134455583573567691957328601 100841687680175768967996451)
              ·
                refine ⟨151262531520263653451994677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100841687680175768967996451 151262531520263653451994677)
                ·
                  refine ⟨14180862330024717511124501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151262531520263653451994677 14180862330024717511124501)
                  ·
                    refine ⟨664727921719908633333961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14180862330024717511124501 664727921719908633333961)
                    ·
                      rfl

theorem cell23_3883659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_3883659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883659 prefixEnd_3883659 := by exact prefixLift 3883659
  have htrace : WordTrace (prefixWord ++ tailWord_3883659) baseStart_3883659 baseEnd_3883659 := by
    simpa [prefixWord, tailWord_3883659, baseEnd_3883659] using wordTrace_append hprefix tailTrace_3883659
  have hstable : (prefixWord ++ tailWord_3883659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883659).length < 2 ^ (prefixWord ++ tailWord_3883659).sum := by decide
  have hdescent : baseEnd_3883659 < baseStart_3883659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883680 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_3883680 : Nat := 118140960795 + 3883680 * 2 ^ 59
def prefixEnd_3883680 : Nat := 4983230072969 + 3 ^ 40 * 3883680 * 2
def baseEnd_3883680 : Nat := 664731516084490105946429

theorem tailTrace_3883680 : CollatzResearch.WordTrace tailWord_3883680 prefixEnd_3883680 664731516084490105946429 := by
  unfold tailWord_3883680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70824723285049057291356247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94432964380065409721808329 70824723285049057291356247)
  ·
    refine ⟨106237084927573585937034371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70824723285049057291356247 106237084927573585937034371)
    ·
      refine ⟨159355627391360378905551557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106237084927573585937034371 159355627391360378905551557)
      ·
        refine ⟨29879180135880071044790917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159355627391360378905551557 29879180135880071044790917)
        ·
          refine ⟨5602346275477513320898297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29879180135880071044790917 5602346275477513320898297)
          ·
            refine ⟨4201759706608134990673723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602346275477513320898297 4201759706608134990673723)
            ·
              refine ⟨6302639559912202486010585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201759706608134990673723 6302639559912202486010585)
              ·
                refine ⟨4726979669934151864507939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302639559912202486010585 4726979669934151864507939)
                ·
                  refine ⟨7090469504901227796761909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726979669934151864507939 7090469504901227796761909)
                  ·
                    refine ⟨664731516084490105946429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7090469504901227796761909 664731516084490105946429)
                    ·
                      rfl

theorem cell23_3883680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_3883680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883680 prefixEnd_3883680 := by exact prefixLift 3883680
  have htrace : WordTrace (prefixWord ++ tailWord_3883680) baseStart_3883680 baseEnd_3883680 := by
    simpa [prefixWord, tailWord_3883680, baseEnd_3883680] using wordTrace_append hprefix tailTrace_3883680
  have hstable : (prefixWord ++ tailWord_3883680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883680).length < 2 ^ (prefixWord ++ tailWord_3883680).sum := by decide
  have hdescent : baseEnd_3883680 < baseStart_3883680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883693 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3883693 : Nat := 118140960795 + 3883693 * 2 ^ 59
def prefixEnd_3883693 : Nat := 4983230072969 + 3 ^ 40 * 3883693 * 2
def baseEnd_3883693 : Nat := 664733741167326255658909

theorem tailTrace_3883693 : CollatzResearch.WordTrace tailWord_3883693 prefixEnd_3883693 664733741167326255658909 := by
  unfold tailWord_3883693
  simp only [CollatzResearch.WordTrace]
  refine ⟨141649920719051017802935733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94433280479367345201957155 141649920719051017802935733)
  ·
    refine ⟨13279680067411032919025225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141649920719051017802935733 13279680067411032919025225)
    ·
      refine ⟨9959760050558274689268919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13279680067411032919025225 9959760050558274689268919)
      ·
        refine ⟨14939640075837412033903379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959760050558274689268919 14939640075837412033903379)
        ·
          refine ⟨22409460113756118050855069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939640075837412033903379 22409460113756118050855069)
          ·
            refine ⟨8403547542658544269070651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22409460113756118050855069 8403547542658544269070651)
            ·
              refine ⟨12605321313987816403605977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403547542658544269070651 12605321313987816403605977)
              ·
                refine ⟨9453990985490862302704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12605321313987816403605977 9453990985490862302704483)
                ·
                  refine ⟨14180986478236293454056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9453990985490862302704483 14180986478236293454056725)
                  ·
                    refine ⟨664733741167326255658909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14180986478236293454056725 664733741167326255658909)
                    ·
                      rfl

theorem cell23_3883693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3883693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883693 prefixEnd_3883693 := by exact prefixLift 3883693
  have htrace : WordTrace (prefixWord ++ tailWord_3883693) baseStart_3883693 baseEnd_3883693 := by
    simpa [prefixWord, tailWord_3883693, baseEnd_3883693] using wordTrace_append hprefix tailTrace_3883693
  have hstable : (prefixWord ++ tailWord_3883693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883693).length < 2 ^ (prefixWord ++ tailWord_3883693).sum := by decide
  have hdescent : baseEnd_3883693 < baseStart_3883693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883697 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_3883697 : Nat := 118140960795 + 3883697 * 2 ^ 59
def prefixEnd_3883697 : Nat := 4983230072969 + 3 ^ 40 * 3883697 * 2
def baseEnd_3883697 : Nat := 664734425808198917108903

theorem tailTrace_3883697 : CollatzResearch.WordTrace tailWord_3883697 prefixEnd_3883697 664734425808198917108903 := by
  unfold tailWord_3883697
  simp only [CollatzResearch.WordTrace]
  refine ⟨141650066611036526486081345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94433377740691017657387563 141650066611036526486081345)
  ·
    refine ⟨106237549958277394864561009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141650066611036526486081345 106237549958277394864561009)
    ·
      refine ⟨79678162468708046148420757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106237549958277394864561009 79678162468708046148420757)
      ·
        refine ⟨3734913865720689663207223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79678162468708046148420757 3734913865720689663207223)
        ·
          refine ⟨5602370798581034494810835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734913865720689663207223 5602370798581034494810835)
          ·
            refine ⟨8403556197871551742216253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602370798581034494810835 8403556197871551742216253)
            ·
              refine ⟨3151333574201831903331095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8403556197871551742216253 3151333574201831903331095)
              ·
                refine ⟨4727000361302747854996643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151333574201831903331095 4727000361302747854996643)
                ·
                  refine ⟨7090500541954121782494965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727000361302747854996643 7090500541954121782494965)
                  ·
                    refine ⟨664734425808198917108903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7090500541954121782494965 664734425808198917108903)
                    ·
                      rfl

theorem cell23_3883697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_3883697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883697 prefixEnd_3883697 := by exact prefixLift 3883697
  have htrace : WordTrace (prefixWord ++ tailWord_3883697) baseStart_3883697 baseEnd_3883697 := by
    simpa [prefixWord, tailWord_3883697, baseEnd_3883697] using wordTrace_append hprefix tailTrace_3883697
  have hstable : (prefixWord ++ tailWord_3883697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883697).length < 2 ^ (prefixWord ++ tailWord_3883697).sum := by decide
  have hdescent : baseEnd_3883697 < baseStart_3883697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883710 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3883710 : Nat := 118140960795 + 3883710 * 2 ^ 59
def prefixEnd_3883710 : Nat := 4983230072969 + 3 ^ 40 * 3883710 * 2
def baseEnd_3883710 : Nat := 664736650891035066821383

theorem tailTrace_3883710 : CollatzResearch.WordTrace tailWord_3883710 prefixEnd_3883710 664736650891035066821383 := by
  unfold tailWord_3883710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706317594998678713288073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94433693839992953137536389 17706317594998678713288073)
  ·
    refine ⟨13279738196249009034966055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17706317594998678713288073 13279738196249009034966055)
    ·
      refine ⟨19919607294373513552449083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279738196249009034966055 19919607294373513552449083)
      ·
        refine ⟨29879410941560270328673625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919607294373513552449083 29879410941560270328673625)
        ·
          refine ⟨22409558206170202746505219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29879410941560270328673625 22409558206170202746505219)
          ·
            refine ⟨33614337309255304119757829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22409558206170202746505219 33614337309255304119757829)
            ·
              refine ⟨6302688245485369522454593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33614337309255304119757829 6302688245485369522454593)
              ·
                refine ⟨4727016184114027141840945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302688245485369522454593 4727016184114027141840945)
                ·
                  refine ⟨3545262138085520356380709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727016184114027141840945 3545262138085520356380709)
                  ·
                    refine ⟨664736650891035066821383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545262138085520356380709 664736650891035066821383)
                    ·
                      rfl

theorem cell23_3883710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3883710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883710 prefixEnd_3883710 := by exact prefixLift 3883710
  have htrace : WordTrace (prefixWord ++ tailWord_3883710) baseStart_3883710 baseEnd_3883710 := by
    simpa [prefixWord, tailWord_3883710, baseEnd_3883710] using wordTrace_append hprefix tailTrace_3883710
  have hstable : (prefixWord ++ tailWord_3883710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883710).length < 2 ^ (prefixWord ++ tailWord_3883710).sum := by decide
  have hdescent : baseEnd_3883710 < baseStart_3883710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883730 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3883730 : Nat := 118140960795 + 3883730 * 2 ^ 59
def prefixEnd_3883730 : Nat := 4983230072969 + 3 ^ 40 * 3883730 * 2
def baseEnd_3883730 : Nat := 1994220222286195122214057

theorem tailTrace_3883730 : CollatzResearch.WordTrace tailWord_3883730 prefixEnd_3883730 1994220222286195122214057 := by
  unfold tailWord_3883730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412817554979243280508161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94434180146611315414688429 35412817554979243280508161)
  ·
    refine ⟨26559613166234432460381121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35412817554979243280508161 26559613166234432460381121)
    ·
      refine ⟨19919709874675824345285841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26559613166234432460381121 19919709874675824345285841)
      ·
        refine ⟨14939782406006868258964381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19919709874675824345285841 14939782406006868258964381)
        ·
          refine ⟨5602418402252575597111643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14939782406006868258964381 5602418402252575597111643)
          ·
            refine ⟨8403627603378863395667465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602418402252575597111643 8403627603378863395667465)
            ·
              refine ⟨6302720702534147546750599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8403627603378863395667465 6302720702534147546750599)
              ·
                refine ⟨9454081053801221320125899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302720702534147546750599 9454081053801221320125899)
                ·
                  refine ⟨14181121580701831980188849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9454081053801221320125899 14181121580701831980188849)
                  ·
                    refine ⟨10635841185526373985141637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14181121580701831980188849 10635841185526373985141637)
                    ·
                      refine ⟨1994220222286195122214057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10635841185526373985141637 1994220222286195122214057)
                      ·
                        rfl

theorem cell23_3883730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3883730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883730 prefixEnd_3883730 := by exact prefixLift 3883730
  have htrace : WordTrace (prefixWord ++ tailWord_3883730) baseStart_3883730 baseEnd_3883730 := by
    simpa [prefixWord, tailWord_3883730, baseEnd_3883730] using wordTrace_append hprefix tailTrace_3883730
  have hstable : (prefixWord ++ tailWord_3883730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883730).length < 2 ^ (prefixWord ++ tailWord_3883730).sum := by decide
  have hdescent : baseEnd_3883730 < baseStart_3883730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883740 : List Nat := [2, 2, 5, 1, 1, 2, 3, 7]
def baseStart_3883740 : Nat := 118140960795 + 3883740 * 2 ^ 59
def prefixEnd_3883740 : Nat := 4983230072969 + 3 ^ 40 * 3883740 * 2
def baseEnd_3883740 : Nat := 73860198410842225299593

theorem tailTrace_3883740 : CollatzResearch.WordTrace tailWord_3883740 prefixEnd_3883740 73860198410842225299593 := by
  unfold tailWord_3883740
  simp only [CollatzResearch.WordTrace]
  refine ⟨70825817474940372414948337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94434423299920496553264449 70825817474940372414948337)
  ·
    refine ⟨53119363106205279311211253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70825817474940372414948337 53119363106205279311211253)
    ·
      refine ⟨4979940291206744935426055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53119363106205279311211253 4979940291206744935426055)
      ·
        refine ⟨7469910436810117403139083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979940291206744935426055 7469910436810117403139083)
        ·
          refine ⟨11204865655215176104708625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469910436810117403139083 11204865655215176104708625)
          ·
            refine ⟨8403649241411382078531469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11204865655215176104708625 8403649241411382078531469)
            ·
              refine ⟨3151368465529268279449301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8403649241411382078531469 3151368465529268279449301)
              ·
                refine ⟨73860198410842225299593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3151368465529268279449301 73860198410842225299593)
                ·
                  rfl

theorem cell23_3883740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 7].length) (baseStart_3883740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883740 prefixEnd_3883740 := by exact prefixLift 3883740
  have htrace : WordTrace (prefixWord ++ tailWord_3883740) baseStart_3883740 baseEnd_3883740 := by
    simpa [prefixWord, tailWord_3883740, baseEnd_3883740] using wordTrace_append hprefix tailTrace_3883740
  have hstable : (prefixWord ++ tailWord_3883740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883740).length < 2 ^ (prefixWord ++ tailWord_3883740).sum := by decide
  have hdescent : baseEnd_3883740 < baseStart_3883740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883760 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2]
def baseStart_3883760 : Nat := 118140960795 + 3883760 * 2 ^ 59
def prefixEnd_3883760 : Nat := 4983230072969 + 3 ^ 40 * 3883760 * 2
def baseEnd_3883760 : Nat := 1994235626705830004838919

theorem tailTrace_3883760 : CollatzResearch.WordTrace tailWord_3883760 prefixEnd_3883760 1994235626705830004838919 := by
  unfold tailWord_3883760
  simp only [CollatzResearch.WordTrace]
  refine ⟨70826182204904144122812367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94434909606538858830416489 70826182204904144122812367)
  ·
    refine ⟨106239273307356216184218551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70826182204904144122812367 106239273307356216184218551)
    ·
      refine ⟨159358909961034324276327827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106239273307356216184218551 159358909961034324276327827)
      ·
        refine ⟨239038364941551486414491741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159358909961034324276327827 239038364941551486414491741)
        ·
          refine ⟨89639386853081807405434403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239038364941551486414491741 89639386853081807405434403)
          ·
            refine ⟨134459080279622711108151605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89639386853081807405434403 134459080279622711108151605)
            ·
              refine ⟨12605538776214629166389213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134459080279622711108151605 12605538776214629166389213)
              ·
                refine ⟨4727077041080485937395955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12605538776214629166389213 4727077041080485937395955)
                ·
                  refine ⟨7090615561620728906093933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727077041080485937395955 7090615561620728906093933)
                  ·
                    refine ⟨2658980835607773339785225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7090615561620728906093933 2658980835607773339785225)
                    ·
                      refine ⟨1994235626705830004838919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2658980835607773339785225 1994235626705830004838919)
                      ·
                        rfl

theorem cell23_3883760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2].length) (baseStart_3883760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883760 prefixEnd_3883760 := by exact prefixLift 3883760
  have htrace : WordTrace (prefixWord ++ tailWord_3883760) baseStart_3883760 baseEnd_3883760 := by
    simpa [prefixWord, tailWord_3883760, baseEnd_3883760] using wordTrace_append hprefix tailTrace_3883760
  have hstable : (prefixWord ++ tailWord_3883760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883760).length < 2 ^ (prefixWord ++ tailWord_3883760).sum := by decide
  have hdescent : baseEnd_3883760 < baseStart_3883760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883783 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 6]
def baseStart_3883783 : Nat := 118140960795 + 3883783 * 2 ^ 59
def prefixEnd_3883783 : Nat := 4983230072969 + 3 ^ 40 * 3883783 * 2
def baseEnd_3883783 : Nat := 664749145586961138283771

theorem tailTrace_3883783 : CollatzResearch.WordTrace tailWord_3883783 prefixEnd_3883783 664749145586961138283771 := by
  unfold tailWord_3883783
  simp only [CollatzResearch.WordTrace]
  refine ⟨141653203288724963173712003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94435468859149975449141335 141653203288724963173712003)
  ·
    refine ⟨212479804933087444760568005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141653203288724963173712003 212479804933087444760568005)
    ·
      refine ⟨39839963424953895892606501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212479804933087444760568005 39839963424953895892606501)
      ·
        refine ⟨7469993142178855479863719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39839963424953895892606501 7469993142178855479863719)
        ·
          refine ⟨11204989713268283219795579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469993142178855479863719 11204989713268283219795579)
          ·
            refine ⟨16807484569902424829693369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204989713268283219795579 16807484569902424829693369)
            ·
              refine ⟨12605613427426818622270027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16807484569902424829693369 12605613427426818622270027)
              ·
                refine ⟨18908420141140227933405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605613427426818622270027 18908420141140227933405041)
                ·
                  refine ⟨14181315105855170950053781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18908420141140227933405041 14181315105855170950053781)
                  ·
                    refine ⟨664749145586961138283771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14181315105855170950053781 664749145586961138283771)
                    ·
                      rfl

theorem cell23_3883783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_3883783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883783 prefixEnd_3883783 := by exact prefixLift 3883783
  have htrace : WordTrace (prefixWord ++ tailWord_3883783) baseStart_3883783 baseEnd_3883783 := by
    simpa [prefixWord, tailWord_3883783, baseEnd_3883783] using wordTrace_append hprefix tailTrace_3883783
  have hstable : (prefixWord ++ tailWord_3883783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883783).length < 2 ^ (prefixWord ++ tailWord_3883783).sum := by decide
  have hdescent : baseEnd_3883783 < baseStart_3883783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883841 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3883841 : Nat := 118140960795 + 3883841 * 2 ^ 59
def prefixEnd_3883841 : Nat := 4983230072969 + 3 ^ 40 * 3883841 * 2
def baseEnd_3883841 : Nat := 1994277218638844187926047

theorem tailTrace_3883841 : CollatzResearch.WordTrace tailWord_3883841 prefixEnd_3883841 1994277218638844187926047 := by
  unfold tailWord_3883841
  simp only [CollatzResearch.WordTrace]
  refine ⟨141655318722514839079323377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94436879148343226052882251 141655318722514839079323377)
  ·
    refine ⟨106241489041886129309492533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141655318722514839079323377 106241489041886129309492533)
    ·
      refine ⟨9960139597676824622764925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106241489041886129309492533 9960139597676824622764925)
      ·
        refine ⟨3735052349128809233536847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9960139597676824622764925 3735052349128809233536847)
        ·
          refine ⟨5602578523693213850305271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735052349128809233536847 5602578523693213850305271)
          ·
            refine ⟨8403867785539820775457907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602578523693213850305271 8403867785539820775457907)
            ·
              refine ⟨12605801678309731163186861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403867785539820775457907 12605801678309731163186861)
              ·
                refine ⟨4727175629366149186195073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12605801678309731163186861 4727175629366149186195073)
                ·
                  refine ⟨3545381722024611889646305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727175629366149186195073 3545381722024611889646305)
                  ·
                    refine ⟨2659036291518458917234729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545381722024611889646305 2659036291518458917234729)
                    ·
                      refine ⟨1994277218638844187926047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659036291518458917234729 1994277218638844187926047)
                      ·
                        rfl

theorem cell23_3883841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3883841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883841 prefixEnd_3883841 := by exact prefixLift 3883841
  have htrace : WordTrace (prefixWord ++ tailWord_3883841) baseStart_3883841 baseEnd_3883841 := by
    simpa [prefixWord, tailWord_3883841, baseEnd_3883841] using wordTrace_append hprefix tailTrace_3883841
  have hstable : (prefixWord ++ tailWord_3883841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883841).length < 2 ^ (prefixWord ++ tailWord_3883841).sum := by decide
  have hdescent : baseEnd_3883841 < baseStart_3883841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883856 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_3883856 : Nat := 118140960795 + 3883856 * 2 ^ 59
def prefixEnd_3883856 : Nat := 4983230072969 + 3 ^ 40 * 3883856 * 2
def baseEnd_3883856 : Nat := 664761640282887209746159

theorem tailTrace_3883856 : CollatzResearch.WordTrace tailWord_3883856 prefixEnd_3883856 664761640282887209746159 := by
  unfold tailWord_3883856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70827932908730248320559711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94437243878306997760746281 70827932908730248320559711)
  ·
    refine ⟨106241899363095372480839567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70827932908730248320559711 106241899363095372480839567)
    ·
      refine ⟨159362849044643058721259351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106241899363095372480839567 159362849044643058721259351)
      ·
        refine ⟨239044273566964588081889027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159362849044643058721259351 239044273566964588081889027)
        ·
          refine ⟨358566410350446882122833541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239044273566964588081889027 358566410350446882122833541)
          ·
            refine ⟨67231201940708790398031289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358566410350446882122833541 67231201940708790398031289)
            ·
              refine ⟨50423401455531592798523467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67231201940708790398031289 50423401455531592798523467)
              ·
                refine ⟨75635102183297389197785201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50423401455531592798523467 75635102183297389197785201)
                ·
                  refine ⟨56726326637473041898338901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75635102183297389197785201 56726326637473041898338901)
                  ·
                    refine ⟨664761640282887209746159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56726326637473041898338901 664761640282887209746159)
                    ·
                      rfl

theorem cell23_3883856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_3883856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883856 prefixEnd_3883856 := by exact prefixLift 3883856
  have htrace : WordTrace (prefixWord ++ tailWord_3883856) baseStart_3883856 baseEnd_3883856 := by
    simpa [prefixWord, tailWord_3883856, baseEnd_3883856] using wordTrace_append hprefix tailTrace_3883856
  have hstable : (prefixWord ++ tailWord_3883856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883856).length < 2 ^ (prefixWord ++ tailWord_3883856).sum := by decide
  have hdescent : baseEnd_3883856 < baseStart_3883856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883873 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3883873 : Nat := 118140960795 + 3883873 * 2 ^ 59
def prefixEnd_3883873 : Nat := 4983230072969 + 3 ^ 40 * 3883873 * 2
def baseEnd_3883873 : Nat := 664764550006596020908633

theorem tailTrace_3883873 : CollatzResearch.WordTrace tailWord_3883873 prefixEnd_3883873 664764550006596020908633 := by
  unfold tailWord_3883873
  simp only [CollatzResearch.WordTrace]
  refine ⟨141656485858398908544488273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94437657238932605696325515 141656485858398908544488273)
  ·
    refine ⟨106242364393799181408366205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141656485858398908544488273 106242364393799181408366205)
    ·
      refine ⟨39840886647674693028137327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106242364393799181408366205 39840886647674693028137327)
      ·
        refine ⟨59761329971512039542205991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39840886647674693028137327 59761329971512039542205991)
        ·
          refine ⟨89641994957268059313308987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59761329971512039542205991 89641994957268059313308987)
          ·
            refine ⟨134462992435902088969963481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89641994957268059313308987 134462992435902088969963481)
            ·
              refine ⟨100847244326926566727472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134462992435902088969963481 100847244326926566727472611)
              ·
                refine ⟨151270866490389850091208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100847244326926566727472611 151270866490389850091208917)
                ·
                  refine ⟨3545410933368512111512709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 151270866490389850091208917 3545410933368512111512709)
                  ·
                    refine ⟨664764550006596020908633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545410933368512111512709 664764550006596020908633)
                    ·
                      rfl

theorem cell23_3883873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3883873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883873 prefixEnd_3883873 := by exact prefixLift 3883873
  have htrace : WordTrace (prefixWord ++ tailWord_3883873) baseStart_3883873 baseEnd_3883873 := by
    simpa [prefixWord, tailWord_3883873, baseEnd_3883873] using wordTrace_append hprefix tailTrace_3883873
  have hstable : (prefixWord ++ tailWord_3883873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883873).length < 2 ^ (prefixWord ++ tailWord_3883873).sum := by decide
  have hdescent : baseEnd_3883873 < baseStart_3883873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883880 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3883880 : Nat := 118140960795 + 3883880 * 2 ^ 59
def prefixEnd_3883880 : Nat := 4983230072969 + 3 ^ 40 * 3883880 * 2
def baseEnd_3883880 : Nat := 1994297244384369535338367

theorem tailTrace_3883880 : CollatzResearch.WordTrace tailWord_3883880 prefixEnd_3883880 1994297244384369535338367 := by
  unfold tailWord_3883880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70828370584686774369996547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94437827446249032493328729 70828370584686774369996547)
  ·
    refine ⟨106242555877030161554994821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70828370584686774369996547 106242555877030161554994821)
    ·
      refine ⟨19920479226943155291561529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106242555877030161554994821 19920479226943155291561529)
      ·
        refine ⟨14940359420207366468671147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19920479226943155291561529 14940359420207366468671147)
        ·
          refine ⟨22410539130311049703006721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14940359420207366468671147 22410539130311049703006721)
          ·
            refine ⟨16807904347733287277255041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22410539130311049703006721 16807904347733287277255041)
            ·
              refine ⟨12605928260799965457941281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16807904347733287277255041 12605928260799965457941281)
              ·
                refine ⟨9454446195599974093455961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12605928260799965457941281 9454446195599974093455961)
                ·
                  refine ⟨7090834646699980570091971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454446195599974093455961 7090834646699980570091971)
                  ·
                    refine ⟨10636251970049970855137957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090834646699980570091971 10636251970049970855137957)
                    ·
                      refine ⟨1994297244384369535338367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10636251970049970855137957 1994297244384369535338367)
                      ·
                        rfl

theorem cell23_3883880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3883880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883880 prefixEnd_3883880 := by exact prefixLift 3883880
  have htrace : WordTrace (prefixWord ++ tailWord_3883880) baseStart_3883880 baseEnd_3883880 := by
    simpa [prefixWord, tailWord_3883880, baseEnd_3883880] using wordTrace_append hprefix tailTrace_3883880
  have hstable : (prefixWord ++ tailWord_3883880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883880).length < 2 ^ (prefixWord ++ tailWord_3883880).sum := by decide
  have hdescent : baseEnd_3883880 < baseStart_3883880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883903 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 6]
def baseStart_3883903 : Nat := 118140960795 + 3883903 * 2 ^ 59
def prefixEnd_3883903 : Nat := 4983230072969 + 3 ^ 40 * 3883903 * 2
def baseEnd_3883903 : Nat := 221589894937713660594529

theorem tailTrace_3883903 : CollatzResearch.WordTrace tailWord_3883903 prefixEnd_3883903 221589894937713660594529 := by
  unfold tailWord_3883903
  simp only [CollatzResearch.WordTrace]
  refine ⟨141657580048290223668080363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94438386698860149112053575 141657580048290223668080363)
  ·
    refine ⟨212486370072435335502120545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141657580048290223668080363 212486370072435335502120545)
    ·
      refine ⟨159364777554326501626590409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212486370072435335502120545 159364777554326501626590409)
      ·
        refine ⟨119523583165744876219942807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159364777554326501626590409 119523583165744876219942807)
        ·
          refine ⟨179285374748617314329914211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119523583165744876219942807 179285374748617314329914211)
          ·
            refine ⟨268928062122925971494871317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179285374748617314329914211 268928062122925971494871317)
            ·
              refine ⟨12606002912012154913822093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268928062122925971494871317 12606002912012154913822093)
              ·
                refine ⟨4727251092004558092683285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606002912012154913822093 4727251092004558092683285)
                ·
                  refine ⟨221589894937713660594529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4727251092004558092683285 221589894937713660594529)
                  ·
                    rfl

theorem cell23_3883903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 6].length) (baseStart_3883903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883903 prefixEnd_3883903 := by exact prefixLift 3883903
  have htrace : WordTrace (prefixWord ++ tailWord_3883903) baseStart_3883903 baseEnd_3883903 := by
    simpa [prefixWord, tailWord_3883903, baseEnd_3883903] using wordTrace_append hprefix tailTrace_3883903
  have hstable : (prefixWord ++ tailWord_3883903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883903).length < 2 ^ (prefixWord ++ tailWord_3883903).sum := by decide
  have hdescent : baseEnd_3883903 < baseStart_3883903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883924 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3883924 : Nat := 118140960795 + 3883924 * 2 ^ 59
def prefixEnd_3883924 : Nat := 4983230072969 + 3 ^ 40 * 3883924 * 2
def baseEnd_3883924 : Nat := 664773279177722454396055

theorem tailTrace_3883924 : CollatzResearch.WordTrace tailWord_3883924 prefixEnd_3883924 664773279177722454396055 := by
  unfold tailWord_3883924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70829172990607072127297413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94438897320809429503063217 70829172990607072127297413)
  ·
    refine ⟨13280469935738826023868265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70829172990607072127297413 13280469935738826023868265)
    ·
      refine ⟨9960352451804119517901199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13280469935738826023868265 9960352451804119517901199)
      ·
        refine ⟨14940528677706179276851799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960352451804119517901199 14940528677706179276851799)
        ·
          refine ⟨22410793016559268915277699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14940528677706179276851799 22410793016559268915277699)
          ·
            refine ⟨33616189524838903372916549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22410793016559268915277699 33616189524838903372916549)
            ·
              refine ⟨6303035535907294382421853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33616189524838903372916549 6303035535907294382421853)
              ·
                refine ⟨2363638325965235393408195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6303035535907294382421853 2363638325965235393408195)
                ·
                  refine ⟨3545457488947853090112293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363638325965235393408195 3545457488947853090112293)
                  ·
                    refine ⟨664773279177722454396055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545457488947853090112293 664773279177722454396055)
                    ·
                      rfl

theorem cell23_3883924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3883924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883924 prefixEnd_3883924 := by exact prefixLift 3883924
  have htrace : WordTrace (prefixWord ++ tailWord_3883924) baseStart_3883924 baseEnd_3883924 := by
    simpa [prefixWord, tailWord_3883924, baseEnd_3883924] using wordTrace_append hprefix tailTrace_3883924
  have hstable : (prefixWord ++ tailWord_3883924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883924).length < 2 ^ (prefixWord ++ tailWord_3883924).sum := by decide
  have hdescent : baseEnd_3883924 < baseStart_3883924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883937 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 6]
def baseStart_3883937 : Nat := 118140960795 + 3883937 * 2 ^ 59
def prefixEnd_3883937 : Nat := 4983230072969 + 3 ^ 40 * 3883937 * 2
def baseEnd_3883937 : Nat := 221591834753519534702845

theorem tailTrace_3883937 : CollatzResearch.WordTrace tailWord_3883937 prefixEnd_3883937 221591834753519534702845 := by
  unfold tailWord_3883937
  simp only [CollatzResearch.WordTrace]
  refine ⟨141658820130167047474818065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94439213420111364983212043 141658820130167047474818065)
  ·
    refine ⟨106244115097625285606113549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141658820130167047474818065 106244115097625285606113549)
    ·
      refine ⟨39841543161609482102292581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106244115097625285606113549 39841543161609482102292581)
      ·
        refine ⟨7470289342801777894179859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39841543161609482102292581 7470289342801777894179859)
        ·
          refine ⟨11205434014202666841269789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470289342801777894179859 11205434014202666841269789)
          ·
            refine ⟨4202037755326000065476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11205434014202666841269789 4202037755326000065476171)
            ·
              refine ⟨6303056632989000098214257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202037755326000065476171 6303056632989000098214257)
              ·
                refine ⟨4727292474741750073660693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303056632989000098214257 4727292474741750073660693)
                ·
                  refine ⟨221591834753519534702845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4727292474741750073660693 221591834753519534702845)
                  ·
                    rfl

theorem cell23_3883937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_3883937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883937 prefixEnd_3883937 := by exact prefixLift 3883937
  have htrace : WordTrace (prefixWord ++ tailWord_3883937) baseStart_3883937 baseEnd_3883937 := by
    simpa [prefixWord, tailWord_3883937, baseEnd_3883937] using wordTrace_append hprefix tailTrace_3883937
  have hstable : (prefixWord ++ tailWord_3883937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883937).length < 2 ^ (prefixWord ++ tailWord_3883937).sum := by decide
  have hdescent : baseEnd_3883937 < baseStart_3883937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883980 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_3883980 : Nat := 118140960795 + 3883980 * 2 ^ 59
def prefixEnd_3883980 : Nat := 4983230072969 + 3 ^ 40 * 3883980 * 2
def baseEnd_3883980 : Nat := 664782864149939714695969

theorem tailTrace_3883980 : CollatzResearch.WordTrace tailWord_3883980 prefixEnd_3883980 664782864149939714695969 := by
  unfold tailWord_3883980
  simp only [CollatzResearch.WordTrace]
  refine ⟨70830194234505632909316697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94440258979340843879088929 70830194234505632909316697)
  ·
    refine ⟨53122645675879224681987523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70830194234505632909316697 53122645675879224681987523)
    ·
      refine ⟨79683968513818837022981285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122645675879224681987523 79683968513818837022981285)
      ·
        refine ⟨14940744096341031941808991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79683968513818837022981285 14940744096341031941808991)
        ·
          refine ⟨22411116144511547912713487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14940744096341031941808991 22411116144511547912713487)
          ·
            refine ⟨33616674216767321869070231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411116144511547912713487 33616674216767321869070231)
            ·
              refine ⟨50425011325150982803605347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616674216767321869070231 50425011325150982803605347)
              ·
                refine ⟨75637516987726474205408021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50425011325150982803605347 75637516987726474205408021)
                ·
                  refine ⟨3545508608799678478378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75637516987726474205408021 3545508608799678478378501)
                  ·
                    refine ⟨664782864149939714695969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545508608799678478378501 664782864149939714695969)
                    ·
                      rfl

theorem cell23_3883980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_3883980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883980 prefixEnd_3883980 := by exact prefixLift 3883980
  have htrace : WordTrace (prefixWord ++ tailWord_3883980) baseStart_3883980 baseEnd_3883980 := by
    simpa [prefixWord, tailWord_3883980, baseEnd_3883980] using wordTrace_append hprefix tailTrace_3883980
  have hstable : (prefixWord ++ tailWord_3883980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883980).length < 2 ^ (prefixWord ++ tailWord_3883980).sum := by decide
  have hdescent : baseEnd_3883980 < baseStart_3883980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883993 : List Nat := [1, 2, 1, 2, 5, 1, 11]
def baseStart_3883993 : Nat := 118140960795 + 3883993 * 2 ^ 59
def prefixEnd_3883993 : Nat := 4983230072969 + 3 ^ 40 * 3883993 * 2
def baseEnd_3883993 : Nat := 24621669971584291274387

theorem tailTrace_3883993 : CollatzResearch.WordTrace tailWord_3883993 prefixEnd_3883993 24621669971584291274387 := by
  unfold tailWord_3883993
  simp only [CollatzResearch.WordTrace]
  refine ⟨141660862617964169038856633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94440575078642779359237755 141660862617964169038856633)
  ·
    refine ⟨106245646963473126779142475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141660862617964169038856633 106245646963473126779142475)
    ·
      refine ⟨159368470445209690168713713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106245646963473126779142475 159368470445209690168713713)
      ·
        refine ⟨119526352833907267626535285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159368470445209690168713713 119526352833907267626535285)
        ·
          refine ⟨11205595578178806339987683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119526352833907267626535285 11205595578178806339987683)
          ·
            refine ⟨16808393367268209509981525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205595578178806339987683 16808393367268209509981525)
            ·
              refine ⟨24621669971584291274387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16808393367268209509981525 24621669971584291274387)
              ·
                rfl

theorem cell23_3883993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 11].length) (baseStart_3883993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883993 prefixEnd_3883993 := by exact prefixLift 3883993
  have htrace : WordTrace (prefixWord ++ tailWord_3883993) baseStart_3883993 baseEnd_3883993 := by
    simpa [prefixWord, tailWord_3883993, baseEnd_3883993] using wordTrace_append hprefix tailTrace_3883993
  have hstable : (prefixWord ++ tailWord_3883993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883993).length < 2 ^ (prefixWord ++ tailWord_3883993).sum := by decide
  have hdescent : baseEnd_3883993 < baseStart_3883993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3883997 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3883997 : Nat := 118140960795 + 3883997 * 2 ^ 59
def prefixEnd_3883997 : Nat := 4983230072969 + 3 ^ 40 * 3883997 * 2
def baseEnd_3883997 : Nat := 664785773873648525858443

theorem tailTrace_3883997 : CollatzResearch.WordTrace tailWord_3883997 prefixEnd_3883997 664785773873648525858443 := by
  unfold tailWord_3883997
  simp only [CollatzResearch.WordTrace]
  refine ⟨141661008509949677722002245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94440672339966451814668163 141661008509949677722002245)
  ·
    refine ⟨26561439095615564572875421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141661008509949677722002245 26561439095615564572875421)
    ·
      refine ⟨9960539660855836714828283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26561439095615564572875421 9960539660855836714828283)
      ·
        refine ⟨14940809491283755072242425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960539660855836714828283 14940809491283755072242425)
        ·
          refine ⟨11205607118462816304181819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14940809491283755072242425 11205607118462816304181819)
          ·
            refine ⟨16808410677694224456272729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205607118462816304181819 16808410677694224456272729)
            ·
              refine ⟨12606308008270668342204547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808410677694224456272729 12606308008270668342204547)
              ·
                refine ⟨18909462012406002513306821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12606308008270668342204547 18909462012406002513306821)
                ·
                  refine ⟨3545524127326125471245029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18909462012406002513306821 3545524127326125471245029)
                  ·
                    refine ⟨664785773873648525858443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545524127326125471245029 664785773873648525858443)
                    ·
                      rfl

theorem cell23_3883997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3883997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3883997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3883997 prefixEnd_3883997 := by exact prefixLift 3883997
  have htrace : WordTrace (prefixWord ++ tailWord_3883997) baseStart_3883997 baseEnd_3883997 := by
    simpa [prefixWord, tailWord_3883997, baseEnd_3883997] using wordTrace_append hprefix tailTrace_3883997
  have hstable : (prefixWord ++ tailWord_3883997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3883997).length < 2 ^ (prefixWord ++ tailWord_3883997).sum := by decide
  have hdescent : baseEnd_3883997 < baseStart_3883997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3883997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884010 : List Nat := [3, 1, 3, 1, 2, 3, 2, 8]
def baseStart_3884010 : Nat := 118140960795 + 3884010 * 2 ^ 59
def prefixEnd_3884010 : Nat := 4983230072969 + 3 ^ 40 * 3884010 * 2
def baseEnd_3884010 : Nat := 73865333217387186174547

theorem tailTrace_3884010 : CollatzResearch.WordTrace tailWord_3884010 prefixEnd_3884010 73865333217387186174547 := by
  unfold tailWord_3884010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415370664725645235556371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94440988439268387294816989 35415370664725645235556371)
  ·
    refine ⟨53123055997088467853334557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35415370664725645235556371 53123055997088467853334557)
    ·
      refine ⟨19921145998908175445000459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53123055997088467853334557 19921145998908175445000459)
      ·
        refine ⟨29881718998362263167500689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921145998908175445000459 29881718998362263167500689)
        ·
          refine ⟨22411289248771697375625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29881718998362263167500689 22411289248771697375625517)
          ·
            refine ⟨8404233468289386515859569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22411289248771697375625517 8404233468289386515859569)
            ·
              refine ⟨6303175101217039886894677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404233468289386515859569 6303175101217039886894677)
              ·
                refine ⟨73865333217387186174547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6303175101217039886894677 73865333217387186174547)
                ·
                  rfl

theorem cell23_3884010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_3884010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884010 prefixEnd_3884010 := by exact prefixLift 3884010
  have htrace : WordTrace (prefixWord ++ tailWord_3884010) baseStart_3884010 baseEnd_3884010 := by
    simpa [prefixWord, tailWord_3884010, baseEnd_3884010] using wordTrace_append hprefix tailTrace_3884010
  have hstable : (prefixWord ++ tailWord_3884010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884010).length < 2 ^ (prefixWord ++ tailWord_3884010).sum := by decide
  have hdescent : baseEnd_3884010 < baseStart_3884010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884014 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3884014 : Nat := 118140960795 + 3884014 * 2 ^ 59
def prefixEnd_3884014 : Nat := 4983230072969 + 3 ^ 40 * 3884014 * 2
def baseEnd_3884014 : Nat := 664788683597357337020917

theorem tailTrace_3884014 : CollatzResearch.WordTrace tailWord_3884014 prefixEnd_3884014 664788683597357337020917 := by
  unfold tailWord_3884014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707703568861011203171387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94441085700592059750247397 17707703568861011203171387)
  ·
    refine ⟨26561555353291516804757081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17707703568861011203171387 26561555353291516804757081)
    ·
      refine ⟨19921166514968637603567811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26561555353291516804757081 19921166514968637603567811)
      ·
        refine ⟨29881749772452956405351717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921166514968637603567811 29881749772452956405351717)
        ·
          refine ⟨5602828082334929326003447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29881749772452956405351717 5602828082334929326003447)
          ·
            refine ⟨8404242123502393989005171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602828082334929326003447 8404242123502393989005171)
            ·
              refine ⟨12606363185253590983507757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404242123502393989005171 12606363185253590983507757)
              ·
                refine ⟨4727386194470096618815409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606363185253590983507757 4727386194470096618815409)
                ·
                  refine ⟨3545539645852572464111557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727386194470096618815409 3545539645852572464111557)
                  ·
                    refine ⟨664788683597357337020917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545539645852572464111557 664788683597357337020917)
                    ·
                      rfl

theorem cell23_3884014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3884014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884014 prefixEnd_3884014 := by exact prefixLift 3884014
  have htrace : WordTrace (prefixWord ++ tailWord_3884014) baseStart_3884014 baseEnd_3884014 := by
    simpa [prefixWord, tailWord_3884014, baseEnd_3884014] using wordTrace_append hprefix tailTrace_3884014
  have hstable : (prefixWord ++ tailWord_3884014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884014).length < 2 ^ (prefixWord ++ tailWord_3884014).sum := by decide
  have hdescent : baseEnd_3884014 < baseStart_3884014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884055 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3884055 : Nat := 118140960795 + 3884055 * 2 ^ 59
def prefixEnd_3884055 : Nat := 4983230072969 + 3 ^ 40 * 3884055 * 2
def baseEnd_3884055 : Nat := 1994387103498906350650063

theorem tailTrace_3884055 : CollatzResearch.WordTrace tailWord_3884055 prefixEnd_3884055 1994387103498906350650063 := by
  unfold tailWord_3884055
  simp only [CollatzResearch.WordTrace]
  refine ⟨141663123943739553627613619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94442082629159702418409079 141663123943739553627613619)
  ·
    refine ⟨212494685915609330441420429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141663123943739553627613619 212494685915609330441420429)
    ·
      refine ⟨79685507218353498915532661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212494685915609330441420429 79685507218353498915532661)
      ·
        refine ⟨7470516301720640523331187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79685507218353498915532661 7470516301720640523331187)
        ·
          refine ⟨11205774452580960784996781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470516301720640523331187 11205774452580960784996781)
          ·
            refine ⟨4202165419717860294373793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11205774452580960784996781 4202165419717860294373793)
            ·
              refine ⟨3151624064788395220780345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4202165419717860294373793 3151624064788395220780345)
              ·
                refine ⟨2363718048591296415585259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151624064788395220780345 2363718048591296415585259)
                ·
                  refine ⟨3545577072886944623377889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363718048591296415585259 3545577072886944623377889)
                  ·
                    refine ⟨2659182804665208467533417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545577072886944623377889 2659182804665208467533417)
                    ·
                      refine ⟨1994387103498906350650063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659182804665208467533417 1994387103498906350650063)
                      ·
                        rfl

theorem cell23_3884055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3884055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884055 prefixEnd_3884055 := by exact prefixLift 3884055
  have htrace : WordTrace (prefixWord ++ tailWord_3884055) baseStart_3884055 baseEnd_3884055 := by
    simpa [prefixWord, tailWord_3884055, baseEnd_3884055] using wordTrace_append hprefix tailTrace_3884055
  have hstable : (prefixWord ++ tailWord_3884055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884055).length < 2 ^ (prefixWord ++ tailWord_3884055).sum := by decide
  have hdescent : baseEnd_3884055 < baseStart_3884055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884071 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3884071 : Nat := 118140960795 + 3884071 * 2 ^ 59
def prefixEnd_3884071 : Nat := 4983230072969 + 3 ^ 40 * 3884071 * 2
def baseEnd_3884071 : Nat := 1994395319189378288049989

theorem tailTrace_3884071 : CollatzResearch.WordTrace tailWord_3884071 prefixEnd_3884071 1994395319189378288049989 := by
  unfold tailWord_3884071
  simp only [CollatzResearch.WordTrace]
  refine ⟨141663707511681588360196067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94442471674454392240130711 141663707511681588360196067)
  ·
    refine ⟨212495561267522382540294101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141663707511681588360196067 212495561267522382540294101)
    ·
      refine ⟨4980364717207555840788143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212495561267522382540294101 4980364717207555840788143)
      ·
        refine ⟨7470547075811333761182215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980364717207555840788143 7470547075811333761182215)
        ·
          refine ⟨11205820613717000641773323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470547075811333761182215 11205820613717000641773323)
          ·
            refine ⟨16808730920575500962659985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205820613717000641773323 16808730920575500962659985)
            ·
              refine ⟨12606548190431625721994989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808730920575500962659985 12606548190431625721994989)
              ·
                refine ⟨4727455571411859645748121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606548190431625721994989 4727455571411859645748121)
                ·
                  refine ⟨3545591678558894734311091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727455571411859645748121 3545591678558894734311091)
                  ·
                    refine ⟨5318387517838342101466637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3545591678558894734311091 5318387517838342101466637)
                    ·
                      refine ⟨1994395319189378288049989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318387517838342101466637 1994395319189378288049989)
                      ·
                        rfl

theorem cell23_3884071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3884071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884071 prefixEnd_3884071 := by exact prefixLift 3884071
  have htrace : WordTrace (prefixWord ++ tailWord_3884071) baseStart_3884071 baseEnd_3884071 := by
    simpa [prefixWord, tailWord_3884071, baseEnd_3884071] using wordTrace_append hprefix tailTrace_3884071
  have hstable : (prefixWord ++ tailWord_3884071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884071).length < 2 ^ (prefixWord ++ tailWord_3884071).sum := by decide
  have hdescent : baseEnd_3884071 < baseStart_3884071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884080 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_3884080 : Nat := 118140960795 + 3884080 * 2 ^ 59
def prefixEnd_3884080 : Nat := 4983230072969 + 3 ^ 40 * 3884080 * 2
def baseEnd_3884080 : Nat := 1994399940515268752837447

theorem tailTrace_3884080 : CollatzResearch.WordTrace tailWord_3884080 prefixEnd_3884080 1994399940515268752837447 := by
  unfold tailWord_3884080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70832017884324491448636847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94442690512432655264849129 70832017884324491448636847)
  ·
    refine ⟨106248026826486737172955271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70832017884324491448636847 106248026826486737172955271)
    ·
      refine ⟨159372040239730105759432907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106248026826486737172955271 159372040239730105759432907)
      ·
        refine ⟨239058060359595158639149361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159372040239730105759432907 239058060359595158639149361)
        ·
          refine ⟨179293545269696368979362021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239058060359595158639149361 179293545269696368979362021)
          ·
            refine ⟨33617539738068069183630379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179293545269696368979362021 33617539738068069183630379)
            ·
              refine ⟨50426309607102103775445569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33617539738068069183630379 50426309607102103775445569)
              ·
                refine ⟨37819732205326577831584177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50426309607102103775445569 37819732205326577831584177)
                ·
                  refine ⟨28364799153994933373688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37819732205326577831584177 28364799153994933373688133)
                  ·
                    refine ⟨5318399841374050007566525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28364799153994933373688133 5318399841374050007566525)
                    ·
                      refine ⟨1994399940515268752837447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318399841374050007566525 1994399940515268752837447)
                      ·
                        rfl

theorem cell23_3884080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_3884080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884080 prefixEnd_3884080 := by exact prefixLift 3884080
  have htrace : WordTrace (prefixWord ++ tailWord_3884080) baseStart_3884080 baseEnd_3884080 := by
    simpa [prefixWord, tailWord_3884080, baseEnd_3884080] using wordTrace_append hprefix tailTrace_3884080
  have hstable : (prefixWord ++ tailWord_3884080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884080).length < 2 ^ (prefixWord ++ tailWord_3884080).sum := by decide
  have hdescent : baseEnd_3884080 < baseStart_3884080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884117 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 5]
def baseStart_3884117 : Nat := 118140960795 + 3884117 * 2 ^ 59
def prefixEnd_3884117 : Nat := 4983230072969 + 3 ^ 40 * 3884117 * 2
def baseEnd_3884117 : Nat := 221602104366609456452753

theorem tailTrace_3884117 : CollatzResearch.WordTrace tailWord_3884117 prefixEnd_3884117 221602104366609456452753 := by
  unfold tailWord_3884117
  simp only [CollatzResearch.WordTrace]
  refine ⟨141665385269514938216370605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94443590179676625477580403 141665385269514938216370605)
  ·
    refine ⟨53124519476068101831138977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141665385269514938216370605 53124519476068101831138977)
    ·
      refine ⟨39843389607051076373354233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53124519476068101831138977 39843389607051076373354233)
      ·
        refine ⟨29882542205288307280015675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39843389607051076373354233 29882542205288307280015675)
        ·
          refine ⟨44823813307932460920023513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29882542205288307280015675 44823813307932460920023513)
          ·
            refine ⟨33617859980949345690017635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44823813307932460920023513 33617859980949345690017635)
            ·
              refine ⟨50426789971424018535026453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33617859980949345690017635 50426789971424018535026453)
              ·
                refine ⟨2363755779910500868829365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50426789971424018535026453 2363755779910500868829365)
                ·
                  refine ⟨221602104366609456452753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2363755779910500868829365 221602104366609456452753)
                  ·
                    rfl

theorem cell23_3884117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_3884117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884117 prefixEnd_3884117 := by exact prefixLift 3884117
  have htrace : WordTrace (prefixWord ++ tailWord_3884117) baseStart_3884117 baseEnd_3884117 := by
    simpa [prefixWord, tailWord_3884117, baseEnd_3884117] using wordTrace_append hprefix tailTrace_3884117
  have hstable : (prefixWord ++ tailWord_3884117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884117).length < 2 ^ (prefixWord ++ tailWord_3884117).sum := by decide
  have hdescent : baseEnd_3884117 < baseStart_3884117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884224 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 6]
def baseStart_3884224 : Nat := 118140960795 + 3884224 * 2 ^ 59
def prefixEnd_3884224 : Nat := 4983230072969 + 3 ^ 40 * 3884224 * 2
def baseEnd_3884224 : Nat := 221608209081057354381865

theorem tailTrace_3884224 : CollatzResearch.WordTrace tailWord_3884224 prefixEnd_3884224 221608209081057354381865 := by
  unfold tailWord_3884224
  simp only [CollatzResearch.WordTrace]
  refine ⟨70834643940063647745257863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94446191920084863660343817 70834643940063647745257863)
  ·
    refine ⟨106251965910095471617886795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70834643940063647745257863 106251965910095471617886795)
    ·
      refine ⟨159377948865143207426830193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106251965910095471617886795 159377948865143207426830193)
      ·
        refine ⟨119533461648857405570122645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159377948865143207426830193 119533461648857405570122645)
        ·
          refine ⟨5603131014790190886099499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119533461648857405570122645 5603131014790190886099499)
          ·
            refine ⟨8404696522185286329149249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603131014790190886099499 8404696522185286329149249)
            ·
              refine ⟨6303522391638964746861937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404696522185286329149249 6303522391638964746861937)
              ·
                refine ⟨4727641793729223560146453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303522391638964746861937 4727641793729223560146453)
                ·
                  refine ⟨221608209081057354381865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4727641793729223560146453 221608209081057354381865)
                  ·
                    rfl

theorem cell23_3884224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_3884224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884224 prefixEnd_3884224 := by exact prefixLift 3884224
  have htrace : WordTrace (prefixWord ++ tailWord_3884224) baseStart_3884224 baseEnd_3884224 := by
    simpa [prefixWord, tailWord_3884224, baseEnd_3884224] using wordTrace_append hprefix tailTrace_3884224
  have hstable : (prefixWord ++ tailWord_3884224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884224).length < 2 ^ (prefixWord ++ tailWord_3884224).sum := by decide
  have hdescent : baseEnd_3884224 < baseStart_3884224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884228 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3884228 : Nat := 118140960795 + 3884228 * 2 ^ 59
def prefixEnd_3884228 : Nat := 4983230072969 + 3 ^ 40 * 3884228 * 2
def baseEnd_3884228 : Nat := 664825311884044724595589

theorem tailTrace_3884228 : CollatzResearch.WordTrace tailWord_3884228 prefixEnd_3884228 664825311884044724595589 := by
  unfold tailWord_3884228
  simp only [CollatzResearch.WordTrace]
  refine ⟨70834716886056402086830669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94446289181408536115774225 70834716886056402086830669)
  ·
    refine ⟨26563018832271150782561501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70834716886056402086830669 26563018832271150782561501)
    ·
      refine ⟨9961132062101681543460563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26563018832271150782561501 9961132062101681543460563)
      ·
        refine ⟨14941698093152522315190845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9961132062101681543460563 14941698093152522315190845)
        ·
          refine ⟨5603136784932195868196567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14941698093152522315190845 5603136784932195868196567)
          ·
            refine ⟨8404705177398293802294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603136784932195868196567 8404705177398293802294851)
            ·
              refine ⟨12607057766097440703442277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404705177398293802294851 12607057766097440703442277)
              ·
                refine ⟨2363823331143270131895427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12607057766097440703442277 2363823331143270131895427)
                ·
                  refine ⟨3545734996714905197843141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363823331143270131895427 3545734996714905197843141)
                  ·
                    refine ⟨664825311884044724595589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545734996714905197843141 664825311884044724595589)
                    ·
                      rfl

theorem cell23_3884228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3884228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884228 prefixEnd_3884228 := by exact prefixLift 3884228
  have htrace : WordTrace (prefixWord ++ tailWord_3884228) baseStart_3884228 baseEnd_3884228 := by
    simpa [prefixWord, tailWord_3884228, baseEnd_3884228] using wordTrace_append hprefix tailTrace_3884228
  have hstable : (prefixWord ++ tailWord_3884228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884228).length < 2 ^ (prefixWord ++ tailWord_3884228).sum := by decide
  have hdescent : baseEnd_3884228 < baseStart_3884228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884261 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3884261 : Nat := 118140960795 + 3884261 * 2 ^ 59
def prefixEnd_3884261 : Nat := 4983230072969 + 3 ^ 40 * 3884261 * 2
def baseEnd_3884261 : Nat := 1994492880513732544674115

theorem tailTrace_3884261 : CollatzResearch.WordTrace tailWord_3884261 prefixEnd_3884261 1994492880513732544674115 := by
  unfold tailWord_3884261
  simp only [CollatzResearch.WordTrace]
  refine ⟨141670637380993250809612637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94447091587328833873075091 141670637380993250809612637)
  ·
    refine ⟨53126489017872469053604739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141670637380993250809612637 53126489017872469053604739)
    ·
      refine ⟨79689733526808703580407109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53126489017872469053604739 79689733526808703580407109)
      ·
        refine ⟨14941825036276631921326333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79689733526808703580407109 14941825036276631921326333)
        ·
          refine ⟨5603184388603736970497375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14941825036276631921326333 5603184388603736970497375)
          ·
            refine ⟨8404776582905605455746063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603184388603736970497375 8404776582905605455746063)
            ·
              refine ⟨12607164874358408183619095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404776582905605455746063 12607164874358408183619095)
              ·
                refine ⟨18910747311537612275428643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607164874358408183619095 18910747311537612275428643)
                ·
                  refine ⟨28366120967306418413142965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18910747311537612275428643 28366120967306418413142965)
                  ·
                    refine ⟨2659323840684976726232153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28366120967306418413142965 2659323840684976726232153)
                    ·
                      refine ⟨1994492880513732544674115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659323840684976726232153 1994492880513732544674115)
                      ·
                        rfl

theorem cell23_3884261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3884261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884261 prefixEnd_3884261 := by exact prefixLift 3884261
  have htrace : WordTrace (prefixWord ++ tailWord_3884261) baseStart_3884261 baseEnd_3884261 := by
    simpa [prefixWord, tailWord_3884261, baseEnd_3884261] using wordTrace_append hprefix tailTrace_3884261
  have hstable : (prefixWord ++ tailWord_3884261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884261).length < 2 ^ (prefixWord ++ tailWord_3884261).sum := by decide
  have hdescent : baseEnd_3884261 < baseStart_3884261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884267 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 6]
def baseStart_3884267 : Nat := 118140960795 + 3884267 * 2 ^ 59
def prefixEnd_3884267 : Nat := 4983230072969 + 3 ^ 40 * 3884267 * 2
def baseEnd_3884267 : Nat := 664831987132553173733029

theorem tailTrace_3884267 : CollatzResearch.WordTrace tailWord_3884267 prefixEnd_3884267 664831987132553173733029 := by
  unfold tailWord_3884267
  simp only [CollatzResearch.WordTrace]
  refine ⟨141670856218971513834331055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94447237479314342556220703 141670856218971513834331055)
  ·
    refine ⟨212506284328457270751496583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141670856218971513834331055 212506284328457270751496583)
    ·
      refine ⟨318759426492685906127244875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212506284328457270751496583 318759426492685906127244875)
      ·
        refine ⟨478139139739028859190867313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318759426492685906127244875 478139139739028859190867313)
        ·
          refine ⟨358604354804271644393150485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478139139739028859190867313 358604354804271644393150485)
          ·
            refine ⟨16809579131450233330928929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358604354804271644393150485 16809579131450233330928929)
            ·
              refine ⟨12607184348587674998196697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809579131450233330928929 12607184348587674998196697)
              ·
                refine ⟨9455388261440756248647523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12607184348587674998196697 9455388261440756248647523)
                ·
                  refine ⟨14183082392161134372971285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455388261440756248647523 14183082392161134372971285)
                  ·
                    refine ⟨664831987132553173733029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14183082392161134372971285 664831987132553173733029)
                    ·
                      rfl

theorem cell23_3884267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_3884267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884267 prefixEnd_3884267 := by exact prefixLift 3884267
  have htrace : WordTrace (prefixWord ++ tailWord_3884267) baseStart_3884267 baseEnd_3884267 := by
    simpa [prefixWord, tailWord_3884267, baseEnd_3884267] using wordTrace_append hprefix tailTrace_3884267
  have hstable : (prefixWord ++ tailWord_3884267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884267).length < 2 ^ (prefixWord ++ tailWord_3884267).sum := by decide
  have hdescent : baseEnd_3884267 < baseStart_3884267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884268 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_3884268 : Nat := 118140960795 + 3884268 * 2 ^ 59
def prefixEnd_3884268 : Nat := 4983230072969 + 3 ^ 40 * 3884268 * 2
def baseEnd_3884268 : Nat := 1994496474878314017286583

theorem tailTrace_3884268 : CollatzResearch.WordTrace tailWord_3884268 prefixEnd_3884268 1994496474878314017286583 := by
  unfold tailWord_3884268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70835446345983945502558729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94447261794645260670078305 70835446345983945502558729)
  ·
    refine ⟨53126584759487959126919047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70835446345983945502558729 53126584759487959126919047)
    ·
      refine ⟨79689877139231938690378571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53126584759487959126919047 79689877139231938690378571)
      ·
        refine ⟨119534815708847908035567857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79689877139231938690378571 119534815708847908035567857)
        ·
          refine ⟨89651111781635931026675893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119534815708847908035567857 89651111781635931026675893)
          ·
            refine ⟨8404791729528368533750865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89651111781635931026675893 8404791729528368533750865)
            ·
              refine ⟨6303593797146276400313149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404791729528368533750865 6303593797146276400313149)
              ·
                refine ⟨2363847673929853650117431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6303593797146276400313149 2363847673929853650117431)
                ·
                  refine ⟨3545771510894780475176147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363847673929853650117431 3545771510894780475176147)
                  ·
                    refine ⟨5318657266342170712764221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3545771510894780475176147 5318657266342170712764221)
                    ·
                      refine ⟨1994496474878314017286583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5318657266342170712764221 1994496474878314017286583)
                      ·
                        rfl

theorem cell23_3884268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_3884268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884268 prefixEnd_3884268 := by exact prefixLift 3884268
  have htrace : WordTrace (prefixWord ++ tailWord_3884268) baseStart_3884268 baseEnd_3884268 := by
    simpa [prefixWord, tailWord_3884268, baseEnd_3884268] using wordTrace_append hprefix tailTrace_3884268
  have hstable : (prefixWord ++ tailWord_3884268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884268).length < 2 ^ (prefixWord ++ tailWord_3884268).sum := by decide
  have hdescent : baseEnd_3884268 < baseStart_3884268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3884291 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 3, 2, 2]
def baseStart_3884291 : Nat := 118140960795 + 3884291 * 2 ^ 59
def prefixEnd_3884291 : Nat := 4983230072969 + 3 ^ 40 * 3884291 * 2
def baseEnd_3884291 : Nat := 1994508284933367427298977

theorem tailTrace_3884291 : CollatzResearch.WordTrace tailWord_3884291 prefixEnd_3884291 1994508284933367427298977 := by
  unfold tailWord_3884291
  simp only [CollatzResearch.WordTrace]
  refine ⟨141671731570884565933204727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94447821047256377288803151 141671731570884565933204727)
  ·
    refine ⟨212507597356326848899807091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141671731570884565933204727 212507597356326848899807091)
    ·
      refine ⟨318761396034490273349710637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212507597356326848899807091 318761396034490273349710637)
      ·
        refine ⟨119535523512933852506141489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318761396034490273349710637 119535523512933852506141489)
        ·
          refine ⟨89651642634700389379606117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119535523512933852506141489 89651642634700389379606117)
          ·
            refine ⟨16809682994006323008676147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89651642634700389379606117 16809682994006323008676147)
            ·
              refine ⟨25214524491009484513014221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16809682994006323008676147 25214524491009484513014221)
              ·
                refine ⟨9455446684128556692380333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25214524491009484513014221 9455446684128556692380333)
                ·
                  refine ⟨3545792506548208759642625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9455446684128556692380333 3545792506548208759642625)
                  ·
                    refine ⟨2659344379911156569731969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545792506548208759642625 2659344379911156569731969)
                    ·
                      refine ⟨1994508284933367427298977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2659344379911156569731969 1994508284933367427298977)
                      ·
                        rfl

theorem cell23_3884291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_3884291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3884291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3884291 prefixEnd_3884291 := by exact prefixLift 3884291
  have htrace : WordTrace (prefixWord ++ tailWord_3884291) baseStart_3884291 baseEnd_3884291 := by
    simpa [prefixWord, tailWord_3884291, baseEnd_3884291] using wordTrace_append hprefix tailTrace_3884291
  have hstable : (prefixWord ++ tailWord_3884291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3884291).length < 2 ^ (prefixWord ++ tailWord_3884291).sum := by decide
  have hdescent : baseEnd_3884291 < baseStart_3884291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3884291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
