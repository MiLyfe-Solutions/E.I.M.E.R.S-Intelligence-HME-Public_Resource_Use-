import V185TrunkScan22Chunk030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_277858 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_277858 : Nat := 118140960795 + 277858 * 2 ^ 59
def prefixEnd_277858 : Nat := 4983230072969 + 3 ^ 40 * 277858 * 2
def baseEnd_277858 : Nat := 31705490599350913999369

theorem tailTrace_277858 : CollatzResearch.WordTrace tailWord_277858 prefixEnd_277858 31705490599350913999369 := by
  unfold tailWord_277858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533578456843848803368557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6756209218250263475649485 2533578456843848803368557)
  ·
    refine ⟨950091921316443301263209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2533578456843848803368557 950091921316443301263209)
    ·
      refine ⟨712568940987332475947407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950091921316443301263209 712568940987332475947407)
      ·
        refine ⟨1068853411480998713921111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712568940987332475947407 1068853411480998713921111)
        ·
          refine ⟨1603280117221498070881667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068853411480998713921111 1603280117221498070881667)
          ·
            refine ⟨2404920175832247106322501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603280117221498070881667 2404920175832247106322501)
            ·
              refine ⟨450922532968546332435469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2404920175832247106322501 450922532968546332435469)
              ·
                refine ⟨169095949863204874663301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450922532968546332435469 169095949863204874663301)
                ·
                  refine ⟨31705490599350913999369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169095949863204874663301 31705490599350913999369)
                  ·
                    rfl

theorem cell22_277858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_277858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277858 prefixEnd_277858 := by exact prefixLift 277858
  have htrace : WordTrace (prefixWord ++ tailWord_277858) baseStart_277858 baseEnd_277858 := by
    simpa [prefixWord, tailWord_277858, baseEnd_277858] using wordTrace_append hprefix tailTrace_277858
  have hstable : (prefixWord ++ tailWord_277858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277858).length < 2 ^ (prefixWord ++ tailWord_277858).sum := by decide
  have hdescent : baseEnd_277858 < baseStart_277858 := by decide
  rcases family_descends (prefixWord ++ tailWord_277858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277869 : List Nat := [1, 5, 1, 1, 1, 4, 9]
def baseStart_277869 : Nat := 118140960795 + 277869 * 2 ^ 59
def prefixEnd_277869 : Nat := 4983230072969 + 3 ^ 40 * 277869 * 2
def baseEnd_277869 : Nat := 3522971752698236295299

theorem tailTrace_277869 : CollatzResearch.WordTrace tailWord_277869 prefixEnd_277869 3522971752698236295299 := by
  unfold tailWord_277869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10134715030335544092124661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6756476686890362728083107 10134715030335544092124661)
  ·
    refine ⟨950129534093957258636687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10134715030335544092124661 950129534093957258636687)
    ·
      refine ⟨1425194301140935887955031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950129534093957258636687 1425194301140935887955031)
      ·
        refine ⟨2137791451711403831932547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425194301140935887955031 2137791451711403831932547)
        ·
          refine ⟨3206687177567105747898821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137791451711403831932547 3206687177567105747898821)
          ·
            refine ⟨601253845793832327731029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3206687177567105747898821 601253845793832327731029)
            ·
              refine ⟨3522971752698236295299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 601253845793832327731029 3522971752698236295299)
              ·
                rfl

theorem cell22_277869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 9].length) (baseStart_277869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277869 prefixEnd_277869 := by exact prefixLift 277869
  have htrace : WordTrace (prefixWord ++ tailWord_277869) baseStart_277869 baseEnd_277869 := by
    simpa [prefixWord, tailWord_277869, baseEnd_277869] using wordTrace_append hprefix tailTrace_277869
  have hstable : (prefixWord ++ tailWord_277869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277869).length < 2 ^ (prefixWord ++ tailWord_277869).sum := by decide
  have hdescent : baseEnd_277869 < baseStart_277869 := by decide
  rcases family_descends (prefixWord ++ tailWord_277869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277890 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_277890 : Nat := 118140960795 + 277890 * 2 ^ 59
def prefixEnd_277890 : Nat := 4983230072969 + 3 ^ 40 * 277890 * 2
def baseEnd_277890 : Nat := 95127426052015325198009

theorem tailTrace_277890 : CollatzResearch.WordTrace tailWord_277890 prefixEnd_277890 95127426052015325198009 := by
  unfold tailWord_277890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533870240814866169659781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6756987308839643119092749 2533870240814866169659781)
  ·
    refine ⟨475100670152787406811209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2533870240814866169659781 475100670152787406811209)
    ·
      refine ⟨356325502614590555108407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475100670152787406811209 356325502614590555108407)
      ·
        refine ⟨534488253921885832662611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356325502614590555108407 534488253921885832662611)
        ·
          refine ⟨801732380882828748993917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534488253921885832662611 801732380882828748993917)
          ·
            refine ⟨300649642831060780872719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 801732380882828748993917 300649642831060780872719)
            ·
              refine ⟨450974464246591171309079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300649642831060780872719 450974464246591171309079)
              ·
                refine ⟨676461696369886756963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450974464246591171309079 676461696369886756963619)
                ·
                  refine ⟨1014692544554830135445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676461696369886756963619 1014692544554830135445429)
                  ·
                    refine ⟨95127426052015325198009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1014692544554830135445429 95127426052015325198009)
                    ·
                      rfl

theorem cell22_277890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_277890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277890 prefixEnd_277890 := by exact prefixLift 277890
  have htrace : WordTrace (prefixWord ++ tailWord_277890) baseStart_277890 baseEnd_277890 := by
    simpa [prefixWord, tailWord_277890, baseEnd_277890] using wordTrace_append hprefix tailTrace_277890
  have hstable : (prefixWord ++ tailWord_277890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277890).length < 2 ^ (prefixWord ++ tailWord_277890).sum := by decide
  have hdescent : baseEnd_277890 < baseStart_277890 := by decide
  rcases family_descends (prefixWord ++ tailWord_277890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277914 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_277914 : Nat := 118140960795 + 277914 * 2 ^ 59
def prefixEnd_277914 : Nat := 4983230072969 + 3 ^ 40 * 277914 * 2
def baseEnd_277914 : Nat := 31711880580829087532645

theorem tailTrace_277914 : CollatzResearch.WordTrace tailWord_277914 prefixEnd_277914 31711880580829087532645 := by
  unfold tailWord_277914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534089078793129194378199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6757570876781677851675197 2534089078793129194378199)
  ·
    refine ⟨3801133618189693791567299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2534089078793129194378199 3801133618189693791567299)
    ·
      refine ⟨5701700427284540687350949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801133618189693791567299 5701700427284540687350949)
      ·
        refine ⟨1069068830115851378878303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5701700427284540687350949 1069068830115851378878303)
        ·
          refine ⟨1603603245173777068317455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069068830115851378878303 1603603245173777068317455)
          ·
            refine ⟨2405404867760665602476183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603603245173777068317455 2405404867760665602476183)
            ·
              refine ⟨3608107301640998403714275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405404867760665602476183 3608107301640998403714275)
              ·
                refine ⟨5412160952461497605571413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608107301640998403714275 5412160952461497605571413)
                ·
                  refine ⟨31711880580829087532645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5412160952461497605571413 31711880580829087532645)
                  ·
                    rfl

theorem cell22_277914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_277914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277914 prefixEnd_277914 := by exact prefixLift 277914
  have htrace : WordTrace (prefixWord ++ tailWord_277914) baseStart_277914 baseEnd_277914 := by
    simpa [prefixWord, tailWord_277914, baseEnd_277914] using wordTrace_append hprefix tailTrace_277914
  have hstable : (prefixWord ++ tailWord_277914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277914).length < 2 ^ (prefixWord ++ tailWord_277914).sum := by decide
  have hdescent : baseEnd_277914 < baseStart_277914 := by decide
  rcases family_descends (prefixWord ++ tailWord_277914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277948 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_277948 : Nat := 118140960795 + 277948 * 2 ^ 59
def prefixEnd_277948 : Nat := 4983230072969 + 3 ^ 40 * 277948 * 2
def baseEnd_277948 : Nat := 31715760212440835749277

theorem tailTrace_277948 : CollatzResearch.WordTrace tailWord_277948 prefixEnd_277948 31715760212440835749277 := by
  unfold tailWord_277948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068798198524670292125249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6758397598032893722833665 5068798198524670292125249)
  ·
    refine ⟨3801598648893502719093937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5068798198524670292125249 3801598648893502719093937)
    ·
      refine ⟨2851198986670127039320453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3801598648893502719093937 2851198986670127039320453)
      ·
        refine ⟨534599810000648819872585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2851198986670127039320453 534599810000648819872585)
        ·
          refine ⟨400949857500486614904439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534599810000648819872585 400949857500486614904439)
          ·
            refine ⟨601424786250729922356659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400949857500486614904439 601424786250729922356659)
            ·
              refine ⟨902137179376094883534989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601424786250729922356659 902137179376094883534989)
              ·
                refine ⟨338301442266035581325621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902137179376094883534989 338301442266035581325621)
                ·
                  refine ⟨31715760212440835749277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338301442266035581325621 31715760212440835749277)
                  ·
                    rfl

theorem cell22_277948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_277948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277948 prefixEnd_277948 := by exact prefixLift 277948
  have htrace : WordTrace (prefixWord ++ tailWord_277948) baseStart_277948 baseEnd_277948 := by
    simpa [prefixWord, tailWord_277948, baseEnd_277948] using wordTrace_append hprefix tailTrace_277948
  have hstable : (prefixWord ++ tailWord_277948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277948).length < 2 ^ (prefixWord ++ tailWord_277948).sum := by decide
  have hdescent : baseEnd_277948 < baseStart_277948 := by decide
  rcases family_descends (prefixWord ++ tailWord_277948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277959 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 8]
def baseStart_277959 : Nat := 118140960795 + 277959 * 2 ^ 59
def prefixEnd_277959 : Nat := 4983230072969 + 3 ^ 40 * 277959 * 2
def baseEnd_277959 : Nat := 31717015387374048407599

theorem tailTrace_277959 : CollatzResearch.WordTrace tailWord_277959 prefixEnd_277959 31717015387374048407599 := by
  unfold tailWord_277959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137997600009489462900931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6758665066672992975267287 10137997600009489462900931)
  ·
    refine ⟨15206996400014234194351397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10137997600009489462900931 15206996400014234194351397)
    ·
      refine ⟨2851311825002668911440887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15206996400014234194351397 2851311825002668911440887)
      ·
        refine ⟨4276967737504003367161331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851311825002668911440887 4276967737504003367161331)
        ·
          refine ⟨6415451606256005050741997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276967737504003367161331 6415451606256005050741997)
          ·
            refine ⟨2405794352346001894028249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6415451606256005050741997 2405794352346001894028249)
            ·
              refine ⟨1804345764259501420521187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405794352346001894028249 1804345764259501420521187)
              ·
                refine ⟨2706518646389252130781781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804345764259501420521187 2706518646389252130781781)
                ·
                  refine ⟨31717015387374048407599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2706518646389252130781781 31717015387374048407599)
                  ·
                    rfl

theorem cell22_277959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_277959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277959 prefixEnd_277959 := by exact prefixLift 277959
  have htrace : WordTrace (prefixWord ++ tailWord_277959) baseStart_277959 baseEnd_277959 := by
    simpa [prefixWord, tailWord_277959, baseEnd_277959] using wordTrace_append hprefix tailTrace_277959
  have hstable : (prefixWord ++ tailWord_277959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277959).length < 2 ^ (prefixWord ++ tailWord_277959).sum := by decide
  have hdescent : baseEnd_277959 < baseStart_277959 := by decide
  rcases family_descends (prefixWord ++ tailWord_277959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278008 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_278008 : Nat := 118140960795 + 278008 * 2 ^ 59
def prefixEnd_278008 : Nat := 4983230072969 + 3 ^ 40 * 278008 * 2
def baseEnd_278008 : Nat := 95167819863502350747647

theorem tailTrace_278008 : CollatzResearch.WordTrace tailWord_278008 prefixEnd_278008 95167819863502350747647 := by
  unfold tailWord_278008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069892388415985415717339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6759856517887980554289785 5069892388415985415717339)
  ·
    refine ⟨7604838582623978123576009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069892388415985415717339 7604838582623978123576009)
    ·
      refine ⟨5703628936967983592682007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604838582623978123576009 5703628936967983592682007)
      ·
        refine ⟨8555443405451975389023011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703628936967983592682007 8555443405451975389023011)
        ·
          refine ⟨12833165108177963083534517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555443405451975389023011 12833165108177963083534517)
          ·
            refine ⟨1203109228891684039081361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12833165108177963083534517 1203109228891684039081361)
            ·
              refine ⟨902331921668763029311021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203109228891684039081361 902331921668763029311021)
              ·
                refine ⟨338374470625786135991633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902331921668763029311021 338374470625786135991633)
                ·
                  refine ⟨253780852969339601993725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338374470625786135991633 253780852969339601993725)
                  ·
                    refine ⟨95167819863502350747647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 253780852969339601993725 95167819863502350747647)
                    ·
                      rfl

theorem cell22_278008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_278008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278008 prefixEnd_278008 := by exact prefixLift 278008
  have htrace : WordTrace (prefixWord ++ tailWord_278008) baseStart_278008 baseEnd_278008 := by
    simpa [prefixWord, tailWord_278008, baseEnd_278008] using wordTrace_append hprefix tailTrace_278008
  have hstable : (prefixWord ++ tailWord_278008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278008).length < 2 ^ (prefixWord ++ tailWord_278008).sum := by decide
  have hdescent : baseEnd_278008 < baseStart_278008 := by decide
  rcases family_descends (prefixWord ++ tailWord_278008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278019 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_278019 : Nat := 118140960795 + 278019 * 2 ^ 59
def prefixEnd_278019 : Nat := 4983230072969 + 3 ^ 40 * 278019 * 2
def baseEnd_278019 : Nat := 95171585388301988722613

theorem tailTrace_278019 : CollatzResearch.WordTrace tailWord_278019 prefixEnd_278019 95171585388301988722613 := by
  unfold tailWord_278019
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140185979792119710085111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6760123986528079806723407 10140185979792119710085111)
  ·
    refine ⟨15210278969688179565127667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10140185979792119710085111 15210278969688179565127667)
    ·
      refine ⟨22815418454532269347691501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15210278969688179565127667 22815418454532269347691501)
      ·
        refine ⟨8555781920449601005384313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22815418454532269347691501 8555781920449601005384313)
        ·
          refine ⟨6416836440337200754038235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8555781920449601005384313 6416836440337200754038235)
          ·
            refine ⟨9625254660505801131057353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416836440337200754038235 9625254660505801131057353)
            ·
              refine ⟨7218940995379350848293015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9625254660505801131057353 7218940995379350848293015)
              ·
                refine ⟨10828411493069026272439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7218940995379350848293015 10828411493069026272439523)
                ·
                  refine ⟨16242617239603539408659285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10828411493069026272439523 16242617239603539408659285)
                  ·
                    refine ⟨95171585388301988722613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16242617239603539408659285 95171585388301988722613)
                    ·
                      rfl

theorem cell22_278019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_278019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278019 prefixEnd_278019 := by exact prefixLift 278019
  have htrace : WordTrace (prefixWord ++ tailWord_278019) baseStart_278019 baseEnd_278019 := by
    simpa [prefixWord, tailWord_278019, baseEnd_278019] using wordTrace_append hprefix tailTrace_278019
  have hstable : (prefixWord ++ tailWord_278019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278019).length < 2 ^ (prefixWord ++ tailWord_278019).sum := by decide
  have hdescent : baseEnd_278019 < baseStart_278019 := by decide
  rcases family_descends (prefixWord ++ tailWord_278019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278023 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_278023 : Nat := 118140960795 + 278023 * 2 ^ 59
def prefixEnd_278023 : Nat := 4983230072969 + 3 ^ 40 * 278023 * 2
def baseEnd_278023 : Nat := 95172954670047311622601

theorem tailTrace_278023 : CollatzResearch.WordTrace tailWord_278023 prefixEnd_278023 95172954670047311622601 := by
  unfold tailWord_278023
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140331871777628393230723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6760221247851752262153815 10140331871777628393230723)
  ·
    refine ⟨15210497807666442589846085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10140331871777628393230723 15210497807666442589846085)
    ·
      refine ⟨2851968338937457985596141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15210497807666442589846085 2851968338937457985596141)
      ·
        refine ⟨1069488127101546744598553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2851968338937457985596141 1069488127101546744598553)
        ·
          refine ⟨802116095326160058448915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069488127101546744598553 802116095326160058448915)
          ·
            refine ⟨1203174142989240087673373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802116095326160058448915 1203174142989240087673373)
            ·
              refine ⟨451190303620965032877515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203174142989240087673373 451190303620965032877515)
              ·
                refine ⟨676785455431447549316273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451190303620965032877515 676785455431447549316273)
                ·
                  refine ⟨507589091573585661987205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676785455431447549316273 507589091573585661987205)
                  ·
                    refine ⟨95172954670047311622601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507589091573585661987205 95172954670047311622601)
                    ·
                      rfl

theorem cell22_278023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_278023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278023 prefixEnd_278023 := by exact prefixLift 278023
  have htrace : WordTrace (prefixWord ++ tailWord_278023) baseStart_278023 baseEnd_278023 := by
    simpa [prefixWord, tailWord_278023, baseEnd_278023] using wordTrace_append hprefix tailTrace_278023
  have hstable : (prefixWord ++ tailWord_278023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278023).length < 2 ^ (prefixWord ++ tailWord_278023).sum := by decide
  have hdescent : baseEnd_278023 < baseStart_278023 := by decide
  rcases family_descends (prefixWord ++ tailWord_278023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278130 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_278130 : Nat := 118140960795 + 278130 * 2 ^ 59
def prefixEnd_278130 : Nat := 4983230072969 + 3 ^ 40 * 278130 * 2
def baseEnd_278130 : Nat := 95209582956734699197273

theorem tailTrace_278130 : CollatzResearch.WordTrace tailWord_278130 prefixEnd_278130 95209582956734699197273 := by
  unfold tailWord_278130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536058620597496416843961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6762822988259990444917229 2536058620597496416843961)
  ·
    refine ⟨1902043965448122312632971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536058620597496416843961 1902043965448122312632971)
    ·
      refine ⟨2853065948172183468949457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902043965448122312632971 2853065948172183468949457)
      ·
        refine ⟨2139799461129137601712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2853065948172183468949457 2139799461129137601712093)
        ·
          refine ⟨802424797923426600642035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2139799461129137601712093 802424797923426600642035)
          ·
            refine ⟨1203637196885139900963053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802424797923426600642035 1203637196885139900963053)
            ·
              refine ⟨451363948831927462861145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203637196885139900963053 451363948831927462861145)
              ·
                refine ⟨338522961623945597145859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451363948831927462861145 338522961623945597145859)
                ·
                  refine ⟨507784442435918395718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338522961623945597145859 507784442435918395718789)
                  ·
                    refine ⟨95209582956734699197273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507784442435918395718789 95209582956734699197273)
                    ·
                      rfl

theorem cell22_278130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_278130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278130 prefixEnd_278130 := by exact prefixLift 278130
  have htrace : WordTrace (prefixWord ++ tailWord_278130) baseStart_278130 baseEnd_278130 := by
    simpa [prefixWord, tailWord_278130, baseEnd_278130] using wordTrace_append hprefix tailTrace_278130
  have hstable : (prefixWord ++ tailWord_278130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278130).length < 2 ^ (prefixWord ++ tailWord_278130).sum := by decide
  have hdescent : baseEnd_278130 < baseStart_278130 := by decide
  rcases family_descends (prefixWord ++ tailWord_278130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278162 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_278162 : Nat := 118140960795 + 278162 * 2 ^ 59
def prefixEnd_278162 : Nat := 4983230072969 + 3 ^ 40 * 278162 * 2
def baseEnd_278162 : Nat := 31740179070232427465725

theorem tailTrace_278162 : CollatzResearch.WordTrace tailWord_278162 prefixEnd_278162 31740179070232427465725 := by
  unfold tailWord_278162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536350404568513783135185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6763601078849370088360493 2536350404568513783135185)
  ·
    refine ⟨1902262803426385337351389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536350404568513783135185 1902262803426385337351389)
    ·
      refine ⟨713348551284894501506771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1902262803426385337351389 713348551284894501506771)
      ·
        refine ⟨1070022826927341752260157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713348551284894501506771 1070022826927341752260157)
        ·
          refine ⟨401258560097753157097559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1070022826927341752260157 401258560097753157097559)
          ·
            refine ⟨601887840146629735646339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401258560097753157097559 601887840146629735646339)
            ·
              refine ⟨902831760219944603469509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601887840146629735646339 902831760219944603469509)
              ·
                refine ⟨169280955041239613150533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 902831760219944603469509 169280955041239613150533)
                ·
                  refine ⟨31740179070232427465725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169280955041239613150533 31740179070232427465725)
                  ·
                    rfl

theorem cell22_278162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_278162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278162 prefixEnd_278162 := by exact prefixLift 278162
  have htrace : WordTrace (prefixWord ++ tailWord_278162) baseStart_278162 baseEnd_278162 := by
    simpa [prefixWord, tailWord_278162, baseEnd_278162] using wordTrace_append hprefix tailTrace_278162
  have hstable : (prefixWord ++ tailWord_278162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278162).length < 2 ^ (prefixWord ++ tailWord_278162).sum := by decide
  have hdescent : baseEnd_278162 < baseStart_278162 := by decide
  rcases family_descends (prefixWord ++ tailWord_278162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278222 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_278222 : Nat := 118140960795 + 278222 * 2 ^ 59
def prefixEnd_278222 : Nat := 4983230072969 + 3 ^ 40 * 278222 * 2
def baseEnd_278222 : Nat := 95241076436877125896991

theorem tailTrace_278222 : CollatzResearch.WordTrace tailWord_278222 prefixEnd_278222 95241076436877125896991 := by
  unfold tailWord_278222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268448749757085672465615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6765059998704456919816613 1268448749757085672465615)
  ·
    refine ⟨1902673124635628508698423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268448749757085672465615 1902673124635628508698423)
    ·
      refine ⟨2854009686953442763047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902673124635628508698423 2854009686953442763047635)
      ·
        refine ⟨4281014530430164144571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854009686953442763047635 4281014530430164144571453)
        ·
          refine ⟨1605380448911311554214295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4281014530430164144571453 1605380448911311554214295)
          ·
            refine ⟨2408070673366967331321443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605380448911311554214295 2408070673366967331321443)
            ·
              refine ⟨3612106010050450996982165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408070673366967331321443 3612106010050450996982165)
              ·
                refine ⟨169317469221114890483539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3612106010050450996982165 169317469221114890483539)
                ·
                  refine ⟨253976203831672335725309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169317469221114890483539 253976203831672335725309)
                  ·
                    refine ⟨95241076436877125896991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 253976203831672335725309 95241076436877125896991)
                    ·
                      rfl

theorem cell22_278222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_278222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278222 prefixEnd_278222 := by exact prefixLift 278222
  have htrace : WordTrace (prefixWord ++ tailWord_278222) baseStart_278222 baseEnd_278222 := by
    simpa [prefixWord, tailWord_278222, baseEnd_278222] using wordTrace_append hprefix tailTrace_278222
  have hstable : (prefixWord ++ tailWord_278222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278222).length < 2 ^ (prefixWord ++ tailWord_278222).sum := by decide
  have hdescent : baseEnd_278222 < baseStart_278222 := by decide
  rcases family_descends (prefixWord ++ tailWord_278222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278233 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_278233 : Nat := 118140960795 + 278233 * 2 ^ 59
def prefixEnd_278233 : Nat := 4983230072969 + 3 ^ 40 * 278233 * 2
def baseEnd_278233 : Nat := 95244841961676763871957

theorem tailTrace_278233 : CollatzResearch.WordTrace tailWord_278233 prefixEnd_278233 95244841961676763871957 := by
  unfold tailWord_278233
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147991201016834258375353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6765327467344556172250235 10147991201016834258375353)
  ·
    refine ⟨7610993400762625693781515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10147991201016834258375353 7610993400762625693781515)
    ·
      refine ⟨11416490101143938540672273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610993400762625693781515 11416490101143938540672273)
      ·
        refine ⟨8562367575857953905504205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11416490101143938540672273 8562367575857953905504205)
        ·
          refine ⟨3210887840946732714564077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8562367575857953905504205 3210887840946732714564077)
          ·
            refine ⟨1204082940355024767961529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3210887840946732714564077 1204082940355024767961529)
            ·
              refine ⟨903062205266268575971147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204082940355024767961529 903062205266268575971147)
              ·
                refine ⟨1354593307899402863956721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903062205266268575971147 1354593307899402863956721)
                ·
                  refine ⟨1015944980924552147967541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354593307899402863956721 1015944980924552147967541)
                  ·
                    refine ⟨95244841961676763871957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1015944980924552147967541 95244841961676763871957)
                    ·
                      rfl

theorem cell22_278233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_278233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278233 prefixEnd_278233 := by exact prefixLift 278233
  have htrace : WordTrace (prefixWord ++ tailWord_278233) baseStart_278233 baseEnd_278233 := by
    simpa [prefixWord, tailWord_278233, baseEnd_278233] using wordTrace_append hprefix tailTrace_278233
  have hstable : (prefixWord ++ tailWord_278233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278233).length < 2 ^ (prefixWord ++ tailWord_278233).sum := by decide
  have hdescent : baseEnd_278233 < baseStart_278233 := by decide
  rcases family_descends (prefixWord ++ tailWord_278233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278325 : List Nat := [1, 3, 3, 1, 5, 9]
def baseStart_278325 : Nat := 118140960795 + 278325 * 2 ^ 59
def prefixEnd_278325 : Nat := 4983230072969 + 3 ^ 40 * 278325 * 2
def baseEnd_278325 : Nat := 1176251054837273957675

theorem tailTrace_278325 : CollatzResearch.WordTrace tailWord_278325 prefixEnd_278325 1176251054837273957675 := by
  unfold tailWord_278325
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151346716683533970724429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6767564477789022647149619 10151346716683533970724429)
  ·
    refine ⟨3806755018756325239021661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10151346716683533970724429 3806755018756325239021661)
    ·
      refine ⟨1427533132033621964633123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3806755018756325239021661 1427533132033621964633123)
      ·
        refine ⟨2141299698050432946949685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1427533132033621964633123 2141299698050432946949685)
        ·
          refine ⟨200746846692228088776533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2141299698050432946949685 200746846692228088776533)
          ·
            refine ⟨1176251054837273957675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 200746846692228088776533 1176251054837273957675)
            ·
              rfl

theorem cell22_278325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 9].length) (baseStart_278325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278325 prefixEnd_278325 := by exact prefixLift 278325
  have htrace : WordTrace (prefixWord ++ tailWord_278325) baseStart_278325 baseEnd_278325 := by
    simpa [prefixWord, tailWord_278325, baseEnd_278325] using wordTrace_append hprefix tailTrace_278325
  have hstable : (prefixWord ++ tailWord_278325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278325).length < 2 ^ (prefixWord ++ tailWord_278325).sum := by decide
  have hdescent : baseEnd_278325 < baseStart_278325 := by decide
  rcases family_descends (prefixWord ++ tailWord_278325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278357 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_278357 : Nat := 118140960795 + 278357 * 2 ^ 59
def prefixEnd_278357 : Nat := 4983230072969 + 3 ^ 40 * 278357 * 2
def baseEnd_278357 : Nat := 95287289695781773771577

theorem tailTrace_278357 : CollatzResearch.WordTrace tailWord_278357 prefixEnd_278357 95287289695781773771577 := by
  unfold tailWord_278357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152513852567603435889325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6768342568378402290592883 10152513852567603435889325)
  ·
    refine ⟨3807192694712851288458497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10152513852567603435889325 3807192694712851288458497)
    ·
      refine ⟨2855394521034638466343873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3807192694712851288458497 2855394521034638466343873)
      ·
        refine ⟨2141545890775978849757905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855394521034638466343873 2141545890775978849757905)
        ·
          refine ⟨1606159418081984137318429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2141545890775978849757905 1606159418081984137318429)
          ·
            refine ⟨602309781780744051494411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1606159418081984137318429 602309781780744051494411)
            ·
              refine ⟨903464672671116077241617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602309781780744051494411 903464672671116077241617)
              ·
                refine ⟨677598504503337057931213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903464672671116077241617 677598504503337057931213)
                ·
                  refine ⟨254099439188751396724205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677598504503337057931213 254099439188751396724205)
                  ·
                    refine ⟨95287289695781773771577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254099439188751396724205 95287289695781773771577)
                    ·
                      rfl

theorem cell22_278357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_278357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278357 prefixEnd_278357 := by exact prefixLift 278357
  have htrace : WordTrace (prefixWord ++ tailWord_278357) baseStart_278357 baseEnd_278357 := by
    simpa [prefixWord, tailWord_278357, baseEnd_278357] using wordTrace_append hprefix tailTrace_278357
  have hstable : (prefixWord ++ tailWord_278357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278357).length < 2 ^ (prefixWord ++ tailWord_278357).sum := by decide
  have hdescent : baseEnd_278357 < baseStart_278357 := by decide
  rcases family_descends (prefixWord ++ tailWord_278357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278447 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 2, 3]
def baseStart_278447 : Nat := 118140960795 + 278447 * 2 ^ 59
def prefixEnd_278447 : Nat := 4983230072969 + 3 ^ 40 * 278447 * 2
def baseEnd_278447 : Nat := 95318098535051539021301

theorem tailTrace_278447 : CollatzResearch.WordTrace tailWord_278447 prefixEnd_278447 95318098535051539021301 := by
  unfold tailWord_278447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155796422241548806665595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6770530948161032537777063 10155796422241548806665595)
  ·
    refine ⟨15233694633362323209998393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10155796422241548806665595 15233694633362323209998393)
    ·
      refine ⟨11425270975021742407498795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15233694633362323209998393 11425270975021742407498795)
      ·
        refine ⟨17137906462532613611248193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11425270975021742407498795 17137906462532613611248193)
        ·
          refine ⟨12853429846899460208436145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17137906462532613611248193 12853429846899460208436145)
          ·
            refine ⟨9640072385174595156327109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12853429846899460208436145 9640072385174595156327109)
            ·
              refine ⟨1807513572220236591811333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9640072385174595156327109 1807513572220236591811333)
              ·
                refine ⟨338908794791294360964625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1807513572220236591811333 338908794791294360964625)
                ·
                  refine ⟨254181596093470770723469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338908794791294360964625 254181596093470770723469)
                  ·
                    refine ⟨95318098535051539021301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254181596093470770723469 95318098535051539021301)
                    ·
                      rfl

theorem cell22_278447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_278447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278447 prefixEnd_278447 := by exact prefixLift 278447
  have htrace : WordTrace (prefixWord ++ tailWord_278447) baseStart_278447 baseEnd_278447 := by
    simpa [prefixWord, tailWord_278447, baseEnd_278447] using wordTrace_append hprefix tailTrace_278447
  have hstable : (prefixWord ++ tailWord_278447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278447).length < 2 ^ (prefixWord ++ tailWord_278447).sum := by decide
  have hdescent : baseEnd_278447 < baseStart_278447 := by decide
  rcases family_descends (prefixWord ++ tailWord_278447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278498 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_278498 : Nat := 118140960795 + 278498 * 2 ^ 59
def prefixEnd_278498 : Nat := 4983230072969 + 3 ^ 40 * 278498 * 2
def baseEnd_278498 : Nat := 95335556877304405996145

theorem tailTrace_278498 : CollatzResearch.WordTrace tailWord_278498 prefixEnd_278498 95335556877304405996145 := by
  unfold tailWord_278498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539414136264196129193037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6771771030037856344514765 2539414136264196129193037)
  ·
    refine ⟨952280301099073548447389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2539414136264196129193037 952280301099073548447389)
    ·
      refine ⟨357105112912152580667771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 952280301099073548447389 357105112912152580667771)
      ·
        refine ⟨535657669368228871001657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357105112912152580667771 535657669368228871001657)
        ·
          refine ⟨401743252026171653251243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535657669368228871001657 401743252026171653251243)
          ·
            refine ⟨602614878039257479876865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401743252026171653251243 602614878039257479876865)
            ·
              refine ⟨451961158529443109907649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602614878039257479876865 451961158529443109907649)
              ·
                refine ⟨338970868897082332430737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451961158529443109907649 338970868897082332430737)
                ·
                  refine ⟨254228151672811749323053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338970868897082332430737 254228151672811749323053)
                  ·
                    refine ⟨95335556877304405996145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254228151672811749323053 95335556877304405996145)
                    ·
                      rfl

theorem cell22_278498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_278498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278498 prefixEnd_278498 := by exact prefixLift 278498
  have htrace : WordTrace (prefixWord ++ tailWord_278498) baseStart_278498 baseEnd_278498 := by
    simpa [prefixWord, tailWord_278498, baseEnd_278498] using wordTrace_append hprefix tailTrace_278498
  have hstable : (prefixWord ++ tailWord_278498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278498).length < 2 ^ (prefixWord ++ tailWord_278498).sum := by decide
  have hdescent : baseEnd_278498 < baseStart_278498 := by decide
  rcases family_descends (prefixWord ++ tailWord_278498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278520 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_278520 : Nat := 118140960795 + 278520 * 2 ^ 59
def prefixEnd_278520 : Nat := 4983230072969 + 3 ^ 40 * 278520 * 2
def baseEnd_278520 : Nat := 95343087926903681946077

theorem tailTrace_278520 : CollatzResearch.WordTrace tailWord_278520 prefixEnd_278520 95343087926903681946077 := by
  unfold tailWord_278520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079229475488541137036507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6772305967318054849382009 5079229475488541137036507)
  ·
    refine ⟨7618844213232811705554761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5079229475488541137036507 7618844213232811705554761)
    ·
      refine ⟨5714133159924608779166071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618844213232811705554761 5714133159924608779166071)
      ·
        refine ⟨8571199739886913168749107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714133159924608779166071 8571199739886913168749107)
        ·
          refine ⟨12856799609830369753123661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8571199739886913168749107 12856799609830369753123661)
          ·
            refine ⟨4821299853686388657421373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12856799609830369753123661 4821299853686388657421373)
            ·
              refine ⟨1807987445132395746533015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4821299853686388657421373 1807987445132395746533015)
              ·
                refine ⟨2711981167698593619799523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807987445132395746533015 2711981167698593619799523)
                ·
                  refine ⟨4067971751547890429699285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711981167698593619799523 4067971751547890429699285)
                  ·
                    refine ⟨95343087926903681946077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4067971751547890429699285 95343087926903681946077)
                    ·
                      rfl

theorem cell22_278520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_278520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278520 prefixEnd_278520 := by exact prefixLift 278520
  have htrace : WordTrace (prefixWord ++ tailWord_278520) baseStart_278520 baseEnd_278520 := by
    simpa [prefixWord, tailWord_278520, baseEnd_278520] using wordTrace_append hprefix tailTrace_278520
  have hstable : (prefixWord ++ tailWord_278520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278520).length < 2 ^ (prefixWord ++ tailWord_278520).sum := by decide
  have hdescent : baseEnd_278520 < baseStart_278520 := by decide
  rcases family_descends (prefixWord ++ tailWord_278520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278526 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_278526 : Nat := 118140960795 + 278526 * 2 ^ 59
def prefixEnd_278526 : Nat := 4983230072969 + 3 ^ 40 * 278526 * 2
def baseEnd_278526 : Nat := 95345141849521666296059

theorem tailTrace_278526 : CollatzResearch.WordTrace tailWord_278526 prefixEnd_278526 95345141849521666296059 := by
  unfold tailWord_278526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269834723619418162348929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6772451859303563532527621 1269834723619418162348929)
  ·
    refine ⟨952376042714563621761697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269834723619418162348929 952376042714563621761697)
    ·
      refine ⟨714282032035922716321273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 952376042714563621761697 714282032035922716321273)
      ·
        refine ⟨535711524026942037240955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714282032035922716321273 535711524026942037240955)
        ·
          refine ⟨803567286040413055861433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535711524026942037240955 803567286040413055861433)
          ·
            refine ⟨602675464530309791896075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803567286040413055861433 602675464530309791896075)
            ·
              refine ⟨904013196795464687844113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602675464530309791896075 904013196795464687844113)
              ·
                refine ⟨678009897596598515883085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904013196795464687844113 678009897596598515883085)
                ·
                  refine ⟨254253711598724443456157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678009897596598515883085 254253711598724443456157)
                  ·
                    refine ⟨95345141849521666296059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254253711598724443456157 95345141849521666296059)
                    ·
                      rfl

theorem cell22_278526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_278526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278526 prefixEnd_278526 := by exact prefixLift 278526
  have htrace : WordTrace (prefixWord ++ tailWord_278526) baseStart_278526 baseEnd_278526 := by
    simpa [prefixWord, tailWord_278526, baseEnd_278526] using wordTrace_append hprefix tailTrace_278526
  have hstable : (prefixWord ++ tailWord_278526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278526).length < 2 ^ (prefixWord ++ tailWord_278526).sum := by decide
  have hdescent : baseEnd_278526 < baseStart_278526 := by decide
  rcases family_descends (prefixWord ++ tailWord_278526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278597 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_278597 : Nat := 118140960795 + 278597 * 2 ^ 59
def prefixEnd_278597 : Nat := 4983230072969 + 3 ^ 40 * 278597 * 2
def baseEnd_278597 : Nat := 95369446600501147770841

theorem tailTrace_278597 : CollatzResearch.WordTrace tailWord_278597 prefixEnd_278597 95369446600501147770841 := by
  unfold tailWord_278597
  simp only [CollatzResearch.WordTrace]
  refine ⟨10161267371698124424626045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6774178247798749616417363 10161267371698124424626045)
  ·
    refine ⟨3810475264386796659234767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10161267371698124424626045 3810475264386796659234767)
    ·
      refine ⟨5715712896580194988852151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810475264386796659234767 5715712896580194988852151)
      ·
        refine ⟨8573569344870292483278227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715712896580194988852151 8573569344870292483278227)
        ·
          refine ⟨12860354017305438724917341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573569344870292483278227 12860354017305438724917341)
          ·
            refine ⟨4822632756489539521844003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12860354017305438724917341 4822632756489539521844003)
            ·
              refine ⟨7233949134734309282766005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822632756489539521844003 7233949134734309282766005)
              ·
                refine ⟨678182731381341495259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7233949134734309282766005 678182731381341495259313)
                ·
                  refine ⟨508637048536006121444485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678182731381341495259313 508637048536006121444485)
                  ·
                    refine ⟨95369446600501147770841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 508637048536006121444485 95369446600501147770841)
                    ·
                      rfl

theorem cell22_278597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_278597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278597 prefixEnd_278597 := by exact prefixLift 278597
  have htrace : WordTrace (prefixWord ++ tailWord_278597) baseStart_278597 baseEnd_278597 := by
    simpa [prefixWord, tailWord_278597, baseEnd_278597] using wordTrace_append hprefix tailTrace_278597
  have hstable : (prefixWord ++ tailWord_278597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278597).length < 2 ^ (prefixWord ++ tailWord_278597).sum := by decide
  have hdescent : baseEnd_278597 < baseStart_278597 := by decide
  rcases family_descends (prefixWord ++ tailWord_278597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278672 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_278672 : Nat := 118140960795 + 278672 * 2 ^ 59
def prefixEnd_278672 : Nat := 4983230072969 + 3 ^ 40 * 278672 * 2
def baseEnd_278672 : Nat := 95395120633225952145611

theorem tailTrace_278672 : CollatzResearch.WordTrace tailWord_278672 prefixEnd_278672 95395120633225952145611 := by
  unfold tailWord_278672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082001423213206116803135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6776001897617608155737513 5082001423213206116803135)
  ·
    refine ⟨7623002134819809175204703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082001423213206116803135 7623002134819809175204703)
    ·
      refine ⟨11434503202229713762807055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623002134819809175204703 11434503202229713762807055)
      ·
        refine ⟨17151754803344570644210583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434503202229713762807055 17151754803344570644210583)
        ·
          refine ⟨25727632205016855966315875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17151754803344570644210583 25727632205016855966315875)
          ·
            refine ⟨38591448307525283949473813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25727632205016855966315875 38591448307525283949473813)
            ·
              refine ⟨1808974139415247685131585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38591448307525283949473813 1808974139415247685131585)
              ·
                refine ⟨1356730604561435763848689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808974139415247685131585 1356730604561435763848689)
                ·
                  refine ⟨1017547953421076822886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356730604561435763848689 1017547953421076822886517)
                  ·
                    refine ⟨95395120633225952145611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1017547953421076822886517 95395120633225952145611)
                    ·
                      rfl

theorem cell22_278672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_278672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278672 prefixEnd_278672 := by exact prefixLift 278672
  have htrace : WordTrace (prefixWord ++ tailWord_278672) baseStart_278672 baseEnd_278672 := by
    simpa [prefixWord, tailWord_278672, baseEnd_278672] using wordTrace_append hprefix tailTrace_278672
  have hstable : (prefixWord ++ tailWord_278672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278672).length < 2 ^ (prefixWord ++ tailWord_278672).sum := by decide
  have hdescent : baseEnd_278672 < baseStart_278672 := by decide
  rcases family_descends (prefixWord ++ tailWord_278672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278689 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_278689 : Nat := 118140960795 + 278689 * 2 ^ 59
def prefixEnd_278689 : Nat := 4983230072969 + 3 ^ 40 * 278689 * 2
def baseEnd_278689 : Nat := 95400940080643574470559

theorem tailTrace_278689 : CollatzResearch.WordTrace tailWord_278689 prefixEnd_278689 95400940080643574470559 := by
  unfold tailWord_278689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164622887364824136975121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6776415258243216091316747 10164622887364824136975121)
  ·
    refine ⟨7623467165523618102731341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10164622887364824136975121 7623467165523618102731341)
    ·
      refine ⟨2858800187071356788524253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7623467165523618102731341 2858800187071356788524253)
      ·
        refine ⟨1072050070151758795696595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2858800187071356788524253 1072050070151758795696595)
        ·
          refine ⟨1608075105227638193544893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072050070151758795696595 1608075105227638193544893)
          ·
            refine ⟨603028164460364322579335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1608075105227638193544893 603028164460364322579335)
            ·
              refine ⟨904542246690546483869003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603028164460364322579335 904542246690546483869003)
              ·
                refine ⟨1356813370035819725803505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904542246690546483869003 1356813370035819725803505)
                ·
                  refine ⟨1017610027526864794352629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356813370035819725803505 1017610027526864794352629)
                  ·
                    refine ⟨95400940080643574470559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1017610027526864794352629 95400940080643574470559)
                    ·
                      rfl

theorem cell22_278689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_278689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278689 prefixEnd_278689 := by exact prefixLift 278689
  have htrace : WordTrace (prefixWord ++ tailWord_278689) baseStart_278689 baseEnd_278689 := by
    simpa [prefixWord, tailWord_278689, baseEnd_278689] using wordTrace_append hprefix tailTrace_278689
  have hstable : (prefixWord ++ tailWord_278689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278689).length < 2 ^ (prefixWord ++ tailWord_278689).sum := by decide
  have hdescent : baseEnd_278689 < baseStart_278689 := by decide
  rcases family_descends (prefixWord ++ tailWord_278689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278888 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_278888 : Nat := 118140960795 + 278888 * 2 ^ 59
def prefixEnd_278888 : Nat := 4983230072969 + 3 ^ 40 * 278888 * 2
def baseEnd_278888 : Nat := 31823020615824462914983

theorem tailTrace_278888 : CollatzResearch.WordTrace tailWord_278888 prefixEnd_278888 31823020615824462914983 := by
  unfold tailWord_278888
  simp only [CollatzResearch.WordTrace]
  refine ⟨5085940506821940561734659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6781254009095920748979545 5085940506821940561734659)
  ·
    refine ⟨7628910760232910842601989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5085940506821940561734659 7628910760232910842601989)
    ·
      refine ⟨1430420767543670782987873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7628910760232910842601989 1430420767543670782987873)
      ·
        refine ⟨1072815575657753087240905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430420767543670782987873 1072815575657753087240905)
        ·
          refine ⟨804611681743314815430679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072815575657753087240905 804611681743314815430679)
          ·
            refine ⟨1206917522614972223146019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804611681743314815430679 1206917522614972223146019)
            ·
              refine ⟨1810376283922458334719029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206917522614972223146019 1810376283922458334719029)
              ·
                refine ⟨169722776617730468879909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1810376283922458334719029 169722776617730468879909)
                ·
                  refine ⟨31823020615824462914983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169722776617730468879909 31823020615824462914983)
                  ·
                    rfl

theorem cell22_278888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_278888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278888 prefixEnd_278888 := by exact prefixLift 278888
  have htrace : WordTrace (prefixWord ++ tailWord_278888) baseStart_278888 baseEnd_278888 := by
    simpa [prefixWord, tailWord_278888, baseEnd_278888] using wordTrace_append hprefix tailTrace_278888
  have hstable : (prefixWord ++ tailWord_278888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278888).length < 2 ^ (prefixWord ++ tailWord_278888).sum := by decide
  have hdescent : baseEnd_278888 < baseStart_278888 := by decide
  rcases family_descends (prefixWord ++ tailWord_278888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278890 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_278890 : Nat := 118140960795 + 278890 * 2 ^ 59
def prefixEnd_278890 : Nat := 4983230072969 + 3 ^ 40 * 278890 * 2
def baseEnd_278890 : Nat := 95469746488346050194943

theorem tailTrace_278890 : CollatzResearch.WordTrace tailWord_278890 prefixEnd_278890 95469746488346050194943 := by
  unfold tailWord_278890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542988489909158866260531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6781302639757756976694749 2542988489909158866260531)
  ·
    refine ⟨3814482734863738299390797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2542988489909158866260531 3814482734863738299390797)
    ·
      refine ⟨1430431025573901862271549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3814482734863738299390797 1430431025573901862271549)
      ·
        refine ⟨536411634590213198351831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1430431025573901862271549 536411634590213198351831)
        ·
          refine ⟨804617451885319797527747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536411634590213198351831 804617451885319797527747)
          ·
            refine ⟨1206926177827979696291621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804617451885319797527747 1206926177827979696291621)
            ·
              refine ⟨226298658342746193054679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1206926177827979696291621 226298658342746193054679)
              ·
                refine ⟨339447987514119289582019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226298658342746193054679 339447987514119289582019)
                ·
                  refine ⟨509171981271178934373029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339447987514119289582019 509171981271178934373029)
                  ·
                    refine ⟨95469746488346050194943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 509171981271178934373029 95469746488346050194943)
                    ·
                      rfl

theorem cell22_278890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_278890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278890 prefixEnd_278890 := by exact prefixLift 278890
  have htrace : WordTrace (prefixWord ++ tailWord_278890) baseStart_278890 baseEnd_278890 := by
    simpa [prefixWord, tailWord_278890, baseEnd_278890] using wordTrace_append hprefix tailTrace_278890
  have hstable : (prefixWord ++ tailWord_278890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278890).length < 2 ^ (prefixWord ++ tailWord_278890).sum := by decide
  have hdescent : baseEnd_278890 < baseStart_278890 := by decide
  rcases family_descends (prefixWord ++ tailWord_278890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278920 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_278920 : Nat := 118140960795 + 278920 * 2 ^ 59
def prefixEnd_278920 : Nat := 4983230072969 + 3 ^ 40 * 278920 * 2
def baseEnd_278920 : Nat := 95480016101435971944851

theorem tailTrace_278920 : CollatzResearch.WordTrace tailWord_278920 prefixEnd_278920 95480016101435971944851 := by
  unfold tailWord_278920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086524074763975294317107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6782032099685300392422809 5086524074763975294317107)
  ·
    refine ⟨7629786112145962941475661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5086524074763975294317107 7629786112145962941475661)
    ·
      refine ⟨2861169792054736103053373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7629786112145962941475661 2861169792054736103053373)
      ·
        refine ⟨1072938672020526038645015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2861169792054736103053373 1072938672020526038645015)
        ·
          refine ⟨1609408008030789057967523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072938672020526038645015 1609408008030789057967523)
          ·
            refine ⟨2414112012046183586951285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609408008030789057967523 2414112012046183586951285)
            ·
              refine ⟨226323001129329711276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2414112012046183586951285 226323001129329711276683)
              ·
                refine ⟨339484501693994566915025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226323001129329711276683 339484501693994566915025)
                ·
                  refine ⟨254613376270495925186269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339484501693994566915025 254613376270495925186269)
                  ·
                    refine ⟨95480016101435971944851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254613376270495925186269 95480016101435971944851)
                    ·
                      rfl

theorem cell22_278920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_278920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278920 prefixEnd_278920 := by exact prefixLift 278920
  have htrace : WordTrace (prefixWord ++ tailWord_278920) baseStart_278920 baseEnd_278920 := by
    simpa [prefixWord, tailWord_278920, baseEnd_278920] using wordTrace_append hprefix tailTrace_278920
  have hstable : (prefixWord ++ tailWord_278920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278920).length < 2 ^ (prefixWord ++ tailWord_278920).sum := by decide
  have hdescent : baseEnd_278920 < baseStart_278920 := by decide
  rcases family_descends (prefixWord ++ tailWord_278920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278961 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 7]
def baseStart_278961 : Nat := 118140960795 + 278961 * 2 ^ 59
def prefixEnd_278961 : Nat := 4983230072969 + 3 ^ 40 * 278961 * 2
def baseEnd_278961 : Nat := 31831350413108510556575

theorem tailTrace_278961 : CollatzResearch.WordTrace tailWord_278961 prefixEnd_278961 31831350413108510556575 := by
  unfold tailWord_278961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174543542379414590876737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6783029028252943060584491 10174543542379414590876737)
  ·
    refine ⟨7630907656784560943157553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10174543542379414590876737 7630907656784560943157553)
    ·
      refine ⟨5723180742588420707368165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7630907656784560943157553 5723180742588420707368165)
      ·
        refine ⟨1073096389235328882631531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5723180742588420707368165 1073096389235328882631531)
        ·
          refine ⟨1609644583852993323947297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073096389235328882631531 1609644583852993323947297)
          ·
            refine ⟨1207233437889744992960473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609644583852993323947297 1207233437889744992960473)
            ·
              refine ⟨905425078417308744720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207233437889744992960473 905425078417308744720355)
              ·
                refine ⟨1358137617625963117080533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905425078417308744720355 1358137617625963117080533)
                ·
                  refine ⟨31831350413108510556575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1358137617625963117080533 31831350413108510556575)
                  ·
                    rfl

theorem cell22_278961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_278961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_278961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_278961 prefixEnd_278961 := by exact prefixLift 278961
  have htrace : WordTrace (prefixWord ++ tailWord_278961) baseStart_278961 baseEnd_278961 := by
    simpa [prefixWord, tailWord_278961, baseEnd_278961] using wordTrace_append hprefix tailTrace_278961
  have hstable : (prefixWord ++ tailWord_278961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278961).length < 2 ^ (prefixWord ++ tailWord_278961).sum := by decide
  have hdescent : baseEnd_278961 < baseStart_278961 := by decide
  rcases family_descends (prefixWord ++ tailWord_278961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279036 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_279036 : Nat := 118140960795 + 279036 * 2 ^ 59
def prefixEnd_279036 : Nat := 4983230072969 + 3 ^ 40 * 279036 * 2
def baseEnd_279036 : Nat := 95519725272050336044495

theorem tailTrace_279036 : CollatzResearch.WordTrace tailWord_279036 prefixEnd_279036 95519725272050336044495 := by
  unfold tailWord_279036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088639508553851199928481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6784852678071801599904641 5088639508553851199928481)
  ·
    refine ⟨3816479631415388399946361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5088639508553851199928481 3816479631415388399946361)
    ·
      refine ⟨2862359723561541299959771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3816479631415388399946361 2862359723561541299959771)
      ·
        refine ⟨4293539585342311949939657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862359723561541299959771 4293539585342311949939657)
        ·
          refine ⟨3220154689006733962454743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4293539585342311949939657 3220154689006733962454743)
          ·
            refine ⟨4830232033510100943682115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220154689006733962454743 4830232033510100943682115)
            ·
              refine ⟨7245348050265151415523173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830232033510100943682115 7245348050265151415523173)
              ·
                refine ⟨1358502759424715890410595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7245348050265151415523173 1358502759424715890410595)
                ·
                  refine ⟨2037754139137073835615893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358502759424715890410595 2037754139137073835615893)
                  ·
                    refine ⟨95519725272050336044495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2037754139137073835615893 95519725272050336044495)
                    ·
                      rfl

theorem cell22_279036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_279036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279036 prefixEnd_279036 := by exact prefixLift 279036
  have htrace : WordTrace (prefixWord ++ tailWord_279036) baseStart_279036 baseEnd_279036 := by
    simpa [prefixWord, tailWord_279036, baseEnd_279036] using wordTrace_append hprefix tailTrace_279036
  have hstable : (prefixWord ++ tailWord_279036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279036).length < 2 ^ (prefixWord ++ tailWord_279036).sum := by decide
  have hdescent : baseEnd_279036 < baseStart_279036 := by decide
  rcases family_descends (prefixWord ++ tailWord_279036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279100 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_279100 : Nat := 118140960795 + 279100 * 2 ^ 59
def prefixEnd_279100 : Nat := 4983230072969 + 3 ^ 40 * 279100 * 2
def baseEnd_279100 : Nat := 95541633779975502444299

theorem tailTrace_279100 : CollatzResearch.WordTrace tailWord_279100 prefixEnd_279100 95541633779975502444299 := by
  unfold tailWord_279100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089806644437920665093377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6786408859250560886791169 5089806644437920665093377)
  ·
    refine ⟨3817354983328440498820033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5089806644437920665093377 3817354983328440498820033)
    ·
      refine ⟨2863016237496330374115025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3817354983328440498820033 2863016237496330374115025)
      ·
        refine ⟨2147262178122247780586269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2863016237496330374115025 2147262178122247780586269)
        ·
          refine ⟨805223316795842917719851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2147262178122247780586269 805223316795842917719851)
          ·
            refine ⟨1207834975193764376579777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805223316795842917719851 1207834975193764376579777)
            ·
              refine ⟨905876231395323282434833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207834975193764376579777 905876231395323282434833)
              ·
                refine ⟨679407173546492461826125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905876231395323282434833 679407173546492461826125)
                ·
                  refine ⟨254777690079934673184797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679407173546492461826125 254777690079934673184797)
                  ·
                    refine ⟨95541633779975502444299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254777690079934673184797 95541633779975502444299)
                    ·
                      rfl

theorem cell22_279100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_279100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279100 prefixEnd_279100 := by exact prefixLift 279100
  have htrace : WordTrace (prefixWord ++ tailWord_279100) baseStart_279100 baseEnd_279100 := by
    simpa [prefixWord, tailWord_279100, baseEnd_279100] using wordTrace_append hprefix tailTrace_279100
  have hstable : (prefixWord ++ tailWord_279100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279100).length < 2 ^ (prefixWord ++ tailWord_279100).sum := by decide
  have hdescent : baseEnd_279100 < baseStart_279100 := by decide
  rcases family_descends (prefixWord ++ tailWord_279100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279108 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_279108 : Nat := 118140960795 + 279108 * 2 ^ 59
def prefixEnd_279108 : Nat := 4983230072969 + 3 ^ 40 * 279108 * 2
def baseEnd_279108 : Nat := 31848124114488716081425

theorem tailTrace_279108 : CollatzResearch.WordTrace tailWord_279108 prefixEnd_279108 31848124114488716081425 := by
  unfold tailWord_279108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089952536423429348238989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6786603381897905797651985 5089952536423429348238989)
  ·
    refine ⟨1908732201158786005589621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5089952536423429348238989 1908732201158786005589621)
    ·
      refine ⟨178943643858636188024027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1908732201158786005589621 178943643858636188024027)
      ·
        refine ⟨268415465787954282036041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178943643858636188024027 268415465787954282036041)
        ·
          refine ⟨201311599340965711527031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268415465787954282036041 201311599340965711527031)
          ·
            refine ⟨301967399011448567290547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201311599340965711527031 301967399011448567290547)
            ·
              refine ⟨452951098517172850935821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301967399011448567290547 452951098517172850935821)
              ·
                refine ⟨169856661943939819100933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452951098517172850935821 169856661943939819100933)
                ·
                  refine ⟨31848124114488716081425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169856661943939819100933 31848124114488716081425)
                  ·
                    rfl

theorem cell22_279108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_279108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279108 prefixEnd_279108 := by exact prefixLift 279108
  have htrace : WordTrace (prefixWord ++ tailWord_279108) baseStart_279108 baseEnd_279108 := by
    simpa [prefixWord, tailWord_279108, baseEnd_279108] using wordTrace_append hprefix tailTrace_279108
  have hstable : (prefixWord ++ tailWord_279108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279108).length < 2 ^ (prefixWord ++ tailWord_279108).sum := by decide
  have hdescent : baseEnd_279108 < baseStart_279108 := by decide
  rcases family_descends (prefixWord ++ tailWord_279108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279143 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_279143 : Nat := 118140960795 + 279143 * 2 ^ 59
def prefixEnd_279143 : Nat := 4983230072969 + 3 ^ 40 * 279143 * 2
def baseEnd_279143 : Nat := 95556353558737723619167

theorem tailTrace_279143 : CollatzResearch.WordTrace tailWord_279143 prefixEnd_279143 95556353558737723619167 := by
  unfold tailWord_279143
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181181627720059674002083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6787454418480039782668055 10181181627720059674002083)
  ·
    refine ⟨15271772441580089511003125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10181181627720059674002083 15271772441580089511003125)
    ·
      refine ⟨1431728666398133391656543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15271772441580089511003125 1431728666398133391656543)
      ·
        refine ⟨2147592999597200087484815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431728666398133391656543 2147592999597200087484815)
        ·
          refine ⟨3221389499395800131227223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147592999597200087484815 3221389499395800131227223)
          ·
            refine ⟨4832084249093700196840835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221389499395800131227223 4832084249093700196840835)
            ·
              refine ⟨7248126373640550295261253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832084249093700196840835 7248126373640550295261253)
              ·
                refine ⟨1359023695057603180361485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7248126373640550295261253 1359023695057603180361485)
                ·
                  refine ⟨509633885646601192635557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1359023695057603180361485 509633885646601192635557)
                  ·
                    refine ⟨95556353558737723619167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 509633885646601192635557 95556353558737723619167)
                    ·
                      rfl

theorem cell22_279143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_279143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279143 prefixEnd_279143 := by exact prefixLift 279143
  have htrace : WordTrace (prefixWord ++ tailWord_279143) baseStart_279143 baseEnd_279143 := by
    simpa [prefixWord, tailWord_279143, baseEnd_279143] using wordTrace_append hprefix tailTrace_279143
  have hstable : (prefixWord ++ tailWord_279143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279143).length < 2 ^ (prefixWord ++ tailWord_279143).sum := by decide
  have hdescent : baseEnd_279143 < baseStart_279143 := by decide
  rcases family_descends (prefixWord ++ tailWord_279143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279173 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_279173 : Nat := 118140960795 + 279173 * 2 ^ 59
def prefixEnd_279173 : Nat := 4983230072969 + 3 ^ 40 * 279173 * 2
def baseEnd_279173 : Nat := 95566623171827645369075

theorem tailTrace_279173 : CollatzResearch.WordTrace tailWord_279173 prefixEnd_279173 95566623171827645369075 := by
  unfold tailWord_279173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182275817611374797594173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6788183878407583198396115 10182275817611374797594173)
  ·
    refine ⟨3818353431604265549097815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10182275817611374797594173 3818353431604265549097815)
    ·
      refine ⟨5727530147406398323646723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818353431604265549097815 5727530147406398323646723)
      ·
        refine ⟨8591295221109597485470085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727530147406398323646723 8591295221109597485470085)
        ·
          refine ⟨1610867853958049528525641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8591295221109597485470085 1610867853958049528525641)
          ·
            refine ⟨1208150890468537146394231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610867853958049528525641 1208150890468537146394231)
            ·
              refine ⟨1812226335702805719591347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208150890468537146394231 1812226335702805719591347)
              ·
                refine ⟨2718339503554208579387021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812226335702805719591347 2718339503554208579387021)
                ·
                  refine ⟨1019377313832828217270133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2718339503554208579387021 1019377313832828217270133)
                  ·
                    refine ⟨95566623171827645369075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1019377313832828217270133 95566623171827645369075)
                    ·
                      rfl

theorem cell22_279173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_279173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279173 prefixEnd_279173 := by exact prefixLift 279173
  have htrace : WordTrace (prefixWord ++ tailWord_279173) baseStart_279173 baseEnd_279173 := by
    simpa [prefixWord, tailWord_279173, baseEnd_279173] using wordTrace_append hprefix tailTrace_279173
  have hstable : (prefixWord ++ tailWord_279173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279173).length < 2 ^ (prefixWord ++ tailWord_279173).sum := by decide
  have hdescent : baseEnd_279173 < baseStart_279173 := by decide
  rcases family_descends (prefixWord ++ tailWord_279173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279175 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 4]
def baseStart_279175 : Nat := 118140960795 + 279175 * 2 ^ 59
def prefixEnd_279175 : Nat := 4983230072969 + 3 ^ 40 * 279175 * 2
def baseEnd_279175 : Nat := 31855769270900102273023

theorem tailTrace_279175 : CollatzResearch.WordTrace tailWord_279175 prefixEnd_279175 31855769270900102273023 := by
  unfold tailWord_279175
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182348763604129139166979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6788232509069419426111319 10182348763604129139166979)
  ·
    refine ⟨15273523145406193708750469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10182348763604129139166979 15273523145406193708750469)
    ·
      refine ⟨2863785589763661320390713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15273523145406193708750469 2863785589763661320390713)
      ·
        refine ⟨2147839192322745990293035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2863785589763661320390713 2147839192322745990293035)
        ·
          refine ⟨3221758788484118985439553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147839192322745990293035 3221758788484118985439553)
          ·
            refine ⟨2416319091363089239079665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221758788484118985439553 2416319091363089239079665)
            ·
              refine ⟨1812239318522316929309749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416319091363089239079665 1812239318522316929309749)
              ·
                refine ⟨169897436111467212122789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1812239318522316929309749 169897436111467212122789)
                ·
                  refine ⟨31855769270900102273023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169897436111467212122789 31855769270900102273023)
                  ·
                    rfl

theorem cell22_279175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 4].length) (baseStart_279175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279175 prefixEnd_279175 := by exact prefixLift 279175
  have htrace : WordTrace (prefixWord ++ tailWord_279175) baseStart_279175 baseEnd_279175 := by
    simpa [prefixWord, tailWord_279175, baseEnd_279175] using wordTrace_append hprefix tailTrace_279175
  have hstable : (prefixWord ++ tailWord_279175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279175).length < 2 ^ (prefixWord ++ tailWord_279175).sum := by decide
  have hdescent : baseEnd_279175 < baseStart_279175 := by decide
  rcases family_descends (prefixWord ++ tailWord_279175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279342 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_279342 : Nat := 118140960795 + 279342 * 2 ^ 59
def prefixEnd_279342 : Nat := 4983230072969 + 3 ^ 40 * 279342 * 2
def baseEnd_279342 : Nat := 95624475325567537893557

theorem tailTrace_279342 : CollatzResearch.WordTrace tailWord_279342 prefixEnd_279342 95624475325567537893557 := by
  unfold tailWord_279342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273554969249889582562035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6792293169332744440330853 1273554969249889582562035)
  ·
    refine ⟨1910332453874834373843053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273554969249889582562035 1910332453874834373843053)
    ·
      refine ⟨716374670203062890191145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1910332453874834373843053 716374670203062890191145)
      ·
        refine ⟨537281002652297167643359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716374670203062890191145 537281002652297167643359)
        ·
          refine ⟨805921503978445751465039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537281002652297167643359 805921503978445751465039)
          ·
            refine ⟨1208882255967668627197559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805921503978445751465039 1208882255967668627197559)
            ·
              refine ⟨1813323383951502940796339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208882255967668627197559 1813323383951502940796339)
              ·
                refine ⟨2719985075927254411194509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813323383951502940796339 2719985075927254411194509)
                ·
                  refine ⟨1019994403472720404197941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2719985075927254411194509 1019994403472720404197941)
                  ·
                    refine ⟨95624475325567537893557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1019994403472720404197941 95624475325567537893557)
                    ·
                      rfl

theorem cell22_279342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_279342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279342 prefixEnd_279342 := by exact prefixLift 279342
  have htrace : WordTrace (prefixWord ++ tailWord_279342) baseStart_279342 baseEnd_279342 := by
    simpa [prefixWord, tailWord_279342, baseEnd_279342] using wordTrace_append hprefix tailTrace_279342
  have hstable : (prefixWord ++ tailWord_279342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279342).length < 2 ^ (prefixWord ++ tailWord_279342).sum := by decide
  have hdescent : baseEnd_279342 < baseStart_279342 := by decide
  rcases family_descends (prefixWord ++ tailWord_279342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279359 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 2, 3]
def baseStart_279359 : Nat := 118140960795 + 279359 * 2 ^ 59
def prefixEnd_279359 : Nat := 4983230072969 + 3 ^ 40 * 279359 * 2
def baseEnd_279359 : Nat := 95630294772985160218505

theorem tailTrace_279359 : CollatzResearch.WordTrace tailWord_279359 prefixEnd_279359 95630294772985160218505 := by
  unfold tailWord_279359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10189059794937528563865131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6792706529958352375910087 10189059794937528563865131)
  ·
    refine ⟨15283589692406292845797697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10189059794937528563865131 15283589692406292845797697)
    ·
      refine ⟨11462692269304719634348273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15283589692406292845797697 11462692269304719634348273)
      ·
        refine ⟨8597019201978539725761205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11462692269304719634348273 8597019201978539725761205)
        ·
          refine ⟨805970550185488099290113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8597019201978539725761205 805970550185488099290113)
          ·
            refine ⟨604477912639116074467585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805970550185488099290113 604477912639116074467585)
            ·
              refine ⟨453358434479337055850689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604477912639116074467585 453358434479337055850689)
              ·
                refine ⟨340018825859502791888017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453358434479337055850689 340018825859502791888017)
                ·
                  refine ⟨255014119394627093916013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340018825859502791888017 255014119394627093916013)
                  ·
                    refine ⟨95630294772985160218505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255014119394627093916013 95630294772985160218505)
                    ·
                      rfl

theorem cell22_279359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_279359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279359 prefixEnd_279359 := by exact prefixLift 279359
  have htrace : WordTrace (prefixWord ++ tailWord_279359) baseStart_279359 baseEnd_279359 := by
    simpa [prefixWord, tailWord_279359, baseEnd_279359] using wordTrace_append hprefix tailTrace_279359
  have hstable : (prefixWord ++ tailWord_279359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279359).length < 2 ^ (prefixWord ++ tailWord_279359).sum := by decide
  have hdescent : baseEnd_279359 < baseStart_279359 := by decide
  rcases family_descends (prefixWord ++ tailWord_279359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279361 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 4]
def baseStart_279361 : Nat := 118140960795 + 279361 * 2 ^ 59
def prefixEnd_279361 : Nat := 4983230072969 + 3 ^ 40 * 279361 * 2
def baseEnd_279361 : Nat := 31876993137952607222833

theorem tailTrace_279361 : CollatzResearch.WordTrace tailWord_279361 prefixEnd_279361 31876993137952607222833 := by
  unfold tailWord_279361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10189132740930282905437937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6792755160620188603625291 10189132740930282905437937)
  ·
    refine ⟨7641849555697712179078453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10189132740930282905437937 7641849555697712179078453)
    ·
      refine ⟨716423395846660516788605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7641849555697712179078453 716423395846660516788605)
      ·
        refine ⟨268658773442497693795727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 716423395846660516788605 268658773442497693795727)
        ·
          refine ⟨402988160163746540693591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268658773442497693795727 402988160163746540693591)
          ·
            refine ⟨604482240245619811040387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402988160163746540693591 604482240245619811040387)
            ·
              refine ⟨906723360368429716560581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604482240245619811040387 906723360368429716560581)
              ·
                refine ⟨170010630069080571855109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 906723360368429716560581 170010630069080571855109)
                ·
                  refine ⟨31876993137952607222833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170010630069080571855109 31876993137952607222833)
                  ·
                    rfl

theorem cell22_279361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_279361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279361 prefixEnd_279361 := by exact prefixLift 279361
  have htrace : WordTrace (prefixWord ++ tailWord_279361) baseStart_279361 baseEnd_279361 := by
    simpa [prefixWord, tailWord_279361, baseEnd_279361] using wordTrace_append hprefix tailTrace_279361
  have hstable : (prefixWord ++ tailWord_279361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279361).length < 2 ^ (prefixWord ++ tailWord_279361).sum := by decide
  have hdescent : baseEnd_279361 < baseStart_279361 := by decide
  rcases family_descends (prefixWord ++ tailWord_279361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279372 : List Nat := [2, 2, 1, 3, 3, 3, 1, 7]
def baseStart_279372 : Nat := 118140960795 + 279372 * 2 ^ 59
def prefixEnd_279372 : Nat := 4983230072969 + 3 ^ 40 * 279372 * 2
def baseEnd_279372 : Nat := 10626082770961939960385

theorem tailTrace_279372 : CollatzResearch.WordTrace tailWord_279372 prefixEnd_279372 10626082770961939960385 := by
  unfold tailWord_279372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094766971945215892044185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6793022629260287856058913 5094766971945215892044185)
  ·
    refine ⟨3821075228958911919033139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5094766971945215892044185 3821075228958911919033139)
    ·
      refine ⟨5731612843438367878549709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821075228958911919033139 5731612843438367878549709)
      ·
        refine ⟨2149354816289387954456141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5731612843438367878549709 2149354816289387954456141)
        ·
          refine ⟨806008056108520482921053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149354816289387954456141 806008056108520482921053)
          ·
            refine ⟨302253021040695181095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806008056108520482921053 302253021040695181095395)
            ·
              refine ⟨453379531561042771643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302253021040695181095395 453379531561042771643093)
              ·
                refine ⟨10626082770961939960385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 453379531561042771643093 10626082770961939960385)
                ·
                  rfl

theorem cell22_279372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_279372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279372 prefixEnd_279372 := by exact prefixLift 279372
  have htrace : WordTrace (prefixWord ++ tailWord_279372) baseStart_279372 baseEnd_279372 := by
    simpa [prefixWord, tailWord_279372, baseEnd_279372] using wordTrace_append hprefix tailTrace_279372
  have hstable : (prefixWord ++ tailWord_279372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279372).length < 2 ^ (prefixWord ++ tailWord_279372).sum := by decide
  have hdescent : baseEnd_279372 < baseStart_279372 := by decide
  rcases family_descends (prefixWord ++ tailWord_279372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279417 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 5]
def baseStart_279417 : Nat := 118140960795 + 279417 * 2 ^ 59
def prefixEnd_279417 : Nat := 4983230072969 + 3 ^ 40 * 279417 * 2
def baseEnd_279417 : Nat := 31883383119430780756109

theorem tailTrace_279417 : CollatzResearch.WordTrace tailWord_279417 prefixEnd_279417 31883383119430780756109 := by
  unfold tailWord_279417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191175228727404469476505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6794116819151602979651003 10191175228727404469476505)
  ·
    refine ⟨7643381421545553352107379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10191175228727404469476505 7643381421545553352107379)
    ·
      refine ⟨11465072132318330028161069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7643381421545553352107379 11465072132318330028161069)
      ·
        refine ⟨4299402049619373760560401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11465072132318330028161069 4299402049619373760560401)
        ·
          refine ⟨3224551537214530320420301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299402049619373760560401 3224551537214530320420301)
          ·
            refine ⟨1209206826455448870157613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3224551537214530320420301 1209206826455448870157613)
            ·
              refine ⟨453452559920793326309105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209206826455448870157613 453452559920793326309105)
              ·
                refine ⟨340089419940594994731829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453452559920793326309105 340089419940594994731829)
                ·
                  refine ⟨31883383119430780756109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340089419940594994731829 31883383119430780756109)
                  ·
                    rfl

theorem cell22_279417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_279417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279417 prefixEnd_279417 := by exact prefixLift 279417
  have htrace : WordTrace (prefixWord ++ tailWord_279417) baseStart_279417 baseEnd_279417 := by
    simpa [prefixWord, tailWord_279417, baseEnd_279417] using wordTrace_append hprefix tailTrace_279417
  have hstable : (prefixWord ++ tailWord_279417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279417).length < 2 ^ (prefixWord ++ tailWord_279417).sum := by decide
  have hdescent : baseEnd_279417 < baseStart_279417 := by decide
  rcases family_descends (prefixWord ++ tailWord_279417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279432 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_279432 : Nat := 118140960795 + 279432 * 2 ^ 59
def prefixEnd_279432 : Nat := 4983230072969 + 3 ^ 40 * 279432 * 2
def baseEnd_279432 : Nat := 95655284164837303143281

theorem tailTrace_279432 : CollatzResearch.WordTrace tailWord_279432 prefixEnd_279432 95655284164837303143281 := by
  unfold tailWord_279432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095861161836531015636275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6794481549115374687515033 5095861161836531015636275)
  ·
    refine ⟨7643791742754796523454413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5095861161836531015636275 7643791742754796523454413)
    ·
      refine ⟨2866421903533048696295405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7643791742754796523454413 2866421903533048696295405)
      ·
        refine ⟨1074908213824893261110777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2866421903533048696295405 1074908213824893261110777)
        ·
          refine ⟨806181160368669945833083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074908213824893261110777 806181160368669945833083)
          ·
            refine ⟨1209271740553004918749625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806181160368669945833083 1209271740553004918749625)
            ·
              refine ⟨906953805414753689062219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209271740553004918749625 906953805414753689062219)
              ·
                refine ⟨1360430708122130533593329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906953805414753689062219 1360430708122130533593329)
                ·
                  refine ⟨1020323031091597900194997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360430708122130533593329 1020323031091597900194997)
                  ·
                    refine ⟨95655284164837303143281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1020323031091597900194997 95655284164837303143281)
                    ·
                      rfl

theorem cell22_279432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_279432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279432 prefixEnd_279432 := by exact prefixLift 279432
  have htrace : WordTrace (prefixWord ++ tailWord_279432) baseStart_279432 baseEnd_279432 := by
    simpa [prefixWord, tailWord_279432, baseEnd_279432] using wordTrace_append hprefix tailTrace_279432
  have hstable : (prefixWord ++ tailWord_279432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279432).length < 2 ^ (prefixWord ++ tailWord_279432).sum := by decide
  have hdescent : baseEnd_279432 < baseStart_279432 := by decide
  rcases family_descends (prefixWord ++ tailWord_279432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279475 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_279475 : Nat := 118140960795 + 279475 * 2 ^ 59
def prefixEnd_279475 : Nat := 4983230072969 + 3 ^ 40 * 279475 * 2
def baseEnd_279475 : Nat := 95670003943599524318149

theorem tailTrace_279475 : CollatzResearch.WordTrace tailWord_279475 prefixEnd_279475 95670003943599524318149 := by
  unfold tailWord_279475
  simp only [CollatzResearch.WordTrace]
  refine ⟨10193290662517280375087879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6795527108344853583391919 10193290662517280375087879)
  ·
    refine ⟨15289935993775920562631819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10193290662517280375087879 15289935993775920562631819)
    ·
      refine ⟨22934903990663880843947729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15289935993775920562631819 22934903990663880843947729)
      ·
        refine ⟨17201177992997910632960797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22934903990663880843947729 17201177992997910632960797)
        ·
          refine ⟨6450441747374216487360299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17201177992997910632960797 6450441747374216487360299)
          ·
            refine ⟨9675662621061324731040449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450441747374216487360299 9675662621061324731040449)
            ·
              refine ⟨7256746965795993548280337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9675662621061324731040449 7256746965795993548280337)
              ·
                refine ⟨5442560224346995161210253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7256746965795993548280337 5442560224346995161210253)
                ·
                  refine ⟨2040960084130123185453845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442560224346995161210253 2040960084130123185453845)
                  ·
                    refine ⟨95670003943599524318149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2040960084130123185453845 95670003943599524318149)
                    ·
                      rfl

theorem cell22_279475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_279475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279475 prefixEnd_279475 := by exact prefixLift 279475
  have htrace : WordTrace (prefixWord ++ tailWord_279475) baseStart_279475 baseEnd_279475 := by
    simpa [prefixWord, tailWord_279475, baseEnd_279475] using wordTrace_append hprefix tailTrace_279475
  have hstable : (prefixWord ++ tailWord_279475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279475).length < 2 ^ (prefixWord ++ tailWord_279475).sum := by decide
  have hdescent : baseEnd_279475 < baseStart_279475 := by decide
  rcases family_descends (prefixWord ++ tailWord_279475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279537 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_279537 : Nat := 118140960795 + 279537 * 2 ^ 59
def prefixEnd_279537 : Nat := 4983230072969 + 3 ^ 40 * 279537 * 2
def baseEnd_279537 : Nat := 95691227810652029267959

theorem tailTrace_279537 : CollatzResearch.WordTrace tailWord_279537 prefixEnd_279537 95691227810652029267959 := by
  unfold tailWord_279537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195551988292664963844865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6797034658861776642563243 10195551988292664963844865)
  ·
    refine ⟨7646663991219498722883649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10195551988292664963844865 7646663991219498722883649)
    ·
      refine ⟨5734997993414624042162737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7646663991219498722883649 5734997993414624042162737)
      ·
        refine ⟨4301248495060968031622053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5734997993414624042162737 4301248495060968031622053)
        ·
          refine ⟨806484092823931505929135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4301248495060968031622053 806484092823931505929135)
          ·
            refine ⟨1209726139235897258893703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806484092823931505929135 1209726139235897258893703)
            ·
              refine ⟨1814589208853845888340555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209726139235897258893703 1814589208853845888340555)
              ·
                refine ⟨2721883813280768832510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814589208853845888340555 2721883813280768832510833)
                ·
                  refine ⟨2041412859960576624383125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721883813280768832510833 2041412859960576624383125)
                  ·
                    refine ⟨95691227810652029267959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2041412859960576624383125 95691227810652029267959)
                    ·
                      rfl

theorem cell22_279537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_279537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279537 prefixEnd_279537 := by exact prefixLift 279537
  have htrace : WordTrace (prefixWord ++ tailWord_279537) baseStart_279537 baseEnd_279537 := by
    simpa [prefixWord, tailWord_279537, baseEnd_279537] using wordTrace_append hprefix tailTrace_279537
  have hstable : (prefixWord ++ tailWord_279537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279537).length < 2 ^ (prefixWord ++ tailWord_279537).sum := by decide
  have hdescent : baseEnd_279537 < baseStart_279537 := by decide
  rcases family_descends (prefixWord ++ tailWord_279537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279573 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_279573 : Nat := 118140960795 + 279573 * 2 ^ 59
def prefixEnd_279573 : Nat := 4983230072969 + 3 ^ 40 * 279573 * 2
def baseEnd_279573 : Nat := 95703551346359935367849

theorem tailTrace_279573 : CollatzResearch.WordTrace tailWord_279573 prefixEnd_279573 95703551346359935367849 := by
  unfold tailWord_279573
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196865016162243112155373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6797910010774828741436915 10196865016162243112155373)
  ·
    refine ⟨3823824381060841167058265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10196865016162243112155373 3823824381060841167058265)
    ·
      refine ⟨2867868285795630875293699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3823824381060841167058265 2867868285795630875293699)
      ·
        refine ⟨4301802428693446312940549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867868285795630875293699 4301802428693446312940549)
        ·
          refine ⟨806587955380021183676353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4301802428693446312940549 806587955380021183676353)
          ·
            refine ⟨604940966535015887757265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806587955380021183676353 604940966535015887757265)
            ·
              refine ⟨453705724901261915817949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604940966535015887757265 453705724901261915817949)
              ·
                refine ⟨170139646837973218431731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453705724901261915817949 170139646837973218431731)
                ·
                  refine ⟨255209470256959827647597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170139646837973218431731 255209470256959827647597)
                  ·
                    refine ⟨95703551346359935367849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255209470256959827647597 95703551346359935367849)
                    ·
                      rfl

theorem cell22_279573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_279573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279573 prefixEnd_279573 := by exact prefixLift 279573
  have htrace : WordTrace (prefixWord ++ tailWord_279573) baseStart_279573 baseEnd_279573 := by
    simpa [prefixWord, tailWord_279573, baseEnd_279573] using wordTrace_append hprefix tailTrace_279573
  have hstable : (prefixWord ++ tailWord_279573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279573).length < 2 ^ (prefixWord ++ tailWord_279573).sum := by decide
  have hdescent : baseEnd_279573 < baseStart_279573 := by decide
  rcases family_descends (prefixWord ++ tailWord_279573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279586 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_279586 : Nat := 118140960795 + 279586 * 2 ^ 59
def prefixEnd_279586 : Nat := 4983230072969 + 3 ^ 40 * 279586 * 2
def baseEnd_279586 : Nat := 31902667170677411597603

theorem tailTrace_279586 : CollatzResearch.WordTrace tailWord_279586 prefixEnd_279586 31902667170677411597603 := by
  unfold tailWord_279586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549334791278786583094653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6798226110076764221585741 2549334791278786583094653)
  ·
    refine ⟨956000546729544968660495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2549334791278786583094653 956000546729544968660495)
    ·
      refine ⟨1434000820094317452990743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956000546729544968660495 1434000820094317452990743)
      ·
        refine ⟨2151001230141476179486115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434000820094317452990743 2151001230141476179486115)
        ·
          refine ⟨3226501845212214269229173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151001230141476179486115 3226501845212214269229173)
          ·
            refine ⟨302484547988645087740235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3226501845212214269229173 302484547988645087740235)
            ·
              refine ⟨453726821982967631610353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302484547988645087740235 453726821982967631610353)
              ·
                refine ⟨340295116487225723707765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453726821982967631610353 340295116487225723707765)
                ·
                  refine ⟨31902667170677411597603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340295116487225723707765 31902667170677411597603)
                  ·
                    rfl

theorem cell22_279586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_279586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279586 prefixEnd_279586 := by exact prefixLift 279586
  have htrace : WordTrace (prefixWord ++ tailWord_279586) baseStart_279586 baseEnd_279586 := by
    simpa [prefixWord, tailWord_279586, baseEnd_279586] using wordTrace_append hprefix tailTrace_279586
  have hstable : (prefixWord ++ tailWord_279586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279586).length < 2 ^ (prefixWord ++ tailWord_279586).sum := by decide
  have hdescent : baseEnd_279586 < baseStart_279586 := by decide
  rcases family_descends (prefixWord ++ tailWord_279586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279873 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 5]
def baseStart_279873 : Nat := 118140960795 + 279873 * 2 ^ 59
def prefixEnd_279873 : Nat := 4983230072969 + 3 ^ 40 * 279873 * 2
def baseEnd_279873 : Nat := 31935415825753050955643

theorem tailTrace_279873 : CollatzResearch.WordTrace tailWord_279873 prefixEnd_279873 31935415825753050955643 := by
  unfold tailWord_279873
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207806915075394348076273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6805204610050262898717515 10207806915075394348076273)
  ·
    refine ⟨7655855186306545761057205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10207806915075394348076273 7655855186306545761057205)
    ·
      refine ⟨717736423716238665099113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7655855186306545761057205 717736423716238665099113)
      ·
        refine ⟨538302317787178998824335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717736423716238665099113 538302317787178998824335)
        ·
          refine ⟨807453476680768498236503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538302317787178998824335 807453476680768498236503)
          ·
            refine ⟨1211180215021152747354755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807453476680768498236503 1211180215021152747354755)
            ·
              refine ⟨1816770322531729121032133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211180215021152747354755 1816770322531729121032133)
              ·
                refine ⟨340644435474699210193525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1816770322531729121032133 340644435474699210193525)
                ·
                  refine ⟨31935415825753050955643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340644435474699210193525 31935415825753050955643)
                  ·
                    rfl

theorem cell22_279873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_279873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279873 prefixEnd_279873 := by exact prefixLift 279873
  have htrace : WordTrace (prefixWord ++ tailWord_279873) baseStart_279873 baseEnd_279873 := by
    simpa [prefixWord, tailWord_279873, baseEnd_279873] using wordTrace_append hprefix tailTrace_279873
  have hstable : (prefixWord ++ tailWord_279873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279873).length < 2 ^ (prefixWord ++ tailWord_279873).sum := by decide
  have hdescent : baseEnd_279873 < baseStart_279873 := by decide
  rcases family_descends (prefixWord ++ tailWord_279873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279886 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_279886 : Nat := 118140960795 + 279886 * 2 ^ 59
def prefixEnd_279886 : Nat := 4983230072969 + 3 ^ 40 * 279886 * 2
def baseEnd_279886 : Nat := 95810697642931452291889

theorem tailTrace_279886 : CollatzResearch.WordTrace tailWord_279886 prefixEnd_279886 95810697642931452291889 := by
  unfold tailWord_279886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276035133003537196037439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6805520709352198378866341 1276035133003537196037439)
  ·
    refine ⟨1914052699505305794056159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276035133003537196037439 1914052699505305794056159)
    ·
      refine ⟨2871079049257958691084239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914052699505305794056159 2871079049257958691084239)
      ·
        refine ⟨4306618573886938036626359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871079049257958691084239 4306618573886938036626359)
        ·
          refine ⟨6459927860830407054939539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306618573886938036626359 6459927860830407054939539)
          ·
            refine ⟨9689891791245610582409309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6459927860830407054939539 9689891791245610582409309)
            ·
              refine ⟨3633709421717103968403491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9689891791245610582409309 3633709421717103968403491)
              ·
                refine ⟨5450564132575655952605237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633709421717103968403491 5450564132575655952605237)
                ·
                  refine ⟨510990387428967745556741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5450564132575655952605237 510990387428967745556741)
                  ·
                    refine ⟨95810697642931452291889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 510990387428967745556741 95810697642931452291889)
                    ·
                      rfl

theorem cell22_279886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_279886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279886 prefixEnd_279886 := by exact prefixLift 279886
  have htrace : WordTrace (prefixWord ++ tailWord_279886) baseStart_279886 baseEnd_279886 := by
    simpa [prefixWord, tailWord_279886, baseEnd_279886] using wordTrace_append hprefix tailTrace_279886
  have hstable : (prefixWord ++ tailWord_279886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279886).length < 2 ^ (prefixWord ++ tailWord_279886).sum := by decide
  have hdescent : baseEnd_279886 < baseStart_279886 := by decide
  rcases family_descends (prefixWord ++ tailWord_279886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279931 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_279931 : Nat := 118140960795 + 279931 * 2 ^ 59
def prefixEnd_279931 : Nat := 4983230072969 + 3 ^ 40 * 279931 * 2
def baseEnd_279931 : Nat := 95826102062566334916751

theorem tailTrace_279931 : CollatzResearch.WordTrace tailWord_279931 prefixEnd_279931 95826102062566334916751 := by
  unfold tailWord_279931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209922348865270253687647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6806614899243513502458431 10209922348865270253687647)
  ·
    refine ⟨15314883523297905380531471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10209922348865270253687647 15314883523297905380531471)
    ·
      refine ⟨22972325284946858070797207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15314883523297905380531471 22972325284946858070797207)
      ·
        refine ⟨34458487927420287106195811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22972325284946858070797207 34458487927420287106195811)
        ·
          refine ⟨51687731891130430659293717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34458487927420287106195811 51687731891130430659293717)
          ·
            refine ⟨2422862432396738937154393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51687731891130430659293717 2422862432396738937154393)
            ·
              refine ⟨1817146824297554202865795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422862432396738937154393 1817146824297554202865795)
              ·
                refine ⟨2725720236446331304298693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817146824297554202865795 2725720236446331304298693)
                ·
                  refine ⟨511072544333687119556005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2725720236446331304298693 511072544333687119556005)
                  ·
                    refine ⟨95826102062566334916751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511072544333687119556005 95826102062566334916751)
                    ·
                      rfl

theorem cell22_279931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_279931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279931 prefixEnd_279931 := by exact prefixLift 279931
  have htrace : WordTrace (prefixWord ++ tailWord_279931) baseStart_279931 baseEnd_279931 := by
    simpa [prefixWord, tailWord_279931, baseEnd_279931] using wordTrace_append hprefix tailTrace_279931
  have hstable : (prefixWord ++ tailWord_279931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279931).length < 2 ^ (prefixWord ++ tailWord_279931).sum := by decide
  have hdescent : baseEnd_279931 < baseStart_279931 := by decide
  rcases family_descends (prefixWord ++ tailWord_279931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279933 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_279933 : Nat := 118140960795 + 279933 * 2 ^ 59
def prefixEnd_279933 : Nat := 4983230072969 + 3 ^ 40 * 279933 * 2
def baseEnd_279933 : Nat := 95826786703438996366745

theorem tailTrace_279933 : CollatzResearch.WordTrace tailWord_279933 prefixEnd_279933 95826786703438996366745 := by
  unfold tailWord_279933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209995294858024595260453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6806663529905349730173635 10209995294858024595260453)
  ·
    refine ⟨1914374117785879611611335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10209995294858024595260453 1914374117785879611611335)
    ·
      refine ⟨2871561176678819417417003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914374117785879611611335 2871561176678819417417003)
      ·
        refine ⟨4307341765018229126125505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871561176678819417417003 4307341765018229126125505)
        ·
          refine ⟨3230506323763671844594129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4307341765018229126125505 3230506323763671844594129)
          ·
            refine ⟨2422879742822753883445597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3230506323763671844594129 2422879742822753883445597)
            ·
              refine ⟨908579903558532706292099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2422879742822753883445597 908579903558532706292099)
              ·
                refine ⟨1362869855337799059438149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908579903558532706292099 1362869855337799059438149)
                ·
                  refine ⟨255538097875837323644653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362869855337799059438149 255538097875837323644653)
                  ·
                    refine ⟨95826786703438996366745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255538097875837323644653 95826786703438996366745)
                    ·
                      rfl

theorem cell22_279933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_279933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279933 prefixEnd_279933 := by exact prefixLift 279933
  have htrace : WordTrace (prefixWord ++ tailWord_279933) baseStart_279933 baseEnd_279933 := by
    simpa [prefixWord, tailWord_279933, baseEnd_279933] using wordTrace_append hprefix tailTrace_279933
  have hstable : (prefixWord ++ tailWord_279933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279933).length < 2 ^ (prefixWord ++ tailWord_279933).sum := by decide
  have hdescent : baseEnd_279933 < baseStart_279933 := by decide
  rcases family_descends (prefixWord ++ tailWord_279933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279991 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 7]
def baseStart_279991 : Nat := 118140960795 + 279991 * 2 ^ 59
def prefixEnd_279991 : Nat := 4983230072969 + 3 ^ 40 * 279991 * 2
def baseEnd_279991 : Nat := 31948880429582059472189

theorem tailTrace_279991 : CollatzResearch.WordTrace tailWord_279991 prefixEnd_279991 31948880429582059472189 := by
  unfold tailWord_279991
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212110728647900500871827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6808073819098600333914551 10212110728647900500871827)
  ·
    refine ⟨15318166092971850751307741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10212110728647900500871827 15318166092971850751307741)
    ·
      refine ⟨5744312284864444031740403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15318166092971850751307741 5744312284864444031740403)
      ·
        refine ⟨8616468427296666047610605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744312284864444031740403 8616468427296666047610605)
        ·
          refine ⟨3231175660236249767853977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8616468427296666047610605 3231175660236249767853977)
          ·
            refine ⟨2423381745177187325890483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3231175660236249767853977 2423381745177187325890483)
            ·
              refine ⟨3635072617765780988835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423381745177187325890483 3635072617765780988835725)
              ·
                refine ⟨1363152231662167870813397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3635072617765780988835725 1363152231662167870813397)
                ·
                  refine ⟨31948880429582059472189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1363152231662167870813397 31948880429582059472189)
                  ·
                    rfl

theorem cell22_279991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_279991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_279991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_279991 prefixEnd_279991 := by exact prefixLift 279991
  have htrace : WordTrace (prefixWord ++ tailWord_279991) baseStart_279991 baseEnd_279991 := by
    simpa [prefixWord, tailWord_279991, baseEnd_279991] using wordTrace_append hprefix tailTrace_279991
  have hstable : (prefixWord ++ tailWord_279991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279991).length < 2 ^ (prefixWord ++ tailWord_279991).sum := by decide
  have hdescent : baseEnd_279991 < baseStart_279991 := by decide
  rcases family_descends (prefixWord ++ tailWord_279991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280008 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_280008 : Nat := 118140960795 + 280008 * 2 ^ 59
def prefixEnd_280008 : Nat := 4983230072969 + 3 ^ 40 * 280008 * 2
def baseEnd_280008 : Nat := 31950820245387933580505

theorem tailTrace_280008 : CollatzResearch.WordTrace tailWord_280008 prefixEnd_280008 31950820245387933580505 := by
  unfold tailWord_280008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106365384793156202120339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6808487179724208269493785 5106365384793156202120339)
  ·
    refine ⟨7659548077189734303180509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5106365384793156202120339 7659548077189734303180509)
    ·
      refine ⟨2872330528946150363692691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7659548077189734303180509 2872330528946150363692691)
      ·
        refine ⟨4308495793419225545539037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872330528946150363692691 4308495793419225545539037)
        ·
          refine ⟨1615685922532209579577139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4308495793419225545539037 1615685922532209579577139)
          ·
            refine ⟨2423528883798314369365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615685922532209579577139 2423528883798314369365709)
            ·
              refine ⟨908823331424367888512141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2423528883798314369365709 908823331424367888512141)
              ·
                refine ⟨340808749284137958192053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908823331424367888512141 340808749284137958192053)
                ·
                  refine ⟨31950820245387933580505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340808749284137958192053 31950820245387933580505)
                  ·
                    rfl

theorem cell22_280008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_280008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280008 prefixEnd_280008 := by exact prefixLift 280008
  have htrace : WordTrace (prefixWord ++ tailWord_280008) baseStart_280008 baseEnd_280008 := by
    simpa [prefixWord, tailWord_280008, baseEnd_280008] using wordTrace_append hprefix tailTrace_280008
  have hstable : (prefixWord ++ tailWord_280008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280008).length < 2 ^ (prefixWord ++ tailWord_280008).sum := by decide
  have hdescent : baseEnd_280008 < baseStart_280008 := by decide
  rcases family_descends (prefixWord ++ tailWord_280008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280083 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_280083 : Nat := 118140960795 + 280083 * 2 ^ 59
def prefixEnd_280083 : Nat := 4983230072969 + 3 ^ 40 * 280083 * 2
def baseEnd_280083 : Nat := 95878134768888605116285

theorem tailTrace_280083 : CollatzResearch.WordTrace tailWord_280083 prefixEnd_280083 95878134768888605116285 := by
  unfold tailWord_280083
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215466244314600213220903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6810310829543066808813935 10215466244314600213220903)
  ·
    refine ⟨15323199366471900319831355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10215466244314600213220903 15323199366471900319831355)
    ·
      refine ⟨22984799049707850479747033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15323199366471900319831355 22984799049707850479747033)
      ·
        refine ⟨17238599287280887859810275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22984799049707850479747033 17238599287280887859810275)
        ·
          refine ⟨25857898930921331789715413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17238599287280887859810275 25857898930921331789715413)
          ·
            refine ⟨606044506193468713821455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25857898930921331789715413 606044506193468713821455)
            ·
              refine ⟨909066759290203070732183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606044506193468713821455 909066759290203070732183)
              ·
                refine ⟨1363600138935304606098275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909066759290203070732183 1363600138935304606098275)
                ·
                  refine ⟨2045400208402956909147413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363600138935304606098275 2045400208402956909147413)
                  ·
                    refine ⟨95878134768888605116285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2045400208402956909147413 95878134768888605116285)
                    ·
                      rfl

theorem cell22_280083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_280083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280083 prefixEnd_280083 := by exact prefixLift 280083
  have htrace : WordTrace (prefixWord ++ tailWord_280083) baseStart_280083 baseEnd_280083 := by
    simpa [prefixWord, tailWord_280083, baseEnd_280083] using wordTrace_append hprefix tailTrace_280083
  have hstable : (prefixWord ++ tailWord_280083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280083).length < 2 ^ (prefixWord ++ tailWord_280083).sum := by decide
  have hdescent : baseEnd_280083 < baseStart_280083 := by decide
  rcases family_descends (prefixWord ++ tailWord_280083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280188 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_280188 : Nat := 118140960795 + 280188 * 2 ^ 59
def prefixEnd_280188 : Nat := 4983230072969 + 3 ^ 40 * 280188 * 2
def baseEnd_280188 : Nat := 31971359471567777080321

theorem tailTrace_280188 : CollatzResearch.WordTrace tailWord_280188 prefixEnd_280188 31971359471567777080321 := by
  unfold tailWord_280188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109647954467101572896609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6812863939289468763862145 5109647954467101572896609)
  ·
    refine ⟨3832235965850326179672457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5109647954467101572896609 3832235965850326179672457)
    ·
      refine ⟨2874176974387744634754343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3832235965850326179672457 2874176974387744634754343)
      ·
        refine ⟨4311265461581616952131515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874176974387744634754343 4311265461581616952131515)
        ·
          refine ⟨6466898192372425428197273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311265461581616952131515 6466898192372425428197273)
          ·
            refine ⟨4850173644279319071147955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466898192372425428197273 4850173644279319071147955)
            ·
              refine ⟨7275260466418978606721933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850173644279319071147955 7275260466418978606721933)
              ·
                refine ⟨2728222674907116977520725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7275260466418978606721933 2728222674907116977520725)
                ·
                  refine ⟨31971359471567777080321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2728222674907116977520725 31971359471567777080321)
                  ·
                    rfl

theorem cell22_280188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_280188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280188 prefixEnd_280188 := by exact prefixLift 280188
  have htrace : WordTrace (prefixWord ++ tailWord_280188) baseStart_280188 baseEnd_280188 := by
    simpa [prefixWord, tailWord_280188, baseEnd_280188] using wordTrace_append hprefix tailTrace_280188
  have hstable : (prefixWord ++ tailWord_280188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280188).length < 2 ^ (prefixWord ++ tailWord_280188).sum := by decide
  have hdescent : baseEnd_280188 < baseStart_280188 := by decide
  rcases family_descends (prefixWord ++ tailWord_280188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280237 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_280237 : Nat := 118140960795 + 280237 * 2 ^ 59
def prefixEnd_280237 : Nat := 4983230072969 + 3 ^ 40 * 280237 * 2
def baseEnd_280237 : Nat := 95930852116083536765813

theorem tailTrace_280237 : CollatzResearch.WordTrace tailWord_280237 prefixEnd_280237 95930852116083536765813 := by
  unfold tailWord_280237
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221083085756684514326965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6814055390504456342884643 10221083085756684514326965)
  ·
    refine ⟨958226539289689173218153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10221083085756684514326965 958226539289689173218153)
    ·
      refine ⟨718669904467266879913615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958226539289689173218153 718669904467266879913615)
      ·
        refine ⟨1078004856700900319870423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718669904467266879913615 1078004856700900319870423)
        ·
          refine ⟨1617007285051350479805635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078004856700900319870423 1617007285051350479805635)
          ·
            refine ⟨2425510927577025719708453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617007285051350479805635 2425510927577025719708453)
            ·
              refine ⟨454783298920692322445335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2425510927577025719708453 454783298920692322445335)
              ·
                refine ⟨682174948381038483668003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454783298920692322445335 682174948381038483668003)
                ·
                  refine ⟨1023262422571557725502005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682174948381038483668003 1023262422571557725502005)
                  ·
                    refine ⟨95930852116083536765813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1023262422571557725502005 95930852116083536765813)
                    ·
                      rfl

theorem cell22_280237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_280237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280237 prefixEnd_280237 := by exact prefixLift 280237
  have htrace : WordTrace (prefixWord ++ tailWord_280237) baseStart_280237 baseEnd_280237 := by
    simpa [prefixWord, tailWord_280237, baseEnd_280237] using wordTrace_append hprefix tailTrace_280237
  have hstable : (prefixWord ++ tailWord_280237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280237).length < 2 ^ (prefixWord ++ tailWord_280237).sum := by decide
  have hdescent : baseEnd_280237 < baseStart_280237 := by decide
  rcases family_descends (prefixWord ++ tailWord_280237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280252 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_280252 : Nat := 118140960795 + 280252 * 2 ^ 59
def prefixEnd_280252 : Nat := 4983230072969 + 3 ^ 40 * 280252 * 2
def baseEnd_280252 : Nat := 95935986922628497640767

theorem tailTrace_280252 : CollatzResearch.WordTrace tailWord_280252 prefixEnd_280252 95935986922628497640767 := by
  unfold tailWord_280252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110815090351171038061505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6814420120468228050748673 5110815090351171038061505)
  ·
    refine ⟨3833111317763378278546129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5110815090351171038061505 3833111317763378278546129)
    ·
      refine ⟨2874833488322533708909597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3833111317763378278546129 2874833488322533708909597)
      ·
        refine ⟨1078062558120950140841099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2874833488322533708909597 1078062558120950140841099)
        ·
          refine ⟨1617093837181425211261649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078062558120950140841099 1617093837181425211261649)
          ·
            refine ⟨1212820377886068908446237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617093837181425211261649 1212820377886068908446237)
            ·
              refine ⟨454807641707275840667339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212820377886068908446237 454807641707275840667339)
              ·
                refine ⟨682211462560913761001009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454807641707275840667339 682211462560913761001009)
                ·
                  refine ⟨511658596920685320750757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682211462560913761001009 511658596920685320750757)
                  ·
                    refine ⟨95935986922628497640767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511658596920685320750757 95935986922628497640767)
                    ·
                      rfl

theorem cell22_280252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_280252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280252 prefixEnd_280252 := by exact prefixLift 280252
  have htrace : WordTrace (prefixWord ++ tailWord_280252) baseStart_280252 baseEnd_280252 := by
    simpa [prefixWord, tailWord_280252, baseEnd_280252] using wordTrace_append hprefix tailTrace_280252
  have hstable : (prefixWord ++ tailWord_280252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280252).length < 2 ^ (prefixWord ++ tailWord_280252).sum := by decide
  have hdescent : baseEnd_280252 < baseStart_280252 := by decide
  rcases family_descends (prefixWord ++ tailWord_280252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280258 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_280258 : Nat := 118140960795 + 280258 * 2 ^ 59
def prefixEnd_280258 : Nat := 4983230072969 + 3 ^ 40 * 280258 * 2
def baseEnd_280258 : Nat := 95938040845246481990749

theorem tailTrace_280258 : CollatzResearch.WordTrace tailWord_280258 prefixEnd_280258 95938040845246481990749 := by
  unfold tailWord_280258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555462254670151275210357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6814566012453736733894285 2555462254670151275210357)
  ·
    refine ⟨239574586375326682050971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2555462254670151275210357 239574586375326682050971)
    ·
      refine ⟨359361879562990023076457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239574586375326682050971 359361879562990023076457)
      ·
        refine ⟨269521409672242517307343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359361879562990023076457 269521409672242517307343)
        ·
          refine ⟨404282114508363775961015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269521409672242517307343 404282114508363775961015)
          ·
            refine ⟨606423171762545663941523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404282114508363775961015 606423171762545663941523)
            ·
              refine ⟨909634757643818495912285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606423171762545663941523 909634757643818495912285)
              ·
                refine ⟨341113034116431935967107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 909634757643818495912285 341113034116431935967107)
                ·
                  refine ⟨511669551174647903950661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341113034116431935967107 511669551174647903950661)
                  ·
                    refine ⟨95938040845246481990749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511669551174647903950661 95938040845246481990749)
                    ·
                      rfl

theorem cell22_280258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_280258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280258 prefixEnd_280258 := by exact prefixLift 280258
  have htrace : WordTrace (prefixWord ++ tailWord_280258) baseStart_280258 baseEnd_280258 := by
    simpa [prefixWord, tailWord_280258, baseEnd_280258] using wordTrace_append hprefix tailTrace_280258
  have hstable : (prefixWord ++ tailWord_280258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280258).length < 2 ^ (prefixWord ++ tailWord_280258).sum := by decide
  have hdescent : baseEnd_280258 < baseStart_280258 := by decide
  rcases family_descends (prefixWord ++ tailWord_280258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280282 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_280282 : Nat := 118140960795 + 280282 * 2 ^ 59
def prefixEnd_280282 : Nat := 4983230072969 + 3 ^ 40 * 280282 * 2
def baseEnd_280282 : Nat := 95946256535718419390675

theorem tailTrace_280282 : CollatzResearch.WordTrace tailWord_280282 prefixEnd_280282 95946256535718419390675 := by
  unfold tailWord_280282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555681092648414299928775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6815149580395771466476733 2555681092648414299928775)
  ·
    refine ⟨3833521638972621449893163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2555681092648414299928775 3833521638972621449893163)
    ·
      refine ⟨5750282458458932174839745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833521638972621449893163 5750282458458932174839745)
      ·
        refine ⟨4312711843844199131129809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5750282458458932174839745 4312711843844199131129809)
        ·
          refine ⟨3234533882883149348347357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4312711843844199131129809 3234533882883149348347357)
          ·
            refine ⟨1212950206081181005630259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3234533882883149348347357 1212950206081181005630259)
            ·
              refine ⟨1819425309121771508445389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212950206081181005630259 1819425309121771508445389)
              ·
                refine ⟨682284490920664315667021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1819425309121771508445389 682284490920664315667021)
                ·
                  refine ⟨255856684095249118375133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682284490920664315667021 255856684095249118375133)
                  ·
                    refine ⟨95946256535718419390675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255856684095249118375133 95946256535718419390675)
                    ·
                      rfl

theorem cell22_280282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_280282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280282 prefixEnd_280282 := by exact prefixLift 280282
  have htrace : WordTrace (prefixWord ++ tailWord_280282) baseStart_280282 baseEnd_280282 := by
    simpa [prefixWord, tailWord_280282, baseEnd_280282] using wordTrace_append hprefix tailTrace_280282
  have hstable : (prefixWord ++ tailWord_280282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280282).length < 2 ^ (prefixWord ++ tailWord_280282).sum := by decide
  have hdescent : baseEnd_280282 < baseStart_280282 := by decide
  rcases family_descends (prefixWord ++ tailWord_280282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280325 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_280325 : Nat := 118140960795 + 280325 * 2 ^ 59
def prefixEnd_280325 : Nat := 4983230072969 + 3 ^ 40 * 280325 * 2
def baseEnd_280325 : Nat := 95960976314480640565543

theorem tailTrace_280325 : CollatzResearch.WordTrace tailWord_280325 prefixEnd_280325 95960976314480640565543 := by
  unfold tailWord_280325
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224292709437875543530429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6816195139625250362353619 10224292709437875543530429)
  ·
    refine ⟨3834109766039203328823911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10224292709437875543530429 3834109766039203328823911)
    ·
      refine ⟨5751164649058804993235867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834109766039203328823911 5751164649058804993235867)
      ·
        refine ⟨8626746973588207489853801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751164649058804993235867 8626746973588207489853801)
        ·
          refine ⟨6470060230191155617390351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8626746973588207489853801 6470060230191155617390351)
          ·
            refine ⟨9705090345286733426085527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470060230191155617390351 9705090345286733426085527)
            ·
              refine ⟨14557635517930100139128291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705090345286733426085527 14557635517930100139128291)
              ·
                refine ⟨21836453276895150208692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14557635517930100139128291 21836453276895150208692437)
                ·
                  refine ⟨511791873677230083016229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21836453276895150208692437 511791873677230083016229)
                  ·
                    refine ⟨95960976314480640565543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511791873677230083016229 95960976314480640565543)
                    ·
                      rfl

theorem cell22_280325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_280325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280325 prefixEnd_280325 := by exact prefixLift 280325
  have htrace : WordTrace (prefixWord ++ tailWord_280325) baseStart_280325 baseEnd_280325 := by
    simpa [prefixWord, tailWord_280325, baseEnd_280325] using wordTrace_append hprefix tailTrace_280325
  have hstable : (prefixWord ++ tailWord_280325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280325).length < 2 ^ (prefixWord ++ tailWord_280325).sum := by decide
  have hdescent : baseEnd_280325 < baseStart_280325 := by decide
  rcases family_descends (prefixWord ++ tailWord_280325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280385 : List Nat := [1, 2, 5, 14]
def baseStart_280385 : Nat := 118140960795 + 280385 * 2 ^ 59
def prefixEnd_280385 : Nat := 4983230072969 + 3 ^ 40 * 280385 * 2
def baseEnd_280385 : Nat := 131661886887051418471

theorem tailTrace_280385 : CollatzResearch.WordTrace tailWord_280385 prefixEnd_280385 131661886887051418471 := by
  unfold tailWord_280385
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226481089220505790714609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6817654059480337193809739 10226481089220505790714609)
  ·
    refine ⟨7669860816915379343035957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10226481089220505790714609 7669860816915379343035957)
    ·
      refine ⟨719049451585816813409621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7669860816915379343035957 719049451585816813409621)
      ·
        refine ⟨131661886887051418471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 719049451585816813409621 131661886887051418471)
        ·
          rfl

theorem cell22_280385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 14].length) (baseStart_280385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280385 prefixEnd_280385 := by exact prefixLift 280385
  have htrace : WordTrace (prefixWord ++ tailWord_280385) baseStart_280385 baseEnd_280385 := by
    simpa [prefixWord, tailWord_280385, baseEnd_280385] using wordTrace_append hprefix tailTrace_280385
  have hstable : (prefixWord ++ tailWord_280385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280385).length < 2 ^ (prefixWord ++ tailWord_280385).sum := by decide
  have hdescent : baseEnd_280385 < baseStart_280385 := by decide
  rcases family_descends (prefixWord ++ tailWord_280385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280387 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_280387 : Nat := 118140960795 + 280387 * 2 ^ 59
def prefixEnd_280387 : Nat := 4983230072969 + 3 ^ 40 * 280387 * 2
def baseEnd_280387 : Nat := 95982200181533145515353

theorem tailTrace_280387 : CollatzResearch.WordTrace tailWord_280387 prefixEnd_280387 95982200181533145515353 := by
  unfold tailWord_280387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226554035213260132287415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6817702690142173421524943 10226554035213260132287415)
  ·
    refine ⟨15339831052819890198431123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10226554035213260132287415 15339831052819890198431123)
    ·
      refine ⟨23009746579229835297646685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15339831052819890198431123 23009746579229835297646685)
      ·
        refine ⟨8628654967211188236617507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23009746579229835297646685 8628654967211188236617507)
        ·
          refine ⟨12942982450816782354926261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628654967211188236617507 12942982450816782354926261)
          ·
            refine ⟨1213404604764073345774337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12942982450816782354926261 1213404604764073345774337)
            ·
              refine ⟨910053453573055009330753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213404604764073345774337 910053453573055009330753)
              ·
                refine ⟨682540090179791256998065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910053453573055009330753 682540090179791256998065)
                ·
                  refine ⟨511905067634843442748549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682540090179791256998065 511905067634843442748549)
                  ·
                    refine ⟨95982200181533145515353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 511905067634843442748549 95982200181533145515353)
                    ·
                      rfl

theorem cell22_280387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_280387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280387 prefixEnd_280387 := by exact prefixLift 280387
  have htrace : WordTrace (prefixWord ++ tailWord_280387) baseStart_280387 baseEnd_280387 := by
    simpa [prefixWord, tailWord_280387, baseEnd_280387] using wordTrace_append hprefix tailTrace_280387
  have hstable : (prefixWord ++ tailWord_280387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280387).length < 2 ^ (prefixWord ++ tailWord_280387).sum := by decide
  have hdescent : baseEnd_280387 < baseStart_280387 := by decide
  rcases family_descends (prefixWord ++ tailWord_280387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280389 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_280389 : Nat := 118140960795 + 280389 * 2 ^ 59
def prefixEnd_280389 : Nat := 4983230072969 + 3 ^ 40 * 280389 * 2
def baseEnd_280389 : Nat := 95982884822405806965347

theorem tailTrace_280389 : CollatzResearch.WordTrace tailWord_280389 prefixEnd_280389 95982884822405806965347 := by
  unfold tailWord_280389
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226626981206014473860221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6817751320804009649240147 10226626981206014473860221)
  ·
    refine ⟨3834985117952255427697583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10226626981206014473860221 3834985117952255427697583)
    ·
      refine ⟨5752477676928383141546375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834985117952255427697583 5752477676928383141546375)
      ·
        refine ⟨8628716515392574712319563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752477676928383141546375 8628716515392574712319563)
        ·
          refine ⟨12943074773088862068479345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628716515392574712319563 12943074773088862068479345)
          ·
            refine ⟨9707306079816646551359509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12943074773088862068479345 9707306079816646551359509)
            ·
              refine ⟨455029972491405307094977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9707306079816646551359509 455029972491405307094977)
              ·
                refine ⟨341272479368553980321233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455029972491405307094977 341272479368553980321233)
                ·
                  refine ⟨255954359526415485240925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341272479368553980321233 255954359526415485240925)
                  ·
                    refine ⟨95982884822405806965347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255954359526415485240925 95982884822405806965347)
                    ·
                      rfl

theorem cell22_280389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_280389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280389 prefixEnd_280389 := by exact prefixLift 280389
  have htrace : WordTrace (prefixWord ++ tailWord_280389) baseStart_280389 baseEnd_280389 := by
    simpa [prefixWord, tailWord_280389, baseEnd_280389] using wordTrace_append hprefix tailTrace_280389
  have hstable : (prefixWord ++ tailWord_280389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280389).length < 2 ^ (prefixWord ++ tailWord_280389).sum := by decide
  have hdescent : baseEnd_280389 < baseStart_280389 := by decide
  rcases family_descends (prefixWord ++ tailWord_280389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280400 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_280400 : Nat := 118140960795 + 280400 * 2 ^ 59
def prefixEnd_280400 : Nat := 4983230072969 + 3 ^ 40 * 280400 * 2
def baseEnd_280400 : Nat := 95986650347205444940313

theorem tailTrace_280400 : CollatzResearch.WordTrace tailWord_280400 prefixEnd_280400 95986650347205444940313 := by
  unfold tailWord_280400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113514092083081676255327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6818018789444108901673769 5113514092083081676255327)
  ·
    refine ⟨7670271138124622514382991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5113514092083081676255327 7670271138124622514382991)
    ·
      refine ⟨11505406707186933771574487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7670271138124622514382991 11505406707186933771574487)
      ·
        refine ⟨17258110060780400657361731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11505406707186933771574487 17258110060780400657361731)
        ·
          refine ⟨25887165091170600986042597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17258110060780400657361731 25887165091170600986042597)
          ·
            refine ⟨4853843454594487684882987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25887165091170600986042597 4853843454594487684882987)
            ·
              refine ⟨7280765181891731527324481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853843454594487684882987 7280765181891731527324481)
              ·
                refine ⟨5460573886418798645493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7280765181891731527324481 5460573886418798645493361)
                ·
                  refine ⟨4095430414814098984120021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5460573886418798645493361 4095430414814098984120021)
                  ·
                    refine ⟨95986650347205444940313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4095430414814098984120021 95986650347205444940313)
                    ·
                      rfl

theorem cell22_280400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_280400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280400 prefixEnd_280400 := by exact prefixLift 280400
  have htrace : WordTrace (prefixWord ++ tailWord_280400) baseStart_280400 baseEnd_280400 := by
    simpa [prefixWord, tailWord_280400, baseEnd_280400] using wordTrace_append hprefix tailTrace_280400
  have hstable : (prefixWord ++ tailWord_280400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280400).length < 2 ^ (prefixWord ++ tailWord_280400).sum := by decide
  have hdescent : baseEnd_280400 < baseStart_280400 := by decide
  rcases family_descends (prefixWord ++ tailWord_280400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280402 : List Nat := [3, 2, 2, 1, 1, 3, 3, 7]
def baseStart_280402 : Nat := 118140960795 + 280402 * 2 ^ 59
def prefixEnd_280402 : Nat := 4983230072969 + 3 ^ 40 * 280402 * 2
def baseEnd_280402 : Nat := 10665259443119789598923

theorem tailTrace_280402 : CollatzResearch.WordTrace tailWord_280402 prefixEnd_280402 10665259443119789598923 := by
  unfold tailWord_280402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556775282539729423520865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6818067420105945129388973 2556775282539729423520865)
  ·
    refine ⟨1917581461904797067640649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2556775282539729423520865 1917581461904797067640649)
    ·
      refine ⟨1438186096428597800730487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1917581461904797067640649 1438186096428597800730487)
      ·
        refine ⟨2157279144642896701095731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438186096428597800730487 2157279144642896701095731)
        ·
          refine ⟨3235918716964345051643597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157279144642896701095731 3235918716964345051643597)
          ·
            refine ⟨1213469518861629394366349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3235918716964345051643597 1213469518861629394366349)
            ·
              refine ⟨455051069573111022887381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1213469518861629394366349 455051069573111022887381)
              ·
                refine ⟨10665259443119789598923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 455051069573111022887381 10665259443119789598923)
                ·
                  rfl

theorem cell22_280402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_280402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280402 prefixEnd_280402 := by exact prefixLift 280402
  have htrace : WordTrace (prefixWord ++ tailWord_280402) baseStart_280402 baseEnd_280402 := by
    simpa [prefixWord, tailWord_280402, baseEnd_280402] using wordTrace_append hprefix tailTrace_280402
  have hstable : (prefixWord ++ tailWord_280402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280402).length < 2 ^ (prefixWord ++ tailWord_280402).sum := by decide
  have hdescent : baseEnd_280402 < baseStart_280402 := by decide
  rcases family_descends (prefixWord ++ tailWord_280402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280419 : List Nat := [1, 1, 1, 5, 4, 1, 3, 6]
def baseStart_280419 : Nat := 118140960795 + 280419 * 2 ^ 59
def prefixEnd_280419 : Nat := 4983230072969 + 3 ^ 40 * 280419 * 2
def baseEnd_280419 : Nat := 10665906048388414301695

theorem tailTrace_280419 : CollatzResearch.WordTrace tailWord_280419 prefixEnd_280419 10665906048388414301695 := by
  unfold tailWord_280419
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227721171097329597452311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6818480780731553064968207 10227721171097329597452311)
  ·
    refine ⟨15341581756645994396178467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227721171097329597452311 15341581756645994396178467)
    ·
      refine ⟨23012372634968991594267701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15341581756645994396178467 23012372634968991594267701)
      ·
        refine ⟨2157409934528342961962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23012372634968991594267701 2157409934528342961962597)
        ·
          refine ⟨404514362724064305367987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2157409934528342961962597 404514362724064305367987)
          ·
            refine ⟨606771544086096458051981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404514362724064305367987 606771544086096458051981)
            ·
              refine ⟨227539329032286171769493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606771544086096458051981 227539329032286171769493)
              ·
                refine ⟨10665906048388414301695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227539329032286171769493 10665906048388414301695)
                ·
                  rfl

theorem cell22_280419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 6].length) (baseStart_280419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280419 prefixEnd_280419 := by exact prefixLift 280419
  have htrace : WordTrace (prefixWord ++ tailWord_280419) baseStart_280419 baseEnd_280419 := by
    simpa [prefixWord, tailWord_280419, baseEnd_280419] using wordTrace_append hprefix tailTrace_280419
  have hstable : (prefixWord ++ tailWord_280419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280419).length < 2 ^ (prefixWord ++ tailWord_280419).sum := by decide
  have hdescent : baseEnd_280419 < baseStart_280419 := by decide
  rcases family_descends (prefixWord ++ tailWord_280419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280451 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 1, 3]
def baseStart_280451 : Nat := 118140960795 + 280451 * 2 ^ 59
def prefixEnd_280451 : Nat := 4983230072969 + 3 ^ 40 * 280451 * 2
def baseEnd_280451 : Nat := 96004108689458311915157

theorem tailTrace_280451 : CollatzResearch.WordTrace tailWord_280451 prefixEnd_280451 96004108689458311915157 := by
  unfold tailWord_280451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228888306981399062617207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6819258871320932708411471 10228888306981399062617207)
  ·
    refine ⟨15343332460472098593925811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10228888306981399062617207 15343332460472098593925811)
    ·
      refine ⟨23014998690708147890888717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15343332460472098593925811 23014998690708147890888717)
      ·
        refine ⟨8630624509015555459083269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23014998690708147890888717 8630624509015555459083269)
        ·
          refine ⟨1618242095440416648578113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8630624509015555459083269 1618242095440416648578113)
          ·
            refine ⟨1213681571580312486433585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618242095440416648578113 1213681571580312486433585)
            ·
              refine ⟨910261178685234364825189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213681571580312486433585 910261178685234364825189)
              ·
                refine ⟨170673971003481443404723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 910261178685234364825189 170673971003481443404723)
                ·
                  refine ⟨256010956505222165107085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170673971003481443404723 256010956505222165107085)
                  ·
                    refine ⟨96004108689458311915157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256010956505222165107085 96004108689458311915157)
                    ·
                      rfl

theorem cell22_280451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 3].length) (baseStart_280451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280451 prefixEnd_280451 := by exact prefixLift 280451
  have htrace : WordTrace (prefixWord ++ tailWord_280451) baseStart_280451 baseEnd_280451 := by
    simpa [prefixWord, tailWord_280451, baseEnd_280451] using wordTrace_append hprefix tailTrace_280451
  have hstable : (prefixWord ++ tailWord_280451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280451).length < 2 ^ (prefixWord ++ tailWord_280451).sum := by decide
  have hdescent : baseEnd_280451 < baseStart_280451 := by decide
  rcases family_descends (prefixWord ++ tailWord_280451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280470 : List Nat := [5, 3, 1, 1, 2, 2, 2, 6]
def baseStart_280470 : Nat := 118140960795 + 280470 * 2 ^ 59
def prefixEnd_280470 : Nat := 4983230072969 + 3 ^ 40 * 280470 * 2
def baseEnd_280470 : Nat := 10667845864194288410011

theorem tailTrace_280470 : CollatzResearch.WordTrace tailWord_280470 prefixEnd_280470 10667845864194288410011 := by
  unfold tailWord_280470
  simp only [CollatzResearch.WordTrace]
  refine ⟨639348830869535331722429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6819720862608376871705909 639348830869535331722429)
  ·
    refine ⟨239755811576075749395911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 639348830869535331722429 239755811576075749395911)
    ·
      refine ⟨359633717364113624093867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239755811576075749395911 359633717364113624093867)
      ·
        refine ⟨539450576046170436140801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359633717364113624093867 539450576046170436140801)
        ·
          refine ⟨404587932034627827105601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539450576046170436140801 404587932034627827105601)
          ·
            refine ⟨303440949025970870329201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404587932034627827105601 303440949025970870329201)
            ·
              refine ⟨227580711769478152746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303440949025970870329201 227580711769478152746901)
              ·
                refine ⟨10667845864194288410011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227580711769478152746901 10667845864194288410011)
                ·
                  rfl

theorem cell22_280470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_280470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280470 prefixEnd_280470 := by exact prefixLift 280470
  have htrace : WordTrace (prefixWord ++ tailWord_280470) baseStart_280470 baseEnd_280470 := by
    simpa [prefixWord, tailWord_280470, baseEnd_280470] using wordTrace_append hprefix tailTrace_280470
  have hstable : (prefixWord ++ tailWord_280470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280470).length < 2 ^ (prefixWord ++ tailWord_280470).sum := by decide
  have hdescent : baseEnd_280470 < baseStart_280470 := by decide
  rcases family_descends (prefixWord ++ tailWord_280470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280509 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 6]
def baseStart_280509 : Nat := 118140960795 + 280509 * 2 ^ 59
def prefixEnd_280509 : Nat := 4983230072969 + 3 ^ 40 * 280509 * 2
def baseEnd_280509 : Nat := 32007987758255164654993

theorem tailTrace_280509 : CollatzResearch.WordTrace tailWord_280509 prefixEnd_280509 32007987758255164654993 := by
  unfold tailWord_280509
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231003740771274968228581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6820669160514183312152387 10231003740771274968228581)
  ·
    refine ⟨1918313201394614056542859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10231003740771274968228581 1918313201394614056542859)
    ·
      refine ⟨2877469802091921084814289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918313201394614056542859 2877469802091921084814289)
      ·
        refine ⟨2158102351568940813610717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2877469802091921084814289 2158102351568940813610717)
        ·
          refine ⟨809288381838352805104019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2158102351568940813610717 809288381838352805104019)
          ·
            refine ⟨1213932572757529207656029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809288381838352805104019 1213932572757529207656029)
            ·
              refine ⟨455224714784073452871011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1213932572757529207656029 455224714784073452871011)
              ·
                refine ⟨682837072176110179306517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455224714784073452871011 682837072176110179306517)
                ·
                  refine ⟨32007987758255164654993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 682837072176110179306517 32007987758255164654993)
                  ·
                    rfl

theorem cell22_280509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_280509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280509 prefixEnd_280509 := by exact prefixLift 280509
  have htrace : WordTrace (prefixWord ++ tailWord_280509) baseStart_280509 baseEnd_280509 := by
    simpa [prefixWord, tailWord_280509, baseEnd_280509] using wordTrace_append hprefix tailTrace_280509
  have hstable : (prefixWord ++ tailWord_280509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280509).length < 2 ^ (prefixWord ++ tailWord_280509).sum := by decide
  have hdescent : baseEnd_280509 < baseStart_280509 := by decide
  rcases family_descends (prefixWord ++ tailWord_280509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280522 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_280522 : Nat := 118140960795 + 280522 * 2 ^ 59
def prefixEnd_280522 : Nat := 4983230072969 + 3 ^ 40 * 280522 * 2
def baseEnd_280522 : Nat := 96028413440437793389939

theorem tailTrace_280522 : CollatzResearch.WordTrace tailWord_280522 prefixEnd_280522 96028413440437793389939 := by
  unfold tailWord_280522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557869472431044547112955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6820985259816118792301213 2557869472431044547112955)
  ·
    refine ⟨3836804208646566820669433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557869472431044547112955 3836804208646566820669433)
    ·
      refine ⟨2877603156484925115502075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3836804208646566820669433 2877603156484925115502075)
      ·
        refine ⟨4316404734727387673253113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877603156484925115502075 4316404734727387673253113)
        ·
          refine ⟨3237303551045540754939835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316404734727387673253113 3237303551045540754939835)
          ·
            refine ⟨4855955326568311132409753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237303551045540754939835 4855955326568311132409753)
            ·
              refine ⟨3641966494926233349307315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855955326568311132409753 3641966494926233349307315)
              ·
                refine ⟨5462949742389350023960973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641966494926233349307315 5462949742389350023960973)
                ·
                  refine ⟨2048606153396006258985365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5462949742389350023960973 2048606153396006258985365)
                  ·
                    refine ⟨96028413440437793389939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2048606153396006258985365 96028413440437793389939)
                    ·
                      rfl

theorem cell22_280522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_280522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280522 prefixEnd_280522 := by exact prefixLift 280522
  have htrace : WordTrace (prefixWord ++ tailWord_280522) baseStart_280522 baseEnd_280522 := by
    simpa [prefixWord, tailWord_280522, baseEnd_280522] using wordTrace_append hprefix tailTrace_280522
  have hstable : (prefixWord ++ tailWord_280522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280522).length < 2 ^ (prefixWord ++ tailWord_280522).sum := by decide
  have hdescent : baseEnd_280522 < baseStart_280522 := by decide
  rcases family_descends (prefixWord ++ tailWord_280522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280541 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_280541 : Nat := 118140960795 + 280541 * 2 ^ 59
def prefixEnd_280541 : Nat := 4983230072969 + 3 ^ 40 * 280541 * 2
def baseEnd_280541 : Nat := 96034917528728077164881

theorem tailTrace_280541 : CollatzResearch.WordTrace tailWord_280541 prefixEnd_280541 96034917528728077164881 := by
  unfold tailWord_280541
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232170876655344433393477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6821447251103562955595651 10232170876655344433393477)
  ·
    refine ⟨1918532039372877081261277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10232170876655344433393477 1918532039372877081261277)
    ·
      refine ⟨719449514764828905472979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1918532039372877081261277 719449514764828905472979)
      ·
        refine ⟨1079174272147243358209469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719449514764828905472979 1079174272147243358209469)
        ·
          refine ⟨404690352055216259328551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1079174272147243358209469 404690352055216259328551)
          ·
            refine ⟨607035528082824388992827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404690352055216259328551 607035528082824388992827)
            ·
              refine ⟨910553292124236583489241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607035528082824388992827 910553292124236583489241)
              ·
                refine ⟨682914969093177437616931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910553292124236583489241 682914969093177437616931)
                ·
                  refine ⟨1024372453639766156425397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682914969093177437616931 1024372453639766156425397)
                  ·
                    refine ⟨96034917528728077164881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1024372453639766156425397 96034917528728077164881)
                    ·
                      rfl

theorem cell22_280541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_280541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280541 prefixEnd_280541 := by exact prefixLift 280541
  have htrace : WordTrace (prefixWord ++ tailWord_280541) baseStart_280541 baseEnd_280541 := by
    simpa [prefixWord, tailWord_280541, baseEnd_280541] using wordTrace_append hprefix tailTrace_280541
  have hstable : (prefixWord ++ tailWord_280541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280541).length < 2 ^ (prefixWord ++ tailWord_280541).sum := by decide
  have hdescent : baseEnd_280541 < baseStart_280541 := by decide
  rcases family_descends (prefixWord ++ tailWord_280541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280558 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_280558 : Nat := 118140960795 + 280558 * 2 ^ 59
def prefixEnd_280558 : Nat := 4983230072969 + 3 ^ 40 * 280558 * 2
def baseEnd_280558 : Nat := 96040736976145699489829

theorem tailTrace_280558 : CollatzResearch.WordTrace tailWord_280558 prefixEnd_280558 96040736976145699489829 := by
  unfold tailWord_280558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279098864699219542095291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6821860611729170891174885 1279098864699219542095291)
  ·
    refine ⟨1918648297048829313142937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1279098864699219542095291 1918648297048829313142937)
    ·
      refine ⟨1438986222786621984857203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1918648297048829313142937 1438986222786621984857203)
      ·
        refine ⟨2158479334179932977285805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438986222786621984857203 2158479334179932977285805)
        ·
          refine ⟨809429750317474866482177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2158479334179932977285805 809429750317474866482177)
          ·
            refine ⟨607072312738106149861633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809429750317474866482177 607072312738106149861633)
            ·
              refine ⟨455304234553579612396225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607072312738106149861633 455304234553579612396225)
              ·
                refine ⟨341478175915184709297169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455304234553579612396225 341478175915184709297169)
                ·
                  refine ⟨256108631936388531972877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341478175915184709297169 256108631936388531972877)
                  ·
                    refine ⟨96040736976145699489829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256108631936388531972877 96040736976145699489829)
                    ·
                      rfl

theorem cell22_280558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_280558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280558 prefixEnd_280558 := by exact prefixLift 280558
  have htrace : WordTrace (prefixWord ++ tailWord_280558) baseStart_280558 baseEnd_280558 := by
    simpa [prefixWord, tailWord_280558, baseEnd_280558] using wordTrace_append hprefix tailTrace_280558
  have hstable : (prefixWord ++ tailWord_280558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280558).length < 2 ^ (prefixWord ++ tailWord_280558).sum := by decide
  have hdescent : baseEnd_280558 < baseStart_280558 := by decide
  rcases family_descends (prefixWord ++ tailWord_280558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280629 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_280629 : Nat := 118140960795 + 280629 * 2 ^ 59
def prefixEnd_280629 : Nat := 4983230072969 + 3 ^ 40 * 280629 * 2
def baseEnd_280629 : Nat := 96065041727125180964611

theorem tailTrace_280629 : CollatzResearch.WordTrace tailWord_280629 prefixEnd_280629 96065041727125180964611 := by
  unfold tailWord_280629
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235380500336535462596941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6823587000224356975064627 10235380500336535462596941)
  ·
    refine ⟨3838267687626200798473853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10235380500336535462596941 3838267687626200798473853)
    ·
      refine ⟨1439350382859825299427695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3838267687626200798473853 1439350382859825299427695)
      ·
        refine ⟨2159025574289737949141543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439350382859825299427695 2159025574289737949141543)
        ·
          refine ⟨3238538361434606923712315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159025574289737949141543 3238538361434606923712315)
          ·
            refine ⟨4857807542151910385568473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238538361434606923712315 4857807542151910385568473)
            ·
              refine ⟨3643355656613932789176355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857807542151910385568473 3643355656613932789176355)
              ·
                refine ⟨5465033484920899183764533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643355656613932789176355 5465033484920899183764533)
                ·
                  refine ⟨512346889211334298477925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5465033484920899183764533 512346889211334298477925)
                  ·
                    refine ⟨96065041727125180964611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512346889211334298477925 96065041727125180964611)
                    ·
                      rfl

theorem cell22_280629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_280629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280629 prefixEnd_280629 := by exact prefixLift 280629
  have htrace : WordTrace (prefixWord ++ tailWord_280629) baseStart_280629 baseEnd_280629 := by
    simpa [prefixWord, tailWord_280629, baseEnd_280629] using wordTrace_append hprefix tailTrace_280629
  have hstable : (prefixWord ++ tailWord_280629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280629).length < 2 ^ (prefixWord ++ tailWord_280629).sum := by decide
  have hdescent : baseEnd_280629 < baseStart_280629 := by decide
  rcases family_descends (prefixWord ++ tailWord_280629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280633 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 5]
def baseStart_280633 : Nat := 118140960795 + 280633 * 2 ^ 59
def prefixEnd_280633 : Nat := 4983230072969 + 3 ^ 40 * 280633 * 2
def baseEnd_280633 : Nat := 32022137002956834621533

theorem tailTrace_280633 : CollatzResearch.WordTrace tailWord_280633 prefixEnd_280633 32022137002956834621533 := by
  unfold tailWord_280633
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235526392322044145742553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6823684261548029430495035 10235526392322044145742553)
  ·
    refine ⟨7676644794241533109306915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10235526392322044145742553 7676644794241533109306915)
    ·
      refine ⟨11514967191362299663960373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676644794241533109306915 11514967191362299663960373)
      ·
        refine ⟨1079528174190215593496285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11514967191362299663960373 1079528174190215593496285)
        ·
          refine ⟨404823065321330847561107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1079528174190215593496285 404823065321330847561107)
          ·
            refine ⟨607234597981996271341661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404823065321330847561107 607234597981996271341661)
            ·
              refine ⟨227712974243248601753123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607234597981996271341661 227712974243248601753123)
              ·
                refine ⟨341569461364872902629685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227712974243248601753123 341569461364872902629685)
                ·
                  refine ⟨32022137002956834621533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341569461364872902629685 32022137002956834621533)
                  ·
                    rfl

theorem cell22_280633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_280633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280633 prefixEnd_280633 := by exact prefixLift 280633
  have htrace : WordTrace (prefixWord ++ tailWord_280633) baseStart_280633 baseEnd_280633 := by
    simpa [prefixWord, tailWord_280633, baseEnd_280633] using wordTrace_append hprefix tailTrace_280633
  have hstable : (prefixWord ++ tailWord_280633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280633).length < 2 ^ (prefixWord ++ tailWord_280633).sum := by decide
  have hdescent : baseEnd_280633 < baseStart_280633 := by decide
  rcases family_descends (prefixWord ++ tailWord_280633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280676 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_280676 : Nat := 118140960795 + 280676 * 2 ^ 59
def prefixEnd_280676 : Nat := 4983230072969 + 3 ^ 40 * 280676 * 2
def baseEnd_280676 : Nat := 96081130787632725039467

theorem tailTrace_280676 : CollatzResearch.WordTrace tailWord_280676 prefixEnd_280676 96081130787632725039467 := by
  unfold tailWord_280676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118547365583131244778941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6824729820777508326371921 5118547365583131244778941)
  ·
    refine ⟨1919455262093674216792103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5118547365583131244778941 1919455262093674216792103)
    ·
      refine ⟨2879182893140511325188155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919455262093674216792103 2879182893140511325188155)
      ·
        refine ⟨4318774339710766987782233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2879182893140511325188155 4318774339710766987782233)
        ·
          refine ⟨3239080754783075240836675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318774339710766987782233 3239080754783075240836675)
          ·
            refine ⟨4858621132174612861255013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239080754783075240836675 4858621132174612861255013)
            ·
              refine ⟨910991462282739911485315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4858621132174612861255013 910991462282739911485315)
              ·
                refine ⟨1366487193424109867227973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910991462282739911485315 1366487193424109867227973)
                ·
                  refine ⟨256216348767020600105245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366487193424109867227973 256216348767020600105245)
                  ·
                    refine ⟨96081130787632725039467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256216348767020600105245 96081130787632725039467)
                    ·
                      rfl

theorem cell22_280676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_280676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280676 prefixEnd_280676 := by exact prefixLift 280676
  have htrace : WordTrace (prefixWord ++ tailWord_280676) baseStart_280676 baseEnd_280676 := by
    simpa [prefixWord, tailWord_280676, baseEnd_280676] using wordTrace_append hprefix tailTrace_280676
  have hstable : (prefixWord ++ tailWord_280676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280676).length < 2 ^ (prefixWord ++ tailWord_280676).sum := by decide
  have hdescent : baseEnd_280676 < baseStart_280676 := by decide
  rcases family_descends (prefixWord ++ tailWord_280676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280689 : List Nat := [1, 2, 2, 2, 1, 1, 6, 7]
def baseStart_280689 : Nat := 118140960795 + 280689 * 2 ^ 59
def prefixEnd_280689 : Nat := 4983230072969 + 3 ^ 40 * 280689 * 2
def baseEnd_280689 : Nat := 10676175661478336051603

theorem tailTrace_280689 : CollatzResearch.WordTrace tailWord_280689 prefixEnd_280689 10676175661478336051603 := by
  unfold tailWord_280689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10237568880119165709781121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6825045920079443806520747 10237568880119165709781121)
  ·
    refine ⟨7678176660089374282335841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10237568880119165709781121 7678176660089374282335841)
    ·
      refine ⟨5758632495067030711751881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7678176660089374282335841 5758632495067030711751881)
      ·
        refine ⟨4318974371300273033813911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5758632495067030711751881 4318974371300273033813911)
        ·
          refine ⟨6478461556950409550720867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318974371300273033813911 6478461556950409550720867)
          ·
            refine ⟨9717692335425614326081301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478461556950409550720867 9717692335425614326081301)
            ·
              refine ⟨455516828223075671535061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9717692335425614326081301 455516828223075671535061)
              ·
                refine ⟨10676175661478336051603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 455516828223075671535061 10676175661478336051603)
                ·
                  rfl

theorem cell22_280689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 7].length) (baseStart_280689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280689 prefixEnd_280689 := by exact prefixLift 280689
  have htrace : WordTrace (prefixWord ++ tailWord_280689) baseStart_280689 baseEnd_280689 := by
    simpa [prefixWord, tailWord_280689, baseEnd_280689] using wordTrace_append hprefix tailTrace_280689
  have hstable : (prefixWord ++ tailWord_280689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280689).length < 2 ^ (prefixWord ++ tailWord_280689).sum := by decide
  have hdescent : baseEnd_280689 < baseStart_280689 := by decide
  rcases family_descends (prefixWord ++ tailWord_280689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280772 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_280772 : Nat := 118140960795 + 280772 * 2 ^ 59
def prefixEnd_280772 : Nat := 4983230072969 + 3 ^ 40 * 280772 * 2
def baseEnd_280772 : Nat := 96113993549520474639173

theorem tailTrace_280772 : CollatzResearch.WordTrace tailWord_280772 prefixEnd_280772 96113993549520474639173 := by
  unfold tailWord_280772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120298069409235442526285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6827064092545647256701713 5120298069409235442526285)
  ·
    refine ⟨1920111776028463290947357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5120298069409235442526285 1920111776028463290947357)
    ·
      refine ⟨720041916010673734105259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1920111776028463290947357 720041916010673734105259)
      ·
        refine ⟨1080062874016010601157889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720041916010673734105259 1080062874016010601157889)
        ·
          refine ⟨810047155512007950868417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080062874016010601157889 810047155512007950868417)
          ·
            refine ⟨607535366634005963151313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810047155512007950868417 607535366634005963151313)
            ·
              refine ⟨455651524975504472363485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607535366634005963151313 455651524975504472363485)
              ·
                refine ⟨170869321865814177136307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455651524975504472363485 170869321865814177136307)
                ·
                  refine ⟨256303982798721265704461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170869321865814177136307 256303982798721265704461)
                  ·
                    refine ⟨96113993549520474639173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256303982798721265704461 96113993549520474639173)
                    ·
                      rfl

theorem cell22_280772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_280772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280772 prefixEnd_280772 := by exact prefixLift 280772
  have htrace : WordTrace (prefixWord ++ tailWord_280772) baseStart_280772 baseEnd_280772 := by
    simpa [prefixWord, tailWord_280772, baseEnd_280772] using wordTrace_append hprefix tailTrace_280772
  have hstable : (prefixWord ++ tailWord_280772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280772).length < 2 ^ (prefixWord ++ tailWord_280772).sum := by decide
  have hdescent : baseEnd_280772 < baseStart_280772 := by decide
  rcases family_descends (prefixWord ++ tailWord_280772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280779 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 8]
def baseStart_280779 : Nat := 118140960795 + 280779 * 2 ^ 59
def prefixEnd_280779 : Nat := 4983230072969 + 3 ^ 40 * 280779 * 2
def baseEnd_280779 : Nat := 32038796597524929904717

theorem tailTrace_280779 : CollatzResearch.WordTrace tailWord_280779 prefixEnd_280779 32038796597524929904717 := by
  unfold tailWord_280779
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240851449793111080557391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6827234299862074053704927 10240851449793111080557391)
  ·
    refine ⟨15361277174689666620836087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240851449793111080557391 15361277174689666620836087)
    ·
      refine ⟨23041915762034499931254131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15361277174689666620836087 23041915762034499931254131)
      ·
        refine ⟨34562873643051749896881197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23041915762034499931254131 34562873643051749896881197)
        ·
          refine ⟨12961077616144406211330449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34562873643051749896881197 12961077616144406211330449)
          ·
            refine ⟨9720808212108304658497837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12961077616144406211330449 9720808212108304658497837)
            ·
              refine ⟨3645303079540614246936689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9720808212108304658497837 3645303079540614246936689)
              ·
                refine ⟨2733977309655460685202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645303079540614246936689 2733977309655460685202517)
                ·
                  refine ⟨32038796597524929904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2733977309655460685202517 32038796597524929904717)
                  ·
                    rfl

theorem cell22_280779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_280779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280779 prefixEnd_280779 := by exact prefixLift 280779
  have htrace : WordTrace (prefixWord ++ tailWord_280779) baseStart_280779 baseEnd_280779 := by
    simpa [prefixWord, tailWord_280779, baseEnd_280779] using wordTrace_append hprefix tailTrace_280779
  have hstable : (prefixWord ++ tailWord_280779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280779).length < 2 ^ (prefixWord ++ tailWord_280779).sum := by decide
  have hdescent : baseEnd_280779 < baseStart_280779 := by decide
  rcases family_descends (prefixWord ++ tailWord_280779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280826 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_280826 : Nat := 118140960795 + 280826 * 2 ^ 59
def prefixEnd_280826 : Nat := 4983230072969 + 3 ^ 40 * 280826 * 2
def baseEnd_280826 : Nat := 96132478853082333789007

theorem tailTrace_280826 : CollatzResearch.WordTrace tailWord_280826 prefixEnd_280826 96132478853082333789007 := by
  unfold tailWord_280826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560641420155709526879583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6828377120415225405012221 2560641420155709526879583)
  ·
    refine ⟨3840962130233564290319375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560641420155709526879583 3840962130233564290319375)
    ·
      refine ⟨5761443195350346435479063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840962130233564290319375 5761443195350346435479063)
      ·
        refine ⟨8642164793025519653218595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761443195350346435479063 8642164793025519653218595)
        ·
          refine ⟨12963247189538279479827893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642164793025519653218595 12963247189538279479827893)
          ·
            refine ⟨1215304424019213701233865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12963247189538279479827893 1215304424019213701233865)
            ·
              refine ⟨911478318014410275925399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215304424019213701233865 911478318014410275925399)
              ·
                refine ⟨1367217477021615413888099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911478318014410275925399 1367217477021615413888099)
                ·
                  refine ⟨2050826215532423120832149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367217477021615413888099 2050826215532423120832149)
                  ·
                    refine ⟨96132478853082333789007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2050826215532423120832149 96132478853082333789007)
                    ·
                      rfl

theorem cell22_280826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_280826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280826 prefixEnd_280826 := by exact prefixLift 280826
  have htrace : WordTrace (prefixWord ++ tailWord_280826) baseStart_280826 baseEnd_280826 := by
    simpa [prefixWord, tailWord_280826, baseEnd_280826] using wordTrace_append hprefix tailTrace_280826
  have hstable : (prefixWord ++ tailWord_280826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280826).length < 2 ^ (prefixWord ++ tailWord_280826).sum := by decide
  have hdescent : baseEnd_280826 < baseStart_280826 := by decide
  rcases family_descends (prefixWord ++ tailWord_280826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280828 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_280828 : Nat := 118140960795 + 280828 * 2 ^ 59
def prefixEnd_280828 : Nat := 4983230072969 + 3 ^ 40 * 280828 * 2
def baseEnd_280828 : Nat := 96133163493954995239001

theorem tailTrace_280828 : CollatzResearch.WordTrace tailWord_280828 prefixEnd_280828 96133163493954995239001 := by
  unfold tailWord_280828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121319313307796224545569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6828425751077061632727425 5121319313307796224545569)
  ·
    refine ⟨3840989484980847168409177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5121319313307796224545569 3840989484980847168409177)
    ·
      refine ⟨2880742113735635376306883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3840989484980847168409177 2880742113735635376306883)
      ·
        refine ⟨4321113170603453064460325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880742113735635376306883 4321113170603453064460325)
        ·
          refine ⟨810208719488147449586311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4321113170603453064460325 810208719488147449586311)
          ·
            refine ⟨1215313079232221174379467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810208719488147449586311 1215313079232221174379467)
            ·
              refine ⟨1822969618848331761569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215313079232221174379467 1822969618848331761569201)
              ·
                refine ⟨1367227214136248821176901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822969618848331761569201 1367227214136248821176901)
                ·
                  refine ⟨256355102650546653970669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367227214136248821176901 256355102650546653970669)
                  ·
                    refine ⟨96133163493954995239001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256355102650546653970669 96133163493954995239001)
                    ·
                      rfl

theorem cell22_280828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_280828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280828 prefixEnd_280828 := by exact prefixLift 280828
  have htrace : WordTrace (prefixWord ++ tailWord_280828) baseStart_280828 baseEnd_280828 := by
    simpa [prefixWord, tailWord_280828, baseEnd_280828] using wordTrace_append hprefix tailTrace_280828
  have hstable : (prefixWord ++ tailWord_280828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280828).length < 2 ^ (prefixWord ++ tailWord_280828).sum := by decide
  have hdescent : baseEnd_280828 < baseStart_280828 := by decide
  rcases family_descends (prefixWord ++ tailWord_280828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280841 : List Nat := [1, 2, 1, 1, 3, 6, 8]
def baseStart_280841 : Nat := 118140960795 + 280841 * 2 ^ 59
def prefixEnd_280841 : Nat := 4983230072969 + 3 ^ 40 * 280841 * 2
def baseEnd_280841 : Nat := 3560652357763973876443

theorem tailTrace_280841 : CollatzResearch.WordTrace tailWord_280841 prefixEnd_280841 3560652357763973876443 := by
  unfold tailWord_280841
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243112775568495669314377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6828741850378997112876251 10243112775568495669314377)
  ·
    refine ⟨7682334581676371751985783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10243112775568495669314377 7682334581676371751985783)
    ·
      refine ⟨11523501872514557627978675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7682334581676371751985783 11523501872514557627978675)
      ·
        refine ⟨17285252808771836441968013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11523501872514557627978675 17285252808771836441968013)
        ·
          refine ⟨6481969803289438665738005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17285252808771836441968013 6481969803289438665738005)
          ·
            refine ⟨303842334529192437456469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6481969803289438665738005 303842334529192437456469)
            ·
              refine ⟨3560652357763973876443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 303842334529192437456469 3560652357763973876443)
              ·
                rfl

theorem cell22_280841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 8].length) (baseStart_280841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280841 prefixEnd_280841 := by exact prefixLift 280841
  have htrace : WordTrace (prefixWord ++ tailWord_280841) baseStart_280841 baseEnd_280841 := by
    simpa [prefixWord, tailWord_280841, baseEnd_280841] using wordTrace_append hprefix tailTrace_280841
  have hstable : (prefixWord ++ tailWord_280841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280841).length < 2 ^ (prefixWord ++ tailWord_280841).sum := by decide
  have hdescent : baseEnd_280841 < baseStart_280841 := by decide
  rcases family_descends (prefixWord ++ tailWord_280841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280858 : List Nat := [3, 1, 1, 3, 4, 1, 2, 7]
def baseStart_280858 : Nat := 118140960795 + 280858 * 2 ^ 59
def prefixEnd_280858 : Nat := 4983230072969 + 3 ^ 40 * 280858 * 2
def baseEnd_280858 : Nat := 10682603678560546332101

theorem tailTrace_280858 : CollatzResearch.WordTrace tailWord_280858 prefixEnd_280858 10682603678560546332101 := by
  unfold tailWord_280858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560933204126726893170807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6829155211004605048455485 2560933204126726893170807)
  ·
    refine ⟨3841399806190090339756211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560933204126726893170807 3841399806190090339756211)
    ·
      refine ⟨5762099709285135509634317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841399806190090339756211 5762099709285135509634317)
      ·
        refine ⟨2160787390981925816112869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5762099709285135509634317 2160787390981925816112869)
        ·
          refine ⟨405147635809111090521163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2160787390981925816112869 405147635809111090521163)
          ·
            refine ⟨607721453713666635781745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405147635809111090521163 607721453713666635781745)
            ·
              refine ⟨455791090285249976836309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607721453713666635781745 455791090285249976836309)
              ·
                refine ⟨10682603678560546332101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 455791090285249976836309 10682603678560546332101)
                ·
                  rfl

theorem cell22_280858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_280858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280858 prefixEnd_280858 := by exact prefixLift 280858
  have htrace : WordTrace (prefixWord ++ tailWord_280858) baseStart_280858 baseEnd_280858 := by
    simpa [prefixWord, tailWord_280858, baseEnd_280858] using wordTrace_append hprefix tailTrace_280858
  have hstable : (prefixWord ++ tailWord_280858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280858).length < 2 ^ (prefixWord ++ tailWord_280858).sum := by decide
  have hdescent : baseEnd_280858 < baseStart_280858 := by decide
  rcases family_descends (prefixWord ++ tailWord_280858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280877 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_280877 : Nat := 118140960795 + 280877 * 2 ^ 59
def prefixEnd_280877 : Nat := 4983230072969 + 3 ^ 40 * 280877 * 2
def baseEnd_280877 : Nat := 96149937195335200763851

theorem tailTrace_280877 : CollatzResearch.WordTrace tailWord_280877 prefixEnd_280877 96149937195335200763851 := by
  unfold tailWord_280877
  simp only [CollatzResearch.WordTrace]
  refine ⟨10244425803438073817624885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6829617202292049211749923 10244425803438073817624885)
  ·
    refine ⟨960414919072319420402333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10244425803438073817624885 960414919072319420402333)
    ·
      refine ⟨360155594652119782650875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 960414919072319420402333 360155594652119782650875)
      ·
        refine ⟨540233391978179673976313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360155594652119782650875 540233391978179673976313)
        ·
          refine ⟨405175043983634755482235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540233391978179673976313 405175043983634755482235)
          ·
            refine ⟨607762565975452133223353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405175043983634755482235 607762565975452133223353)
            ·
              refine ⟨455821924481589099917515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607762565975452133223353 455821924481589099917515)
              ·
                refine ⟨683732886722383649876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455821924481589099917515 683732886722383649876273)
                ·
                  refine ⟨512799665041787737407205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683732886722383649876273 512799665041787737407205)
                  ·
                    refine ⟨96149937195335200763851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512799665041787737407205 96149937195335200763851)
                    ·
                      rfl

theorem cell22_280877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_280877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280877 prefixEnd_280877 := by exact prefixLift 280877
  have htrace : WordTrace (prefixWord ++ tailWord_280877) baseStart_280877 baseEnd_280877 := by
    simpa [prefixWord, tailWord_280877, baseEnd_280877] using wordTrace_append hprefix tailTrace_280877
  have hstable : (prefixWord ++ tailWord_280877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280877).length < 2 ^ (prefixWord ++ tailWord_280877).sum := by decide
  have hdescent : baseEnd_280877 < baseStart_280877 := by decide
  rcases family_descends (prefixWord ++ tailWord_280877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280903 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 5]
def baseStart_280903 : Nat := 118140960795 + 280903 * 2 ^ 59
def prefixEnd_280903 : Nat := 4983230072969 + 3 ^ 40 * 280903 * 2
def baseEnd_280903 : Nat := 32052945842226599871257

theorem tailTrace_280903 : CollatzResearch.WordTrace tailWord_280903 prefixEnd_280903 32052945842226599871257 := by
  unfold tailWord_280903
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245374101343880258071363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6830249400895920172047575 10245374101343880258071363)
  ·
    refine ⟨15368061152015820387107045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245374101343880258071363 15368061152015820387107045)
    ·
      refine ⟨2881511466002966322582571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15368061152015820387107045 2881511466002966322582571)
      ·
        refine ⟨4322267199004449483873857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881511466002966322582571 4322267199004449483873857)
        ·
          refine ⟨3241700399253337112905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4322267199004449483873857 3241700399253337112905393)
          ·
            refine ⟨2431275299440002834679045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241700399253337112905393 2431275299440002834679045)
            ·
              refine ⟨455864118645000531502321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2431275299440002834679045 455864118645000531502321)
              ·
                refine ⟨341898088983750398626741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455864118645000531502321 341898088983750398626741)
                ·
                  refine ⟨32052945842226599871257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341898088983750398626741 32052945842226599871257)
                  ·
                    rfl

theorem cell22_280903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 5].length) (baseStart_280903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280903 prefixEnd_280903 := by exact prefixLift 280903
  have htrace : WordTrace (prefixWord ++ tailWord_280903) baseStart_280903 baseEnd_280903 := by
    simpa [prefixWord, tailWord_280903, baseEnd_280903] using wordTrace_append hprefix tailTrace_280903
  have hstable : (prefixWord ++ tailWord_280903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280903).length < 2 ^ (prefixWord ++ tailWord_280903).sum := by decide
  have hdescent : baseEnd_280903 < baseStart_280903 := by decide
  rcases family_descends (prefixWord ++ tailWord_280903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280926 : List Nat := [4, 4, 2, 1, 1, 1, 3, 6]
def baseStart_280926 : Nat := 118140960795 + 280926 * 2 ^ 59
def prefixEnd_280926 : Nat := 4983230072969 + 3 ^ 40 * 280926 * 2
def baseEnd_280926 : Nat := 10685190099635045143189

theorem tailTrace_280926 : CollatzResearch.WordTrace tailWord_280926 prefixEnd_280926 10685190099635045143189 := by
  unfold tailWord_280926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280776622532569398269829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6830808653507036790772421 1280776622532569398269829)
  ·
    refine ⟨240145616724856762175593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1280776622532569398269829 240145616724856762175593)
    ·
      refine ⟨180109212543642571631695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240145616724856762175593 180109212543642571631695)
      ·
        refine ⟨270163818815463857447543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180109212543642571631695 270163818815463857447543)
        ·
          refine ⟨405245728223195786171315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270163818815463857447543 405245728223195786171315)
          ·
            refine ⟨607868592334793679256973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405245728223195786171315 607868592334793679256973)
            ·
              refine ⟨227950722125547629721365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607868592334793679256973 227950722125547629721365)
              ·
                refine ⟨10685190099635045143189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227950722125547629721365 10685190099635045143189)
                ·
                  rfl

theorem cell22_280926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_280926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280926 prefixEnd_280926 := by exact prefixLift 280926
  have htrace : WordTrace (prefixWord ++ tailWord_280926) baseStart_280926 baseEnd_280926 := by
    simpa [prefixWord, tailWord_280926, baseEnd_280926] using wordTrace_append hprefix tailTrace_280926
  have hstable : (prefixWord ++ tailWord_280926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280926).length < 2 ^ (prefixWord ++ tailWord_280926).sum := by decide
  have hdescent : baseEnd_280926 < baseStart_280926 := by decide
  rcases family_descends (prefixWord ++ tailWord_280926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280933 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_280933 : Nat := 118140960795 + 280933 * 2 ^ 59
def prefixEnd_280933 : Nat := 4983230072969 + 3 ^ 40 * 280933 * 2
def baseEnd_280933 : Nat := 96169107139769721363679

theorem tailTrace_280933 : CollatzResearch.WordTrace tailWord_280933 prefixEnd_280933 96169107139769721363679 := by
  unfold tailWord_280933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10246468291235195381663453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6830978860823463587775635 10246468291235195381663453)
  ·
    refine ⟨3842425609213198268123795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10246468291235195381663453 3842425609213198268123795)
    ·
      refine ⟨5763638413819797402185693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842425609213198268123795 5763638413819797402185693)
      ·
        refine ⟨2161364405182424025819635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5763638413819797402185693 2161364405182424025819635)
        ·
          refine ⟨3242046607773636038729453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161364405182424025819635 3242046607773636038729453)
          ·
            refine ⟨1215767477915113514523545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3242046607773636038729453 1215767477915113514523545)
            ·
              refine ⟨911825608436335135892659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215767477915113514523545 911825608436335135892659)
              ·
                refine ⟨1367738412654502703838989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911825608436335135892659 1367738412654502703838989)
                ·
                  refine ⟨512901904745438513939621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1367738412654502703838989 512901904745438513939621)
                  ·
                    refine ⟨96169107139769721363679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 512901904745438513939621 96169107139769721363679)
                    ·
                      rfl

theorem cell22_280933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_280933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_280933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_280933 prefixEnd_280933 := by exact prefixLift 280933
  have htrace : WordTrace (prefixWord ++ tailWord_280933) baseStart_280933 baseEnd_280933 := by
    simpa [prefixWord, tailWord_280933, baseEnd_280933] using wordTrace_append hprefix tailTrace_280933
  have hstable : (prefixWord ++ tailWord_280933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280933).length < 2 ^ (prefixWord ++ tailWord_280933).sum := by decide
  have hdescent : baseEnd_280933 < baseStart_280933 := by decide
  rcases family_descends (prefixWord ++ tailWord_280933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281100 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_281100 : Nat := 118140960795 + 281100 * 2 ^ 59
def prefixEnd_281100 : Nat := 4983230072969 + 3 ^ 40 * 281100 * 2
def baseEnd_281100 : Nat := 32075424884212317479389

theorem tailTrace_281100 : CollatzResearch.WordTrace tailWord_281100 prefixEnd_281100 32075424884212317479389 := by
  unfold tailWord_281100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126279640815091451496377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6835039521086788601995169 5126279640815091451496377)
  ·
    refine ⟨3844709730611318588622283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5126279640815091451496377 3844709730611318588622283)
    ·
      refine ⟨5767064595916977882933425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3844709730611318588622283 5767064595916977882933425)
      ·
        refine ⟨4325298446937733412200069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5767064595916977882933425 4325298446937733412200069)
        ·
          refine ⟨810993458800825014787513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4325298446937733412200069 810993458800825014787513)
          ·
            refine ⟨608245094100618761090635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810993458800825014787513 608245094100618761090635)
            ·
              refine ⟨912367641150928141635953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608245094100618761090635 912367641150928141635953)
              ·
                refine ⟨684275730863196106226965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912367641150928141635953 684275730863196106226965)
                ·
                  refine ⟨32075424884212317479389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 684275730863196106226965 32075424884212317479389)
                  ·
                    rfl

theorem cell22_281100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_281100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281100 prefixEnd_281100 := by exact prefixLift 281100
  have htrace : WordTrace (prefixWord ++ tailWord_281100) baseStart_281100 baseEnd_281100 := by
    simpa [prefixWord, tailWord_281100, baseEnd_281100] using wordTrace_append hprefix tailTrace_281100
  have hstable : (prefixWord ++ tailWord_281100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281100).length < 2 ^ (prefixWord ++ tailWord_281100).sum := by decide
  have hdescent : baseEnd_281100 < baseStart_281100 := by decide
  rcases family_descends (prefixWord ++ tailWord_281100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281113 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_281113 : Nat := 118140960795 + 281113 * 2 ^ 59
def prefixEnd_281113 : Nat := 4983230072969 + 3 ^ 40 * 281113 * 2
def baseEnd_281113 : Nat := 96230724818309251863127

theorem tailTrace_281113 : CollatzResearch.WordTrace tailWord_281113 prefixEnd_281113 96230724818309251863127 := by
  unfold tailWord_281113
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253033430583086123215993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835355620388724082143995 10253033430583086123215993)
  ·
    refine ⟨7689775072937314592411995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10253033430583086123215993 7689775072937314592411995)
    ·
      refine ⟨11534662609405971888617993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689775072937314592411995 11534662609405971888617993)
      ·
        refine ⟨8650996957054478916463495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11534662609405971888617993 8650996957054478916463495)
        ·
          refine ⟨12976495435581718374695243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8650996957054478916463495 12976495435581718374695243)
          ·
            refine ⟨19464743153372577562042865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12976495435581718374695243 19464743153372577562042865)
            ·
              refine ⟨14598557365029433171532149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19464743153372577562042865 14598557365029433171532149)
              ·
                refine ⟨1368614752971509359831139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14598557365029433171532149 1368614752971509359831139)
                ·
                  refine ⟨2052922129457264039746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368614752971509359831139 2052922129457264039746709)
                  ·
                    refine ⟨96230724818309251863127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2052922129457264039746709 96230724818309251863127)
                    ·
                      rfl

theorem cell22_281113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_281113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281113 prefixEnd_281113 := by exact prefixLift 281113
  have htrace : WordTrace (prefixWord ++ tailWord_281113) baseStart_281113 baseEnd_281113 := by
    simpa [prefixWord, tailWord_281113, baseEnd_281113] using wordTrace_append hprefix tailTrace_281113
  have hstable : (prefixWord ++ tailWord_281113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281113).length < 2 ^ (prefixWord ++ tailWord_281113).sum := by decide
  have hdescent : baseEnd_281113 < baseStart_281113 := by decide
  rcases family_descends (prefixWord ++ tailWord_281113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281117 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 4]
def baseStart_281117 : Nat := 118140960795 + 281117 * 2 ^ 59
def prefixEnd_281117 : Nat := 4983230072969 + 3 ^ 40 * 281117 * 2
def baseEnd_281117 : Nat := 32077364700018191587705

theorem tailTrace_281117 : CollatzResearch.WordTrace tailWord_281117 prefixEnd_281117 32077364700018191587705 := by
  unfold tailWord_281117
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253179322568594806361605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835452881712396537574403 10253179322568594806361605)
  ·
    refine ⟨1922471122981611526192801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10253179322568594806361605 1922471122981611526192801)
    ·
      refine ⟨1441853342236208644644601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1922471122981611526192801 1441853342236208644644601)
      ·
        refine ⟨1081390006677156483483451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1441853342236208644644601 1081390006677156483483451)
        ·
          refine ⟨1622085010015734725225177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081390006677156483483451 1622085010015734725225177)
          ·
            refine ⟨1216563757511801043918883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622085010015734725225177 1216563757511801043918883)
            ·
              refine ⟨1824845636267701565878325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216563757511801043918883 1824845636267701565878325)
              ·
                refine ⟨171079278400097021801093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1824845636267701565878325 171079278400097021801093)
                ·
                  refine ⟨32077364700018191587705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171079278400097021801093 32077364700018191587705)
                  ·
                    rfl

theorem cell22_281117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_281117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281117 prefixEnd_281117 := by exact prefixLift 281117
  have htrace : WordTrace (prefixWord ++ tailWord_281117) baseStart_281117 baseEnd_281117 := by
    simpa [prefixWord, tailWord_281117, baseEnd_281117] using wordTrace_append hprefix tailTrace_281117
  have hstable : (prefixWord ++ tailWord_281117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281117).length < 2 ^ (prefixWord ++ tailWord_281117).sum := by decide
  have hdescent : baseEnd_281117 < baseStart_281117 := by decide
  rcases family_descends (prefixWord ++ tailWord_281117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281162 : List Nat := [3, 1, 2, 1, 1, 6, 2, 6]
def baseStart_281162 : Nat := 118140960795 + 281162 * 2 ^ 59
def prefixEnd_281162 : Nat := 4983230072969 + 3 ^ 40 * 281162 * 2
def baseEnd_281162 : Nat := 10694166502187717487553

theorem tailTrace_281162 : CollatzResearch.WordTrace tailWord_281162 prefixEnd_281162 10694166502187717487553 := by
  unfold tailWord_281162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563705151851391872937435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6836547071603711661166493 2563705151851391872937435)
  ·
    refine ⟨3845557727777087809406153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563705151851391872937435 3845557727777087809406153)
    ·
      refine ⟨2884168295832815857054615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3845557727777087809406153 2884168295832815857054615)
      ·
        refine ⟨4326252443749223785581923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884168295832815857054615 4326252443749223785581923)
        ·
          refine ⟨6489378665623835678372885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326252443749223785581923 6489378665623835678372885)
          ·
            refine ⟨304189624951117297423729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6489378665623835678372885 304189624951117297423729)
            ·
              refine ⟨228142218713337973067797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304189624951117297423729 228142218713337973067797)
              ·
                refine ⟨10694166502187717487553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228142218713337973067797 10694166502187717487553)
                ·
                  rfl

theorem cell22_281162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_281162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281162 prefixEnd_281162 := by exact prefixLift 281162
  have htrace : WordTrace (prefixWord ++ tailWord_281162) baseStart_281162 baseEnd_281162 := by
    simpa [prefixWord, tailWord_281162, baseEnd_281162] using wordTrace_append hprefix tailTrace_281162
  have hstable : (prefixWord ++ tailWord_281162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281162).length < 2 ^ (prefixWord ++ tailWord_281162).sum := by decide
  have hdescent : baseEnd_281162 < baseStart_281162 := by decide
  rcases family_descends (prefixWord ++ tailWord_281162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281207 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 5]
def baseStart_281207 : Nat := 118140960795 + 281207 * 2 ^ 59
def prefixEnd_281207 : Nat := 4983230072969 + 3 ^ 40 * 281207 * 2
def baseEnd_281207 : Nat := 32087634313108113337613

theorem tailTrace_281207 : CollatzResearch.WordTrace tailWord_281207 prefixEnd_281207 32087634313108113337613 := by
  unfold tailWord_281207
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256461892242540177137875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837641261495026784758583 10256461892242540177137875)
  ·
    refine ⟨15384692838363810265706813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10256461892242540177137875 15384692838363810265706813)
    ·
      refine ⟨5769259814386428849640055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15384692838363810265706813 5769259814386428849640055)
      ·
        refine ⟨8653889721579643274460083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769259814386428849640055 8653889721579643274460083)
        ·
          refine ⟨12980834582369464911690125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8653889721579643274460083 12980834582369464911690125)
          ·
            refine ⟨4867812968388549341883797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12980834582369464911690125 4867812968388549341883797)
            ·
              refine ⟨228178732893213250400803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4867812968388549341883797 228178732893213250400803)
              ·
                refine ⟨342268099339819875601205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228178732893213250400803 342268099339819875601205)
                ·
                  refine ⟨32087634313108113337613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 342268099339819875601205 32087634313108113337613)
                  ·
                    rfl

theorem cell22_281207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 5].length) (baseStart_281207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281207 prefixEnd_281207 := by exact prefixLift 281207
  have htrace : WordTrace (prefixWord ++ tailWord_281207) baseStart_281207 baseEnd_281207 := by
    simpa [prefixWord, tailWord_281207, baseEnd_281207] using wordTrace_append hprefix tailTrace_281207
  have hstable : (prefixWord ++ tailWord_281207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281207).length < 2 ^ (prefixWord ++ tailWord_281207).sum := by decide
  have hdescent : baseEnd_281207 < baseStart_281207 := by decide
  rcases family_descends (prefixWord ++ tailWord_281207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281267 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_281267 : Nat := 118140960795 + 281267 * 2 ^ 59
def prefixEnd_281267 : Nat := 4983230072969 + 3 ^ 40 * 281267 * 2
def baseEnd_281267 : Nat := 96283442165504183512655

theorem tailTrace_281267 : CollatzResearch.WordTrace tailWord_281267 prefixEnd_281267 96283442165504183512655 := by
  unfold tailWord_281267
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258650272025170424322055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6839100181350113616214703 10258650272025170424322055)
  ·
    refine ⟨15387975408037755636483083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258650272025170424322055 15387975408037755636483083)
    ·
      refine ⟨23081963112056633454724625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387975408037755636483083 23081963112056633454724625)
      ·
        refine ⟨17311472334042475091043469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23081963112056633454724625 17311472334042475091043469)
        ·
          refine ⟨6491802125265928159141301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17311472334042475091043469 6491802125265928159141301)
          ·
            refine ⟨608606449243680764919497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6491802125265928159141301 608606449243680764919497)
            ·
              refine ⟨456454836932760573689623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608606449243680764919497 456454836932760573689623)
              ·
                refine ⟨684682255399140860534435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456454836932760573689623 684682255399140860534435)
                ·
                  refine ⟨1027023383098711290801653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684682255399140860534435 1027023383098711290801653)
                  ·
                    refine ⟨96283442165504183512655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1027023383098711290801653 96283442165504183512655)
                    ·
                      rfl

theorem cell22_281267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_281267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281267 prefixEnd_281267 := by exact prefixLift 281267
  have htrace : WordTrace (prefixWord ++ tailWord_281267) baseStart_281267 baseEnd_281267 := by
    simpa [prefixWord, tailWord_281267, baseEnd_281267] using wordTrace_append hprefix tailTrace_281267
  have hstable : (prefixWord ++ tailWord_281267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281267).length < 2 ^ (prefixWord ++ tailWord_281267).sum := by decide
  have hdescent : baseEnd_281267 < baseStart_281267 := by decide
  rcases family_descends (prefixWord ++ tailWord_281267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281301 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_281301 : Nat := 118140960795 + 281301 * 2 ^ 59
def prefixEnd_281301 : Nat := 4983230072969 + 3 ^ 40 * 281301 * 2
def baseEnd_281301 : Nat := 96295081060339428162551

theorem tailTrace_281301 : CollatzResearch.WordTrace tailWord_281301 prefixEnd_281301 96295081060339428162551 := by
  unfold tailWord_281301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259890353901994231059757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6839926902601329487373171 10259890353901994231059757)
  ·
    refine ⟨3847458882713247836647409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10259890353901994231059757 3847458882713247836647409)
    ·
      refine ⟨2885594162034935877485557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3847458882713247836647409 2885594162034935877485557)
      ·
        refine ⟨270524452690775238514271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2885594162034935877485557 270524452690775238514271)
        ·
          refine ⟨405786679036162857771407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270524452690775238514271 405786679036162857771407)
          ·
            refine ⟨608680018554244286657111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405786679036162857771407 608680018554244286657111)
            ·
              refine ⟨913020027831366429985667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608680018554244286657111 913020027831366429985667)
              ·
                refine ⟨1369530041747049644978501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913020027831366429985667 1369530041747049644978501)
                ·
                  refine ⟨256786882827571808433469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369530041747049644978501 256786882827571808433469)
                  ·
                    refine ⟨96295081060339428162551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256786882827571808433469 96295081060339428162551)
                    ·
                      rfl

theorem cell22_281301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_281301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281301 prefixEnd_281301 := by exact prefixLift 281301
  have htrace : WordTrace (prefixWord ++ tailWord_281301) baseStart_281301 baseEnd_281301 := by
    simpa [prefixWord, tailWord_281301, baseEnd_281301] using wordTrace_append hprefix tailTrace_281301
  have hstable : (prefixWord ++ tailWord_281301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281301).length < 2 ^ (prefixWord ++ tailWord_281301).sum := by decide
  have hdescent : baseEnd_281301 < baseStart_281301 := by decide
  rcases family_descends (prefixWord ++ tailWord_281301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281376 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_281376 : Nat := 118140960795 + 281376 * 2 ^ 59
def prefixEnd_281376 : Nat := 4983230072969 + 3 ^ 40 * 281376 * 2
def baseEnd_281376 : Nat := 32106918364354744179107

theorem tailTrace_281376 : CollatzResearch.WordTrace tailWord_281376 prefixEnd_281376 32106918364354744179107 := by
  unfold tailWord_281376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131312914315141020019991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6841750552420188026693321 5131312914315141020019991)
  ·
    refine ⟨7696969371472711530029987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5131312914315141020019991 7696969371472711530029987)
    ·
      refine ⟨11545454057209067295044981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7696969371472711530029987 11545454057209067295044981)
      ·
        refine ⟨1082386317863350058910467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11545454057209067295044981 1082386317863350058910467)
        ·
          refine ⟨1623579476795025088365701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082386317863350058910467 1623579476795025088365701)
          ·
            refine ⟨304421151899067204068569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1623579476795025088365701 304421151899067204068569)
            ·
              refine ⟨228315863924300403051427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304421151899067204068569 228315863924300403051427)
              ·
                refine ⟨342473795886450604577141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228315863924300403051427 342473795886450604577141)
                ·
                  refine ⟨32106918364354744179107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 342473795886450604577141 32106918364354744179107)
                  ·
                    rfl

theorem cell22_281376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_281376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281376 prefixEnd_281376 := by exact prefixLift 281376
  have htrace : WordTrace (prefixWord ++ tailWord_281376) baseStart_281376 baseEnd_281376 := by
    simpa [prefixWord, tailWord_281376, baseEnd_281376] using wordTrace_append hprefix tailTrace_281376
  have hstable : (prefixWord ++ tailWord_281376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281376).length < 2 ^ (prefixWord ++ tailWord_281376).sum := by decide
  have hdescent : baseEnd_281376 < baseStart_281376 := by decide
  rcases family_descends (prefixWord ++ tailWord_281376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281404 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_281404 : Nat := 118140960795 + 281404 * 2 ^ 59
def prefixEnd_281404 : Nat := 4983230072969 + 3 ^ 40 * 281404 * 2
def baseEnd_281404 : Nat := 32110113355093830945745

theorem tailTrace_281404 : CollatzResearch.WordTrace tailWord_281404 prefixEnd_281404 32110113355093830945745 := by
  unfold tailWord_281404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131823536264421411029633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6842431381685895214706177 5131823536264421411029633)
  ·
    refine ⟨3848867652198316058272225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5131823536264421411029633 3848867652198316058272225)
    ·
      refine ⟨2886650739148737043704169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3848867652198316058272225 2886650739148737043704169)
      ·
        refine ⟨2164988054361552782778127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2886650739148737043704169 2164988054361552782778127)
        ·
          refine ⟨3247482081542329174167191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164988054361552782778127 3247482081542329174167191)
          ·
            refine ⟨4871223122313493761250787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247482081542329174167191 4871223122313493761250787)
            ·
              refine ⟨7306834683470240641876181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871223122313493761250787 7306834683470240641876181)
              ·
                refine ⟨171253937893833765043973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7306834683470240641876181 171253937893833765043973)
                ·
                  refine ⟨32110113355093830945745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171253937893833765043973 32110113355093830945745)
                  ·
                    rfl

theorem cell22_281404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_281404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281404 prefixEnd_281404 := by exact prefixLift 281404
  have htrace : WordTrace (prefixWord ++ tailWord_281404) baseStart_281404 baseEnd_281404 := by
    simpa [prefixWord, tailWord_281404, baseEnd_281404] using wordTrace_append hprefix tailTrace_281404
  have hstable : (prefixWord ++ tailWord_281404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281404).length < 2 ^ (prefixWord ++ tailWord_281404).sum := by decide
  have hdescent : baseEnd_281404 < baseStart_281404 := by decide
  rcases family_descends (prefixWord ++ tailWord_281404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281414 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_281414 : Nat := 118140960795 + 281414 * 2 ^ 59
def prefixEnd_281414 : Nat := 4983230072969 + 3 ^ 40 * 281414 * 2
def baseEnd_281414 : Nat := 96333763269644800087205

theorem tailTrace_281414 : CollatzResearch.WordTrace tailWord_281414 prefixEnd_281414 96333763269644800087205 := by
  unfold tailWord_281414
  simp only [CollatzResearch.WordTrace]
  refine ⟨320750368827894204060103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6842674534995076353282197 320750368827894204060103)
  ·
    refine ⟨481125553241841306090155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320750368827894204060103 481125553241841306090155)
    ·
      refine ⟨721688329862761959135233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481125553241841306090155 721688329862761959135233)
      ·
        refine ⟨541266247397071469351425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 721688329862761959135233 541266247397071469351425)
        ·
          refine ⟨405949685547803602013569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541266247397071469351425 405949685547803602013569)
          ·
            refine ⟨304462264160852701510177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405949685547803602013569 304462264160852701510177)
            ·
              refine ⟨228346698120639526132633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304462264160852701510177 228346698120639526132633)
              ·
                refine ⟨171260023590479644599475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228346698120639526132633 171260023590479644599475)
                ·
                  refine ⟨256890035385719466899213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171260023590479644599475 256890035385719466899213)
                  ·
                    refine ⟨96333763269644800087205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256890035385719466899213 96333763269644800087205)
                    ·
                      rfl

theorem cell22_281414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_281414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281414 prefixEnd_281414 := by exact prefixLift 281414
  have htrace : WordTrace (prefixWord ++ tailWord_281414) baseStart_281414 baseEnd_281414 := by
    simpa [prefixWord, tailWord_281414, baseEnd_281414] using wordTrace_append hprefix tailTrace_281414
  have hstable : (prefixWord ++ tailWord_281414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281414).length < 2 ^ (prefixWord ++ tailWord_281414).sum := by decide
  have hdescent : baseEnd_281414 < baseStart_281414 := by decide
  rcases family_descends (prefixWord ++ tailWord_281414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281436 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_281436 : Nat := 118140960795 + 281436 * 2 ^ 59
def prefixEnd_281436 : Nat := 4983230072969 + 3 ^ 40 * 281436 * 2
def baseEnd_281436 : Nat := 96341294319244076037137

theorem tailTrace_281436 : CollatzResearch.WordTrace tailWord_281436 prefixEnd_281436 96341294319244076037137 := by
  unfold tailWord_281436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132407104206456143612081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6843209472275274858149441 5132407104206456143612081)
  ·
    refine ⟨3849305328154842107709061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5132407104206456143612081 3849305328154842107709061)
    ·
      refine ⟨721744749029032895195449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3849305328154842107709061 721744749029032895195449)
      ·
        refine ⟨541308561771774671396587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 721744749029032895195449 541308561771774671396587)
        ·
          refine ⟨811962842657662007094881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541308561771774671396587 811962842657662007094881)
          ·
            refine ⟨608972131993246505321161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811962842657662007094881 608972131993246505321161)
            ·
              refine ⟨456729098994934878990871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608972131993246505321161 456729098994934878990871)
              ·
                refine ⟨685093648492402318486307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456729098994934878990871 685093648492402318486307)
                ·
                  refine ⟨1027640472738603477729461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685093648492402318486307 1027640472738603477729461)
                  ·
                    refine ⟨96341294319244076037137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1027640472738603477729461 96341294319244076037137)
                    ·
                      rfl

theorem cell22_281436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_281436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281436 prefixEnd_281436 := by exact prefixLift 281436
  have htrace : WordTrace (prefixWord ++ tailWord_281436) baseStart_281436 baseEnd_281436 := by
    simpa [prefixWord, tailWord_281436, baseEnd_281436] using wordTrace_append hprefix tailTrace_281436
  have hstable : (prefixWord ++ tailWord_281436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281436).length < 2 ^ (prefixWord ++ tailWord_281436).sum := by decide
  have hdescent : baseEnd_281436 < baseStart_281436 := by decide
  rcases family_descends (prefixWord ++ tailWord_281436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281481 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_281481 : Nat := 118140960795 + 281481 * 2 ^ 59
def prefixEnd_281481 : Nat := 4983230072969 + 3 ^ 40 * 281481 * 2
def baseEnd_281481 : Nat := 96356698738878958661999

theorem tailTrace_281481 : CollatzResearch.WordTrace tailWord_281481 prefixEnd_281481 96356698738878958661999 := by
  unfold tailWord_281481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10266455493249884972612297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6844303662166589981741531 10266455493249884972612297)
  ·
    refine ⟨7699841619937413729459223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10266455493249884972612297 7699841619937413729459223)
    ·
      refine ⟨11549762429906120594188835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7699841619937413729459223 11549762429906120594188835)
      ·
        refine ⟨17324643644859180891283253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11549762429906120594188835 17324643644859180891283253)
        ·
          refine ⟨1624185341705548208557805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17324643644859180891283253 1624185341705548208557805)
          ·
            refine ⟨609069503139580578209177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1624185341705548208557805 609069503139580578209177)
            ·
              refine ⟨456802127354685433656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609069503139580578209177 456802127354685433656883)
              ·
                refine ⟨685203191032028150485325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456802127354685433656883 685203191032028150485325)
                ·
                  refine ⟨256951196637010556431997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685203191032028150485325 256951196637010556431997)
                  ·
                    refine ⟨96356698738878958661999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256951196637010556431997 96356698738878958661999)
                    ·
                      rfl

theorem cell22_281481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_281481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281481 prefixEnd_281481 := by exact prefixLift 281481
  have htrace : WordTrace (prefixWord ++ tailWord_281481) baseStart_281481 baseEnd_281481 := by
    simpa [prefixWord, tailWord_281481, baseEnd_281481] using wordTrace_append hprefix tailTrace_281481
  have hstable : (prefixWord ++ tailWord_281481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281481).length < 2 ^ (prefixWord ++ tailWord_281481).sum := by decide
  have hdescent : baseEnd_281481 < baseStart_281481 := by decide
  rcases family_descends (prefixWord ++ tailWord_281481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281558 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_281558 : Nat := 118140960795 + 281558 * 2 ^ 59
def prefixEnd_281558 : Nat := 4983230072969 + 3 ^ 40 * 281558 * 2
def baseEnd_281558 : Nat := 96383057412476424486763

theorem tailTrace_281558 : CollatzResearch.WordTrace tailWord_281558 prefixEnd_281558 96383057412476424486763 := by
  unfold tailWord_281558
  simp only [CollatzResearch.WordTrace]
  refine ⟨641828994623182945197833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6846175942647284748776885 641828994623182945197833)
  ·
    refine ⟨481371745967387208898375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 641828994623182945197833 481371745967387208898375)
    ·
      refine ⟨722057618951080813347563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481371745967387208898375 722057618951080813347563)
      ·
        refine ⟨1083086428426621220021345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722057618951080813347563 1083086428426621220021345)
        ·
          refine ⟨812314821319965915016009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083086428426621220021345 812314821319965915016009)
          ·
            refine ⟨609236115989974436262007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812314821319965915016009 609236115989974436262007)
            ·
              refine ⟨913854173984961654393011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609236115989974436262007 913854173984961654393011)
              ·
                refine ⟨1370781260977442481589517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913854173984961654393011 1370781260977442481589517)
                ·
                  refine ⟨514042972866540930596069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1370781260977442481589517 514042972866540930596069)
                  ·
                    refine ⟨96383057412476424486763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514042972866540930596069 96383057412476424486763)
                    ·
                      rfl

theorem cell22_281558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_281558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281558 prefixEnd_281558 := by exact prefixLift 281558
  have htrace : WordTrace (prefixWord ++ tailWord_281558) baseStart_281558 baseEnd_281558 := by
    simpa [prefixWord, tailWord_281558, baseEnd_281558] using wordTrace_append hprefix tailTrace_281558
  have hstable : (prefixWord ++ tailWord_281558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281558).length < 2 ^ (prefixWord ++ tailWord_281558).sum := by decide
  have hdescent : baseEnd_281558 < baseStart_281558 := by decide
  rcases family_descends (prefixWord ++ tailWord_281558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281590 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_281590 : Nat := 118140960795 + 281590 * 2 ^ 59
def prefixEnd_281590 : Nat := 4983230072969 + 3 ^ 40 * 281590 * 2
def baseEnd_281590 : Nat := 32131337222146335895555

theorem tailTrace_281590 : CollatzResearch.WordTrace tailWord_281590 prefixEnd_281590 32131337222146335895555 := by
  unfold tailWord_281590
  simp only [CollatzResearch.WordTrace]
  refine ⟨641901940615937286770639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6846954033236664392220149 641901940615937286770639)
  ·
    refine ⟨962852910923905930155959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 641901940615937286770639 962852910923905930155959)
    ·
      refine ⟨1444279366385858895233939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962852910923905930155959 1444279366385858895233939)
      ·
        refine ⟨2166419049578788342850909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444279366385858895233939 2166419049578788342850909)
        ·
          refine ⟨812407143592045628569091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2166419049578788342850909 812407143592045628569091)
          ·
            refine ⟨1218610715388068442853637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812407143592045628569091 1218610715388068442853637)
            ·
              refine ⟨228489509135262833035057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1218610715388068442853637 228489509135262833035057)
              ·
                refine ⟨171367131851447124776293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228489509135262833035057 171367131851447124776293)
                ·
                  refine ⟨32131337222146335895555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171367131851447124776293 32131337222146335895555)
                  ·
                    rfl

theorem cell22_281590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_281590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281590 prefixEnd_281590 := by exact prefixLift 281590
  have htrace : WordTrace (prefixWord ++ tailWord_281590) baseStart_281590 baseEnd_281590 := by
    simpa [prefixWord, tailWord_281590, baseEnd_281590] using wordTrace_append hprefix tailTrace_281590
  have hstable : (prefixWord ++ tailWord_281590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281590).length < 2 ^ (prefixWord ++ tailWord_281590).sum := by decide
  have hdescent : baseEnd_281590 < baseStart_281590 := by decide
  rcases family_descends (prefixWord ++ tailWord_281590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281601 : List Nat := [1, 2, 4, 1, 2, 4, 1, 7]
def baseStart_281601 : Nat := 118140960795 + 281601 * 2 ^ 59
def prefixEnd_281601 : Nat := 4983230072969 + 3 ^ 40 * 281601 * 2
def baseEnd_281601 : Nat := 10710864132359849517959

theorem tailTrace_281601 : CollatzResearch.WordTrace tailWord_281601 prefixEnd_281601 10710864132359849517959 := by
  unfold tailWord_281601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10270832252815145466980657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6847221501876763644653771 10270832252815145466980657)
  ·
    refine ⟨7703124189611359100235493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10270832252815145466980657 7703124189611359100235493)
    ·
      refine ⟨1444335785552129831294155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7703124189611359100235493 1444335785552129831294155)
      ·
        refine ⟨2166503678328194746941233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444335785552129831294155 2166503678328194746941233)
        ·
          refine ⟨1624877758746146060205925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166503678328194746941233 1624877758746146060205925)
          ·
            refine ⟨304664579764902386288611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1624877758746146060205925 304664579764902386288611)
            ·
              refine ⟨456996869647353579432917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304664579764902386288611 456996869647353579432917)
              ·
                refine ⟨10710864132359849517959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 456996869647353579432917 10710864132359849517959)
                ·
                  rfl

theorem cell22_281601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 7].length) (baseStart_281601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281601 prefixEnd_281601 := by exact prefixLift 281601
  have htrace : WordTrace (prefixWord ++ tailWord_281601) baseStart_281601 baseEnd_281601 := by
    simpa [prefixWord, tailWord_281601, baseEnd_281601] using wordTrace_append hprefix tailTrace_281601
  have hstable : (prefixWord ++ tailWord_281601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281601).length < 2 ^ (prefixWord ++ tailWord_281601).sum := by decide
  have hdescent : baseEnd_281601 < baseStart_281601 := by decide
  rcases family_descends (prefixWord ++ tailWord_281601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281644 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_281644 : Nat := 118140960795 + 281644 * 2 ^ 59
def prefixEnd_281644 : Nat := 4983230072969 + 3 ^ 40 * 281644 * 2
def baseEnd_281644 : Nat := 96412496970000866836499

theorem tailTrace_281644 : CollatzResearch.WordTrace tailWord_281644 prefixEnd_281644 96412496970000866836499 := by
  unfold tailWord_281644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136200295829681905397993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6848267061106242540530657 5136200295829681905397993)
  ·
    refine ⟨3852150221872261429048495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5136200295829681905397993 3852150221872261429048495)
    ·
      refine ⟨5778225332808392143572743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852150221872261429048495 5778225332808392143572743)
      ·
        refine ⟨8667337999212588215359115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778225332808392143572743 8667337999212588215359115)
        ·
          refine ⟨13001006998818882323038673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667337999212588215359115 13001006998818882323038673)
          ·
            refine ⟨9750755249114161742279005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13001006998818882323038673 9750755249114161742279005)
            ·
              refine ⟨3656533218417810653354627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9750755249114161742279005 3656533218417810653354627)
              ·
                refine ⟨5484799827626715980031941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656533218417810653354627 5484799827626715980031941)
                ·
                  refine ⟨1028399967680009246255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5484799827626715980031941 1028399967680009246255989)
                  ·
                    refine ⟨96412496970000866836499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1028399967680009246255989 96412496970000866836499)
                    ·
                      rfl

theorem cell22_281644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_281644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281644 prefixEnd_281644 := by exact prefixLift 281644
  have htrace : WordTrace (prefixWord ++ tailWord_281644) baseStart_281644 baseEnd_281644 := by
    simpa [prefixWord, tailWord_281644, baseEnd_281644] using wordTrace_append hprefix tailTrace_281644
  have hstable : (prefixWord ++ tailWord_281644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281644).length < 2 ^ (prefixWord ++ tailWord_281644).sum := by decide
  have hdescent : baseEnd_281644 < baseStart_281644 := by decide
  rcases family_descends (prefixWord ++ tailWord_281644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281646 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_281646 : Nat := 118140960795 + 281646 * 2 ^ 59
def prefixEnd_281646 : Nat := 4983230072969 + 3 ^ 40 * 281646 * 2
def baseEnd_281646 : Nat := 32137727203624509428831

theorem tailTrace_281646 : CollatzResearch.WordTrace tailWord_281646 prefixEnd_281646 32137727203624509428831 := by
  unfold tailWord_281646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284059192206514769046099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6848315691768078768245861 1284059192206514769046099)
  ·
    refine ⟨1926088788309772153569149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1284059192206514769046099 1926088788309772153569149)
    ·
      refine ⟨722283295616164557588431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1926088788309772153569149 722283295616164557588431)
      ·
        refine ⟨1083424943424246836382647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722283295616164557588431 1083424943424246836382647)
        ·
          refine ⟨1625137415136370254573971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083424943424246836382647 1625137415136370254573971)
          ·
            refine ⟨2437706122704555381860957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625137415136370254573971 2437706122704555381860957)
            ·
              refine ⟨914139796014208268197859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437706122704555381860957 914139796014208268197859)
              ·
                refine ⟨1371209694021312402296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914139796014208268197859 1371209694021312402296789)
                ·
                  refine ⟨32137727203624509428831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1371209694021312402296789 32137727203624509428831)
                  ·
                    rfl

theorem cell22_281646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_281646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281646 prefixEnd_281646 := by exact prefixLift 281646
  have htrace : WordTrace (prefixWord ++ tailWord_281646) baseStart_281646 baseEnd_281646 := by
    simpa [prefixWord, tailWord_281646, baseEnd_281646] using wordTrace_append hprefix tailTrace_281646
  have hstable : (prefixWord ++ tailWord_281646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281646).length < 2 ^ (prefixWord ++ tailWord_281646).sum := by decide
  have hdescent : baseEnd_281646 < baseStart_281646 := by decide
  rcases family_descends (prefixWord ++ tailWord_281646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281661 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_281661 : Nat := 118140960795 + 281661 * 2 ^ 59
def prefixEnd_281661 : Nat := 4983230072969 + 3 ^ 40 * 281661 * 2
def baseEnd_281661 : Nat := 96418316417418489161447

theorem tailTrace_281661 : CollatzResearch.WordTrace tailWord_281661 prefixEnd_281661 96418316417418489161447 := by
  unfold tailWord_281661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10273020632597775714164837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6848680421731850476109891 10273020632597775714164837)
  ·
    refine ⟨1926191368612082946405907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10273020632597775714164837 1926191368612082946405907)
    ·
      refine ⟨2889287052918124419608861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926191368612082946405907 2889287052918124419608861)
      ·
        refine ⟨1083482644844296657353323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2889287052918124419608861 1083482644844296657353323)
        ·
          refine ⟨1625223967266444986029985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083482644844296657353323 1625223967266444986029985)
          ·
            refine ⟨1218917975449833739522489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625223967266444986029985 1218917975449833739522489)
            ·
              refine ⟨914188481587375304641867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218917975449833739522489 914188481587375304641867)
              ·
                refine ⟨1371282722381062956962801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914188481587375304641867 1371282722381062956962801)
                ·
                  refine ⟨1028462041785797217722101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371282722381062956962801 1028462041785797217722101)
                  ·
                    refine ⟨96418316417418489161447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1028462041785797217722101 96418316417418489161447)
                    ·
                      rfl

theorem cell22_281661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_281661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281661 prefixEnd_281661 := by exact prefixLift 281661
  have htrace : WordTrace (prefixWord ++ tailWord_281661) baseStart_281661 baseEnd_281661 := by
    simpa [prefixWord, tailWord_281661, baseEnd_281661] using wordTrace_append hprefix tailTrace_281661
  have hstable : (prefixWord ++ tailWord_281661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281661).length < 2 ^ (prefixWord ++ tailWord_281661).sum := by decide
  have hdescent : baseEnd_281661 < baseStart_281661 := by decide
  rcases family_descends (prefixWord ++ tailWord_281661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281738 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_281738 : Nat := 118140960795 + 281738 * 2 ^ 59
def prefixEnd_281738 : Nat := 4983230072969 + 3 ^ 40 * 281738 * 2
def baseEnd_281738 : Nat := 96444675091015954986211

theorem tailTrace_281738 : CollatzResearch.WordTrace tailWord_281738 prefixEnd_281738 96444675091015954986211 := by
  unfold tailWord_281738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568957263329704466179467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6850552702212545243145245 2568957263329704466179467)
  ·
    refine ⟨3853435894994556699269201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568957263329704466179467 3853435894994556699269201)
    ·
      refine ⟨2890076921245917524451901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853435894994556699269201 2890076921245917524451901)
      ·
        refine ⟨1083778845467219071669463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2890076921245917524451901 1083778845467219071669463)
        ·
          refine ⟨1625668268200828607504195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083778845467219071669463 1625668268200828607504195)
          ·
            refine ⟨2438502402301242911256293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625668268200828607504195 2438502402301242911256293)
            ·
              refine ⟨457219200431483045860555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2438502402301242911256293 457219200431483045860555)
              ·
                refine ⟨685828800647224568790833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457219200431483045860555 685828800647224568790833)
                ·
                  refine ⟨514371600485418426593125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685828800647224568790833 514371600485418426593125)
                  ·
                    refine ⟨96444675091015954986211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514371600485418426593125 96444675091015954986211)
                    ·
                      rfl

theorem cell22_281738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_281738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281738 prefixEnd_281738 := by exact prefixLift 281738
  have htrace : WordTrace (prefixWord ++ tailWord_281738) baseStart_281738 baseEnd_281738 := by
    simpa [prefixWord, tailWord_281738, baseEnd_281738] using wordTrace_append hprefix tailTrace_281738
  have hstable : (prefixWord ++ tailWord_281738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281738).length < 2 ^ (prefixWord ++ tailWord_281738).sum := by decide
  have hdescent : baseEnd_281738 < baseStart_281738 := by decide
  rcases family_descends (prefixWord ++ tailWord_281738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281759 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 4]
def baseStart_281759 : Nat := 118140960795 + 281759 * 2 ^ 59
def prefixEnd_281759 : Nat := 4983230072969 + 3 ^ 40 * 281759 * 2
def baseEnd_281759 : Nat := 32150621273392966737049

theorem tailTrace_281759 : CollatzResearch.WordTrace tailWord_281759 prefixEnd_281759 32150621273392966737049 := by
  unfold tailWord_281759
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276594986242738451232331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6851063324161825634154887 10276594986242738451232331)
  ·
    refine ⟨15414892479364107676848497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10276594986242738451232331 15414892479364107676848497)
    ·
      refine ⟨11561169359523080757636373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15414892479364107676848497 11561169359523080757636373)
      ·
        refine ⟨541929813727644410514205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11561169359523080757636373 541929813727644410514205)
        ·
          refine ⟨203223680147866653942827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 541929813727644410514205 203223680147866653942827)
          ·
            refine ⟨304835520221799980914241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203223680147866653942827 304835520221799980914241)
            ·
              refine ⟨228626640166349985685681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304835520221799980914241 228626640166349985685681)
              ·
                refine ⟨171469980124762489264261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228626640166349985685681 171469980124762489264261)
                ·
                  refine ⟨32150621273392966737049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171469980124762489264261 32150621273392966737049)
                  ·
                    rfl

theorem cell22_281759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 4].length) (baseStart_281759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281759 prefixEnd_281759 := by exact prefixLift 281759
  have htrace : WordTrace (prefixWord ++ tailWord_281759) baseStart_281759 baseEnd_281759 := by
    simpa [prefixWord, tailWord_281759, baseEnd_281759] using wordTrace_append hprefix tailTrace_281759
  have hstable : (prefixWord ++ tailWord_281759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281759).length < 2 ^ (prefixWord ++ tailWord_281759).sum := by decide
  have hdescent : baseEnd_281759 < baseStart_281759 := by decide
  rcases family_descends (prefixWord ++ tailWord_281759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281770 : List Nat := [3, 1, 5, 1, 1, 3, 1, 7]
def baseStart_281770 : Nat := 118140960795 + 281770 * 2 ^ 59
def prefixEnd_281770 : Nat := 4983230072969 + 3 ^ 40 * 281770 * 2
def baseEnd_281770 : Nat := 10717292149442059798457

theorem tailTrace_281770 : CollatzResearch.WordTrace tailWord_281770 prefixEnd_281770 10717292149442059798457 := by
  unfold tailWord_281770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569249047300721832470691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6851330792801924886588509 2569249047300721832470691)
  ·
    refine ⟨3853873570951082748706037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569249047300721832470691 3853873570951082748706037)
    ·
      refine ⟨361300647276664007691191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3853873570951082748706037 361300647276664007691191)
      ·
        refine ⟨541950970914996011536787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361300647276664007691191 541950970914996011536787)
        ·
          refine ⟨812926456372494017305181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541950970914996011536787 812926456372494017305181)
          ·
            refine ⟨304847421139685256489443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812926456372494017305181 304847421139685256489443)
            ·
              refine ⟨457271131709527884734165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304847421139685256489443 457271131709527884734165)
              ·
                refine ⟨10717292149442059798457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 457271131709527884734165 10717292149442059798457)
                ·
                  rfl

theorem cell22_281770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_281770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281770 prefixEnd_281770 := by exact prefixLift 281770
  have htrace : WordTrace (prefixWord ++ tailWord_281770) baseStart_281770 baseEnd_281770 := by
    simpa [prefixWord, tailWord_281770, baseEnd_281770] using wordTrace_append hprefix tailTrace_281770
  have hstable : (prefixWord ++ tailWord_281770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281770).length < 2 ^ (prefixWord ++ tailWord_281770).sum := by decide
  have hdescent : baseEnd_281770 < baseStart_281770 := by decide
  rcases family_descends (prefixWord ++ tailWord_281770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281802 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_281802 : Nat := 118140960795 + 281802 * 2 ^ 59
def prefixEnd_281802 : Nat := 4983230072969 + 3 ^ 40 * 281802 * 2
def baseEnd_281802 : Nat := 96466583598941121386015

theorem tailTrace_281802 : CollatzResearch.WordTrace tailWord_281802 prefixEnd_281802 96466583598941121386015 := by
  unfold tailWord_281802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569540831271739198761915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6852108883391304530031773 2569540831271739198761915)
  ·
    refine ⟨3854311246907608798142873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569540831271739198761915 3854311246907608798142873)
    ·
      refine ⟨2890733435180706598607155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854311246907608798142873 2890733435180706598607155)
      ·
        refine ⟨4336100152771059897910733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890733435180706598607155 4336100152771059897910733)
        ·
          refine ⟨1626037557289147461716525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4336100152771059897910733 1626037557289147461716525)
          ·
            refine ⟨609764083983430298143697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1626037557289147461716525 609764083983430298143697)
            ·
              refine ⟨457323062987572723607773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609764083983430298143697 457323062987572723607773)
              ·
                refine ⟨171496148620339771352915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457323062987572723607773 171496148620339771352915)
                ·
                  refine ⟨257244222930509657029373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171496148620339771352915 257244222930509657029373)
                  ·
                    refine ⟨96466583598941121386015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257244222930509657029373 96466583598941121386015)
                    ·
                      rfl

theorem cell22_281802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_281802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281802 prefixEnd_281802 := by exact prefixLift 281802
  have htrace : WordTrace (prefixWord ++ tailWord_281802) baseStart_281802 baseEnd_281802 := by
    simpa [prefixWord, tailWord_281802, baseEnd_281802] using wordTrace_append hprefix tailTrace_281802
  have hstable : (prefixWord ++ tailWord_281802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281802).length < 2 ^ (prefixWord ++ tailWord_281802).sum := by decide
  have hdescent : baseEnd_281802 < baseStart_281802 := by decide
  rcases family_descends (prefixWord ++ tailWord_281802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281813 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_281813 : Nat := 118140960795 + 281813 * 2 ^ 59
def prefixEnd_281813 : Nat := 4983230072969 + 3 ^ 40 * 281813 * 2
def baseEnd_281813 : Nat := 96470349123740759360981

theorem tailTrace_281813 : CollatzResearch.WordTrace tailWord_281813 prefixEnd_281813 96470349123740759360981 := by
  unfold tailWord_281813
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278564528047105673698093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6852376352031403782465395 10278564528047105673698093)
  ·
    refine ⟨3854461698017664627636785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10278564528047105673698093 3854461698017664627636785)
    ·
      refine ⟨2890846273513248470727589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854461698017664627636785 2890846273513248470727589)
      ·
        refine ⟨542033676283734088261423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2890846273513248470727589 542033676283734088261423)
        ·
          refine ⟨813050514425601132392135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542033676283734088261423 813050514425601132392135)
          ·
            refine ⟨1219575771638401698588203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813050514425601132392135 1219575771638401698588203)
            ·
              refine ⟨1829363657457602547882305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219575771638401698588203 1829363657457602547882305)
              ·
                refine ⟨1372022743093201910911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829363657457602547882305 1372022743093201910911729)
                ·
                  refine ⟨1029017057319901433183797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372022743093201910911729 1029017057319901433183797)
                  ·
                    refine ⟨96470349123740759360981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1029017057319901433183797 96470349123740759360981)
                    ·
                      rfl

theorem cell22_281813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_281813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281813 prefixEnd_281813 := by exact prefixLift 281813
  have htrace : WordTrace (prefixWord ++ tailWord_281813) baseStart_281813 baseEnd_281813 := by
    simpa [prefixWord, tailWord_281813, baseEnd_281813] using wordTrace_append hprefix tailTrace_281813
  have hstable : (prefixWord ++ tailWord_281813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281813).length < 2 ^ (prefixWord ++ tailWord_281813).sum := by decide
  have hdescent : baseEnd_281813 < baseStart_281813 := by decide
  rcases family_descends (prefixWord ++ tailWord_281813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281873 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_281873 : Nat := 118140960795 + 281873 * 2 ^ 59
def prefixEnd_281873 : Nat := 4983230072969 + 3 ^ 40 * 281873 * 2
def baseEnd_281873 : Nat := 96490888349920602860797

theorem tailTrace_281873 : CollatzResearch.WordTrace tailWord_281873 prefixEnd_281873 96490888349920602860797 := by
  unfold tailWord_281873
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280752907829735920882273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6853835271886490613921515 10280752907829735920882273)
  ·
    refine ⟨7710564680872301940661705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10280752907829735920882273 7710564680872301940661705)
    ·
      refine ⟨5782923510654226455496279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7710564680872301940661705 5782923510654226455496279)
      ·
        refine ⟨8674385265981339683244419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5782923510654226455496279 8674385265981339683244419)
        ·
          refine ⟨13011577898972009524866629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674385265981339683244419 13011577898972009524866629)
          ·
            refine ⟨2439670856057251785912493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13011577898972009524866629 2439670856057251785912493)
            ·
              refine ⟨914876571021469419717185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2439670856057251785912493 914876571021469419717185)
              ·
                refine ⟨686157428266102064787889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914876571021469419717185 686157428266102064787889)
                ·
                  refine ⟨514618071199576548590917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686157428266102064787889 514618071199576548590917)
                  ·
                    refine ⟨96490888349920602860797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514618071199576548590917 96490888349920602860797)
                    ·
                      rfl

theorem cell22_281873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_281873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281873 prefixEnd_281873 := by exact prefixLift 281873
  have htrace : WordTrace (prefixWord ++ tailWord_281873) baseStart_281873 baseEnd_281873 := by
    simpa [prefixWord, tailWord_281873, baseEnd_281873] using wordTrace_append hprefix tailTrace_281873
  have hstable : (prefixWord ++ tailWord_281873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281873).length < 2 ^ (prefixWord ++ tailWord_281873).sum := by decide
  have hdescent : baseEnd_281873 < baseStart_281873 := by decide
  rcases family_descends (prefixWord ++ tailWord_281873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281903 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 5, 3]
def baseStart_281903 : Nat := 118140960795 + 281903 * 2 ^ 59
def prefixEnd_281903 : Nat := 4983230072969 + 3 ^ 40 * 281903 * 2
def baseEnd_281903 : Nat := 96501157963010524610705

theorem tailTrace_281903 : CollatzResearch.WordTrace tailWord_281903 prefixEnd_281903 96501157963010524610705 := by
  unfold tailWord_281903
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281847097721051044474363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6854564731814034029649575 10281847097721051044474363)
  ·
    refine ⟨15422770646581576566711545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10281847097721051044474363 15422770646581576566711545)
    ·
      refine ⟨11567077984936182425033659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15422770646581576566711545 11567077984936182425033659)
      ·
        refine ⟨17350616977404273637550489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567077984936182425033659 17350616977404273637550489)
        ·
          refine ⟨13012962733053205228162867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17350616977404273637550489 13012962733053205228162867)
          ·
            refine ⟨19519444099579807842244301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012962733053205228162867 19519444099579807842244301)
            ·
              refine ⟨7319791537342427940841613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19519444099579807842244301 7319791537342427940841613)
              ·
                refine ⟨2744921826503410477815605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7319791537342427940841613 2744921826503410477815605)
                ·
                  refine ⟨257336421234694732295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2744921826503410477815605 257336421234694732295213)
                  ·
                    refine ⟨96501157963010524610705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257336421234694732295213 96501157963010524610705)
                    ·
                      rfl

theorem cell22_281903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_281903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281903 prefixEnd_281903 := by exact prefixLift 281903
  have htrace : WordTrace (prefixWord ++ tailWord_281903) baseStart_281903 baseEnd_281903 := by
    simpa [prefixWord, tailWord_281903, baseEnd_281903] using wordTrace_append hprefix tailTrace_281903
  have hstable : (prefixWord ++ tailWord_281903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281903).length < 2 ^ (prefixWord ++ tailWord_281903).sum := by decide
  have hdescent : baseEnd_281903 < baseStart_281903 := by decide
  rcases family_descends (prefixWord ++ tailWord_281903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281937 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_281937 : Nat := 118140960795 + 281937 * 2 ^ 59
def prefixEnd_281937 : Nat := 4983230072969 + 3 ^ 40 * 281937 * 2
def baseEnd_281937 : Nat := 96512796857845769260601

theorem tailTrace_281937 : CollatzResearch.WordTrace tailWord_281937 prefixEnd_281937 96512796857845769260601 := by
  unfold tailWord_281937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283087179597874851212065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6855391453065249900808043 10283087179597874851212065)
  ·
    refine ⟨7712315384698406138409049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10283087179597874851212065 7712315384698406138409049)
    ·
      refine ⟨5784236538523804603806787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7712315384698406138409049 5784236538523804603806787)
      ·
        refine ⟨8676354807785706905710181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784236538523804603806787 8676354807785706905710181)
        ·
          refine ⟨1626816526459820044820659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8676354807785706905710181 1626816526459820044820659)
          ·
            refine ⟨2440224789689730067230989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626816526459820044820659 2440224789689730067230989)
            ·
              refine ⟨915084296133648775211621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2440224789689730067230989 915084296133648775211621)
              ·
                refine ⟨171578305525059145352179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 915084296133648775211621 171578305525059145352179)
                ·
                  refine ⟨257367458287588718028269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171578305525059145352179 257367458287588718028269)
                  ·
                    refine ⟨96512796857845769260601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257367458287588718028269 96512796857845769260601)
                    ·
                      rfl

theorem cell22_281937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_281937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281937 prefixEnd_281937 := by exact prefixLift 281937
  have htrace : WordTrace (prefixWord ++ tailWord_281937) baseStart_281937 baseEnd_281937 := by
    simpa [prefixWord, tailWord_281937, baseEnd_281937] using wordTrace_append hprefix tailTrace_281937
  have hstable : (prefixWord ++ tailWord_281937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281937).length < 2 ^ (prefixWord ++ tailWord_281937).sum := by decide
  have hdescent : baseEnd_281937 < baseStart_281937 := by decide
  rcases family_descends (prefixWord ++ tailWord_281937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281980 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_281980 : Nat := 118140960795 + 281980 * 2 ^ 59
def prefixEnd_281980 : Nat := 4983230072969 + 3 ^ 40 * 281980 * 2
def baseEnd_281980 : Nat := 96527516636607990435469

theorem tailTrace_281980 : CollatzResearch.WordTrace tailWord_281980 prefixEnd_281980 96527516636607990435469 := by
  unfold tailWord_281980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142327759221046597513697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6856437012294728796684929 5142327759221046597513697)
  ·
    refine ⟨3856745819415784948135273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5142327759221046597513697 3856745819415784948135273)
    ·
      refine ⟨2892559364561838711101455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3856745819415784948135273 2892559364561838711101455)
      ·
        refine ⟨4338839046842758066652183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2892559364561838711101455 4338839046842758066652183)
        ·
          refine ⟨6508258570264137099978275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338839046842758066652183 6508258570264137099978275)
          ·
            refine ⟨9762387855396205649967413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508258570264137099978275 9762387855396205649967413)
            ·
              refine ⟨915223861443394279684445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9762387855396205649967413 915223861443394279684445)
              ·
                refine ⟨343208948041272854881667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915223861443394279684445 343208948041272854881667)
                ·
                  refine ⟨514813422061909282322501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343208948041272854881667 514813422061909282322501)
                  ·
                    refine ⟨96527516636607990435469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514813422061909282322501 96527516636607990435469)
                    ·
                      rfl

theorem cell22_281980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_281980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281980 prefixEnd_281980 := by exact prefixLift 281980
  have htrace : WordTrace (prefixWord ++ tailWord_281980) baseStart_281980 baseEnd_281980 := by
    simpa [prefixWord, tailWord_281980, baseEnd_281980] using wordTrace_append hprefix tailTrace_281980
  have hstable : (prefixWord ++ tailWord_281980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281980).length < 2 ^ (prefixWord ++ tailWord_281980).sum := by decide
  have hdescent : baseEnd_281980 < baseStart_281980 := by decide
  rcases family_descends (prefixWord ++ tailWord_281980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281995 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 4]
def baseStart_281995 : Nat := 118140960795 + 281995 * 2 ^ 59
def prefixEnd_281995 : Nat := 4983230072969 + 3 ^ 40 * 281995 * 2
def baseEnd_281995 : Nat := 32177550481050983770141

theorem tailTrace_281995 : CollatzResearch.WordTrace tailWord_281995 prefixEnd_281995 32177550481050983770141 := by
  unfold tailWord_281995
  simp only [CollatzResearch.WordTrace]
  refine ⟨10285202613387750756823439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6856801742258500504548959 10285202613387750756823439)
  ·
    refine ⟨15427803920081626135235159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10285202613387750756823439 15427803920081626135235159)
    ·
      refine ⟨23141705880122439202852739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15427803920081626135235159 23141705880122439202852739)
      ·
        refine ⟨34712558820183658804279109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23141705880122439202852739 34712558820183658804279109)
        ·
          refine ⟨6508604778784436025802333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34712558820183658804279109 6508604778784436025802333)
          ·
            refine ⟨2440726792044163509675875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6508604778784436025802333 2440726792044163509675875)
            ·
              refine ⟨3661090188066245264513813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440726792044163509675875 3661090188066245264513813)
              ·
                refine ⟨171613602565605246774085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3661090188066245264513813 171613602565605246774085)
                ·
                  refine ⟨32177550481050983770141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171613602565605246774085 32177550481050983770141)
                  ·
                    rfl

theorem cell22_281995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 4].length) (baseStart_281995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_281995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_281995 prefixEnd_281995 := by exact prefixLift 281995
  have htrace : WordTrace (prefixWord ++ tailWord_281995) baseStart_281995 baseEnd_281995 := by
    simpa [prefixWord, tailWord_281995, baseEnd_281995] using wordTrace_append hprefix tailTrace_281995
  have hstable : (prefixWord ++ tailWord_281995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281995).length < 2 ^ (prefixWord ++ tailWord_281995).sum := by decide
  have hdescent : baseEnd_281995 < baseStart_281995 := by decide
  rcases family_descends (prefixWord ++ tailWord_281995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282029 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 4]
def baseStart_282029 : Nat := 118140960795 + 282029 * 2 ^ 59
def prefixEnd_282029 : Nat := 4983230072969 + 3 ^ 40 * 282029 * 2
def baseEnd_282029 : Nat := 32181430112662731986773

theorem tailTrace_282029 : CollatzResearch.WordTrace tailWord_282029 prefixEnd_282029 32181430112662731986773 := by
  unfold tailWord_282029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286442695264574563561141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6857628463509716375707427 10286442695264574563561141)
  ·
    refine ⟨964354002681053865333857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10286442695264574563561141 964354002681053865333857)
    ·
      refine ⟨723265502010790399000393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 964354002681053865333857 723265502010790399000393)
      ·
        refine ⟨542449126508092799250295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723265502010790399000393 542449126508092799250295)
        ·
          refine ⟨813673689762139198875443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542449126508092799250295 813673689762139198875443)
          ·
            refine ⟨1220510534643208798313165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813673689762139198875443 1220510534643208798313165)
            ·
              refine ⟨457691450491203299367437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220510534643208798313165 457691450491203299367437)
              ·
                refine ⟨171634293934201237262789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457691450491203299367437 171634293934201237262789)
                ·
                  refine ⟨32181430112662731986773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171634293934201237262789 32181430112662731986773)
                  ·
                    rfl

theorem cell22_282029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_282029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282029 prefixEnd_282029 := by exact prefixLift 282029
  have htrace : WordTrace (prefixWord ++ tailWord_282029) baseStart_282029 baseEnd_282029 := by
    simpa [prefixWord, tailWord_282029, baseEnd_282029] using wordTrace_append hprefix tailTrace_282029
  have hstable : (prefixWord ++ tailWord_282029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282029).length < 2 ^ (prefixWord ++ tailWord_282029).sum := by decide
  have hdescent : baseEnd_282029 < baseStart_282029 := by decide
  rcases family_descends (prefixWord ++ tailWord_282029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282102 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_282102 : Nat := 118140960795 + 282102 * 2 ^ 59
def prefixEnd_282102 : Nat := 4983230072969 + 3 ^ 40 * 282102 * 2
def baseEnd_282102 : Nat := 32189759909946779628365

theorem tailTrace_282102 : CollatzResearch.WordTrace tailWord_282102 prefixEnd_282102 32189759909946779628365 := by
  unfold tailWord_282102
  simp only [CollatzResearch.WordTrace]
  refine ⟨643069076500006751935535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6859403482666738687312373 643069076500006751935535)
  ·
    refine ⟨964603614750010127903303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 643069076500006751935535 964603614750010127903303)
    ·
      refine ⟨1446905422125015191854955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964603614750010127903303 1446905422125015191854955)
      ·
        refine ⟨2170358133187522787782433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446905422125015191854955 2170358133187522787782433)
        ·
          refine ⟨1627768599890642090836825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170358133187522787782433 1627768599890642090836825)
          ·
            refine ⟨1220826449917981568127619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627768599890642090836825 1220826449917981568127619)
            ·
              refine ⟨1831239674876972352191429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220826449917981568127619 1831239674876972352191429)
              ·
                refine ⟨343357439039432316035893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831239674876972352191429 343357439039432316035893)
                ·
                  refine ⟨32189759909946779628365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 343357439039432316035893 32189759909946779628365)
                  ·
                    rfl

theorem cell22_282102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_282102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282102 prefixEnd_282102 := by exact prefixLift 282102
  have htrace : WordTrace (prefixWord ++ tailWord_282102) baseStart_282102 baseEnd_282102 := by
    simpa [prefixWord, tailWord_282102, baseEnd_282102] using wordTrace_append hprefix tailTrace_282102
  have hstable : (prefixWord ++ tailWord_282102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282102).length < 2 ^ (prefixWord ++ tailWord_282102).sum := by decide
  have hdescent : baseEnd_282102 < baseStart_282102 := by decide
  rcases family_descends (prefixWord ++ tailWord_282102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282160 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_282160 : Nat := 118140960795 + 282160 * 2 ^ 59
def prefixEnd_282160 : Nat := 4983230072969 + 3 ^ 40 * 282160 * 2
def baseEnd_282160 : Nat := 96589134315147520934917

theorem tailTrace_282160 : CollatzResearch.WordTrace tailWord_282160 prefixEnd_282160 96589134315147520934917 := by
  unfold tailWord_282160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145610328894991968289967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6860813771859989291053289 5145610328894991968289967)
  ·
    refine ⟨7718415493342487952434951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5145610328894991968289967 7718415493342487952434951)
    ·
      refine ⟨11577623240013731928652427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718415493342487952434951 11577623240013731928652427)
      ·
        refine ⟨17366434860020597892978641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11577623240013731928652427 17366434860020597892978641)
        ·
          refine ⟨13024826145015448419733981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17366434860020597892978641 13024826145015448419733981)
          ·
            refine ⟨4884309804380793157400243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13024826145015448419733981 4884309804380793157400243)
            ·
              refine ⟨7326464706571189736100365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884309804380793157400243 7326464706571189736100365)
              ·
                refine ⟨2747424264964196151037637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7326464706571189736100365 2747424264964196151037637)
                ·
                  refine ⟨515142049680786778319557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2747424264964196151037637 515142049680786778319557)
                  ·
                    refine ⟨96589134315147520934917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515142049680786778319557 96589134315147520934917)
                    ·
                      rfl

theorem cell22_282160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_282160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282160 prefixEnd_282160 := by exact prefixLift 282160
  have htrace : WordTrace (prefixWord ++ tailWord_282160) baseStart_282160 baseEnd_282160 := by
    simpa [prefixWord, tailWord_282160, baseEnd_282160] using wordTrace_append hprefix tailTrace_282160
  have hstable : (prefixWord ++ tailWord_282160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282160).length < 2 ^ (prefixWord ++ tailWord_282160).sum := by decide
  have hdescent : baseEnd_282160 < baseStart_282160 := by decide
  rcases family_descends (prefixWord ++ tailWord_282160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282190 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_282190 : Nat := 118140960795 + 282190 * 2 ^ 59
def prefixEnd_282190 : Nat := 4983230072969 + 3 ^ 40 * 282190 * 2
def baseEnd_282190 : Nat := 96599403928237442684825

theorem tailTrace_282190 : CollatzResearch.WordTrace tailWord_282190 prefixEnd_282190 96599403928237442684825 := by
  unfold tailWord_282190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286539355960162382521503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6861543231787532706781349 1286539355960162382521503)
  ·
    refine ⟨1929809033940243573782255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286539355960162382521503 1929809033940243573782255)
    ·
      refine ⟨2894713550910365360673383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929809033940243573782255 2894713550910365360673383)
      ·
        refine ⟨4342070326365548041010075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894713550910365360673383 4342070326365548041010075)
        ·
          refine ⟨6513105489548322061515113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342070326365548041010075 6513105489548322061515113)
          ·
            refine ⟨4884829117161241546136335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6513105489548322061515113 4884829117161241546136335)
            ·
              refine ⟨7327243675741862319204503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884829117161241546136335 7327243675741862319204503)
              ·
                refine ⟨10990865513612793478806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327243675741862319204503 10990865513612793478806755)
                ·
                  refine ⟨16486298270419190218210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10990865513612793478806755 16486298270419190218210133)
                  ·
                    refine ⟨96599403928237442684825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16486298270419190218210133 96599403928237442684825)
                    ·
                      rfl

theorem cell22_282190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_282190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282190 prefixEnd_282190 := by exact prefixLift 282190
  have htrace : WordTrace (prefixWord ++ tailWord_282190) baseStart_282190 baseEnd_282190 := by
    simpa [prefixWord, tailWord_282190, baseEnd_282190] using wordTrace_append hprefix tailTrace_282190
  have hstable : (prefixWord ++ tailWord_282190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282190).length < 2 ^ (prefixWord ++ tailWord_282190).sum := by decide
  have hdescent : baseEnd_282190 < baseStart_282190 := by decide
  rcases family_descends (prefixWord ++ tailWord_282190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282224 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_282224 : Nat := 118140960795 + 282224 * 2 ^ 59
def prefixEnd_282224 : Nat := 4983230072969 + 3 ^ 40 * 282224 * 2
def baseEnd_282224 : Nat := 96611042823072687334721

theorem tailTrace_282224 : CollatzResearch.WordTrace tailWord_282224 prefixEnd_282224 96611042823072687334721 := by
  unfold tailWord_282224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146777464779061433454863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6862369953038748577939817 5146777464779061433454863)
  ·
    refine ⟨7720166197168592150182295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5146777464779061433454863 7720166197168592150182295)
    ·
      refine ⟨11580249295752888225273443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7720166197168592150182295 11580249295752888225273443)
      ·
        refine ⟨17370373943629332337910165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11580249295752888225273443 17370373943629332337910165)
        ·
          refine ⟨814236278607624953339539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17370373943629332337910165 814236278607624953339539)
          ·
            refine ⟨1221354417911437430009309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814236278607624953339539 1221354417911437430009309)
            ·
              refine ⟨458007906716789036253491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1221354417911437430009309 458007906716789036253491)
              ·
                refine ⟨687011860075183554380237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458007906716789036253491 687011860075183554380237)
                ·
                  refine ⟨257629447528193832892589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687011860075183554380237 257629447528193832892589)
                  ·
                    refine ⟨96611042823072687334721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257629447528193832892589 96611042823072687334721)
                    ·
                      rfl

theorem cell22_282224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_282224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282224 prefixEnd_282224 := by exact prefixLift 282224
  have htrace : WordTrace (prefixWord ++ tailWord_282224) baseStart_282224 baseEnd_282224 := by
    simpa [prefixWord, tailWord_282224, baseEnd_282224] using wordTrace_append hprefix tailTrace_282224
  have hstable : (prefixWord ++ tailWord_282224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282224).length < 2 ^ (prefixWord ++ tailWord_282224).sum := by decide
  have hdescent : baseEnd_282224 < baseStart_282224 := by decide
  rcases family_descends (prefixWord ++ tailWord_282224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282235 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_282235 : Nat := 118140960795 + 282235 * 2 ^ 59
def prefixEnd_282235 : Nat := 4983230072969 + 3 ^ 40 * 282235 * 2
def baseEnd_282235 : Nat := 96614808347872325309687

theorem tailTrace_282235 : CollatzResearch.WordTrace tailWord_282235 prefixEnd_282235 96614808347872325309687 := by
  unfold tailWord_282235
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293956132518271745560159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862637421678847830373439 10293956132518271745560159)
  ·
    refine ⟨15440934198777407618340239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293956132518271745560159 15440934198777407618340239)
    ·
      refine ⟨23161401298166111427510359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15440934198777407618340239 23161401298166111427510359)
      ·
        refine ⟨34742101947249167141265539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23161401298166111427510359 34742101947249167141265539)
        ·
          refine ⟨52113152920873750711898309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34742101947249167141265539 52113152920873750711898309)
          ·
            refine ⟨9771216172663828258480933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52113152920873750711898309 9771216172663828258480933)
            ·
              refine ⟨1832103032374467798465175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9771216172663828258480933 1832103032374467798465175)
              ·
                refine ⟨2748154548561701697697763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832103032374467798465175 2748154548561701697697763)
                ·
                  refine ⟨4122231822842552546546645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748154548561701697697763 4122231822842552546546645)
                  ·
                    refine ⟨96614808347872325309687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4122231822842552546546645 96614808347872325309687)
                    ·
                      rfl

theorem cell22_282235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_282235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282235 prefixEnd_282235 := by exact prefixLift 282235
  have htrace : WordTrace (prefixWord ++ tailWord_282235) baseStart_282235 baseEnd_282235 := by
    simpa [prefixWord, tailWord_282235, baseEnd_282235] using wordTrace_append hprefix tailTrace_282235
  have hstable : (prefixWord ++ tailWord_282235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282235).length < 2 ^ (prefixWord ++ tailWord_282235).sum := by decide
  have hdescent : baseEnd_282235 < baseStart_282235 := by decide
  rcases family_descends (prefixWord ++ tailWord_282235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282265 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 10]
def baseStart_282265 : Nat := 118140960795 + 282265 * 2 ^ 59
def prefixEnd_282265 : Nat := 4983230072969 + 3 ^ 40 * 282265 * 2
def baseEnd_282265 : Nat := 32208359320320749019865

theorem tailTrace_282265 : CollatzResearch.WordTrace tailWord_282265 prefixEnd_282265 32208359320320749019865 := by
  unfold tailWord_282265
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295050322409586869152249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6863366881606391246101499 10295050322409586869152249)
  ·
    refine ⟨7721287741807190151864187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10295050322409586869152249 7721287741807190151864187)
    ·
      refine ⟨11581931612710785227796281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7721287741807190151864187 11581931612710785227796281)
      ·
        refine ⟨8686448709533088920847211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11581931612710785227796281 8686448709533088920847211)
        ·
          refine ⟨13029673064299633381270817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8686448709533088920847211 13029673064299633381270817)
          ·
            refine ⟨9772254798224725035953113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13029673064299633381270817 9772254798224725035953113)
            ·
              refine ⟨7329191098668543776964835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9772254798224725035953113 7329191098668543776964835)
              ·
                refine ⟨10993786648002815665447253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329191098668543776964835 10993786648002815665447253)
                ·
                  refine ⟨32208359320320749019865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10993786648002815665447253 32208359320320749019865)
                  ·
                    rfl

theorem cell22_282265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_282265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282265 prefixEnd_282265 := by exact prefixLift 282265
  have htrace : WordTrace (prefixWord ++ tailWord_282265) baseStart_282265 baseEnd_282265 := by
    simpa [prefixWord, tailWord_282265, baseEnd_282265] using wordTrace_append hprefix tailTrace_282265
  have hstable : (prefixWord ++ tailWord_282265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282265).length < 2 ^ (prefixWord ++ tailWord_282265).sum := by decide
  have hdescent : baseEnd_282265 < baseStart_282265 := by decide
  rcases family_descends (prefixWord ++ tailWord_282265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282271 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 5]
def baseStart_282271 : Nat := 118140960795 + 282271 * 2 ^ 59
def prefixEnd_282271 : Nat := 4983230072969 + 3 ^ 40 * 282271 * 2
def baseEnd_282271 : Nat := 32209043961193410469859

theorem tailTrace_282271 : CollatzResearch.WordTrace tailWord_282271 prefixEnd_282271 32209043961193410469859 := by
  unfold tailWord_282271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295269160387849893870667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6863512773591899929247111 10295269160387849893870667)
  ·
    refine ⟨15442903740581774840806001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10295269160387849893870667 15442903740581774840806001)
    ·
      refine ⟨11582177805436331130604501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15442903740581774840806001 11582177805436331130604501)
      ·
        refine ⟨271457292314914010873543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11582177805436331130604501 271457292314914010873543)
        ·
          refine ⟨407185938472371016310315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271457292314914010873543 407185938472371016310315)
          ·
            refine ⟨610778907708556524465473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407185938472371016310315 610778907708556524465473)
            ·
              refine ⟨458084180781417393349105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610778907708556524465473 458084180781417393349105)
              ·
                refine ⟨343563135586063045011829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458084180781417393349105 343563135586063045011829)
                ·
                  refine ⟨32209043961193410469859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 343563135586063045011829 32209043961193410469859)
                  ·
                    rfl

theorem cell22_282271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 5].length) (baseStart_282271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282271 prefixEnd_282271 := by exact prefixLift 282271
  have htrace : WordTrace (prefixWord ++ tailWord_282271) baseStart_282271 baseEnd_282271 := by
    simpa [prefixWord, tailWord_282271, baseEnd_282271] using wordTrace_append hprefix tailTrace_282271
  have hstable : (prefixWord ++ tailWord_282271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282271).length < 2 ^ (prefixWord ++ tailWord_282271).sum := by decide
  have hdescent : baseEnd_282271 < baseStart_282271 := by decide
  rcases family_descends (prefixWord ++ tailWord_282271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282286 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_282286 : Nat := 118140960795 + 282286 * 2 ^ 59
def prefixEnd_282286 : Nat := 4983230072969 + 3 ^ 40 * 282286 * 2
def baseEnd_282286 : Nat := 96632266690125192284531

theorem tailTrace_282286 : CollatzResearch.WordTrace tailWord_282286 prefixEnd_282286 96632266690125192284531 := by
  unfold tailWord_282286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286977031916688431958339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6863877503555671637111141 1286977031916688431958339)
  ·
    refine ⟨1930465547875032647937509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286977031916688431958339 1930465547875032647937509)
    ·
      refine ⟨361962290226568621488283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1930465547875032647937509 361962290226568621488283)
      ·
        refine ⟨542943435339852932232425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361962290226568621488283 542943435339852932232425)
        ·
          refine ⟨407207576504889699174319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542943435339852932232425 407207576504889699174319)
          ·
            refine ⟨610811364757334548761479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407207576504889699174319 610811364757334548761479)
            ·
              refine ⟨916217047136001823142219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610811364757334548761479 916217047136001823142219)
              ·
                refine ⟨1374325570704002734713329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916217047136001823142219 1374325570704002734713329)
                ·
                  refine ⟨1030744178028002051034997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374325570704002734713329 1030744178028002051034997)
                  ·
                    refine ⟨96632266690125192284531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1030744178028002051034997 96632266690125192284531)
                    ·
                      rfl

theorem cell22_282286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_282286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282286 prefixEnd_282286 := by exact prefixLift 282286
  have htrace : WordTrace (prefixWord ++ tailWord_282286) baseStart_282286 baseEnd_282286 := by
    simpa [prefixWord, tailWord_282286, baseEnd_282286] using wordTrace_append hprefix tailTrace_282286
  have hstable : (prefixWord ++ tailWord_282286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282286).length < 2 ^ (prefixWord ++ tailWord_282286).sum := by decide
  have hdescent : baseEnd_282286 < baseStart_282286 := by decide
  rcases family_descends (prefixWord ++ tailWord_282286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282297 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_282297 : Nat := 118140960795 + 282297 * 2 ^ 59
def prefixEnd_282297 : Nat := 4983230072969 + 3 ^ 40 * 282297 * 2
def baseEnd_282297 : Nat := 96636032214924830259497

theorem tailTrace_282297 : CollatzResearch.WordTrace tailWord_282297 prefixEnd_282297 96636032214924830259497 := by
  unfold tailWord_282297
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296217458293656334317145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6864144972195770889544763 10296217458293656334317145)
  ·
    refine ⟨7722163093720242250737859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10296217458293656334317145 7722163093720242250737859)
    ·
      refine ⟨11583244640580363376106789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7722163093720242250737859 11583244640580363376106789)
      ·
        refine ⟨2171858370108818133020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11583244640580363376106789 2171858370108818133020023)
        ·
          refine ⟨3257787555163227199530035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171858370108818133020023 3257787555163227199530035)
          ·
            refine ⟨4886681332744840799295053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257787555163227199530035 4886681332744840799295053)
            ·
              refine ⟨1832505499779315299735645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4886681332744840799295053 1832505499779315299735645)
              ·
                refine ⟨687189562417243237400867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832505499779315299735645 687189562417243237400867)
                ·
                  refine ⟨1030784343625864856101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687189562417243237400867 1030784343625864856101301)
                  ·
                    refine ⟨96636032214924830259497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1030784343625864856101301 96636032214924830259497)
                    ·
                      rfl

theorem cell22_282297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_282297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282297 prefixEnd_282297 := by exact prefixLift 282297
  have htrace : WordTrace (prefixWord ++ tailWord_282297) baseStart_282297 baseEnd_282297 := by
    simpa [prefixWord, tailWord_282297, baseEnd_282297] using wordTrace_append hprefix tailTrace_282297
  have hstable : (prefixWord ++ tailWord_282297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282297).length < 2 ^ (prefixWord ++ tailWord_282297).sum := by decide
  have hdescent : baseEnd_282297 < baseStart_282297 := by decide
  rcases family_descends (prefixWord ++ tailWord_282297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282312 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_282312 : Nat := 118140960795 + 282312 * 2 ^ 59
def prefixEnd_282312 : Nat := 4983230072969 + 3 ^ 40 * 282312 * 2
def baseEnd_282312 : Nat := 96641167021469791134451

theorem tailTrace_282312 : CollatzResearch.WordTrace tailWord_282312 prefixEnd_282312 96641167021469791134451 := by
  unfold tailWord_282312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5148382276619656948056595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6864509702159542597408793 5148382276619656948056595)
  ·
    refine ⟨7722573414929485422084893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5148382276619656948056595 7722573414929485422084893)
    ·
      refine ⟨2895965030598557033281835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7722573414929485422084893 2895965030598557033281835)
      ·
        refine ⟨4343947545897835549922753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895965030598557033281835 4343947545897835549922753)
        ·
          refine ⟨3257960659423376662442065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4343947545897835549922753 3257960659423376662442065)
          ·
            refine ⟨2443470494567532496831549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3257960659423376662442065 2443470494567532496831549)
            ·
              refine ⟨916301435462824686311831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2443470494567532496831549 916301435462824686311831)
              ·
                refine ⟨1374452153194237029467747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916301435462824686311831 1374452153194237029467747)
                ·
                  refine ⟨2061678229791355544201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374452153194237029467747 2061678229791355544201621)
                  ·
                    refine ⟨96641167021469791134451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2061678229791355544201621 96641167021469791134451)
                    ·
                      rfl

theorem cell22_282312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_282312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282312 prefixEnd_282312 := by exact prefixLift 282312
  have htrace : WordTrace (prefixWord ++ tailWord_282312) baseStart_282312 baseEnd_282312 := by
    simpa [prefixWord, tailWord_282312, baseEnd_282312] using wordTrace_append hprefix tailTrace_282312
  have hstable : (prefixWord ++ tailWord_282312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282312).length < 2 ^ (prefixWord ++ tailWord_282312).sum := by decide
  have hdescent : baseEnd_282312 < baseStart_282312 := by decide
  rcases family_descends (prefixWord ++ tailWord_282312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282359 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 3, 3]
def baseStart_282359 : Nat := 118140960795 + 282359 * 2 ^ 59
def prefixEnd_282359 : Nat := 4983230072969 + 3 ^ 40 * 282359 * 2
def baseEnd_282359 : Nat := 96657256081977335209307

theorem tailTrace_282359 : CollatzResearch.WordTrace tailWord_282359 prefixEnd_282359 96657256081977335209307 := by
  unfold tailWord_282359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298478784069040923074131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6865652522712693948716087 10298478784069040923074131)
  ·
    refine ⟨15447718176103561384611197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298478784069040923074131 15447718176103561384611197)
    ·
      refine ⟨5792894316038835519229199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15447718176103561384611197 5792894316038835519229199)
      ·
        refine ⟨8689341474058253278843799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792894316038835519229199 8689341474058253278843799)
        ·
          refine ⟨13034012211087379918265699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8689341474058253278843799 13034012211087379918265699)
          ·
            refine ⟨19551018316631069877398549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13034012211087379918265699 19551018316631069877398549)
            ·
              refine ⟨916453983592081400503057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19551018316631069877398549 916453983592081400503057)
              ·
                refine ⟨687340487694061050377293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916453983592081400503057 687340487694061050377293)
                ·
                  refine ⟨257752682885272893891485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687340487694061050377293 257752682885272893891485)
                  ·
                    refine ⟨96657256081977335209307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257752682885272893891485 96657256081977335209307)
                    ·
                      rfl

theorem cell22_282359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_282359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282359 prefixEnd_282359 := by exact prefixLift 282359
  have htrace : WordTrace (prefixWord ++ tailWord_282359) baseStart_282359 baseEnd_282359 := by
    simpa [prefixWord, tailWord_282359, baseEnd_282359] using wordTrace_append hprefix tailTrace_282359
  have hstable : (prefixWord ++ tailWord_282359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282359).length < 2 ^ (prefixWord ++ tailWord_282359).sum := by decide
  have hdescent : baseEnd_282359 < baseStart_282359 := by decide
  rcases family_descends (prefixWord ++ tailWord_282359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282387 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_282387 : Nat := 118140960795 + 282387 * 2 ^ 59
def prefixEnd_282387 : Nat := 4983230072969 + 3 ^ 40 * 282387 * 2
def baseEnd_282387 : Nat := 96666841054194595509221

theorem tailTrace_282387 : CollatzResearch.WordTrace tailWord_282387 prefixEnd_282387 96666841054194595509221 := by
  unfold tailWord_282387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299500027967601705093415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6866333351978401136728943 10299500027967601705093415)
  ·
    refine ⟨15449250041951402557640123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10299500027967601705093415 15449250041951402557640123)
    ·
      refine ⟨23173875062927103836460185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15449250041951402557640123 23173875062927103836460185)
      ·
        refine ⟨17380406297195327877345139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23173875062927103836460185 17380406297195327877345139)
        ·
          refine ⟨26070609445792991816017709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17380406297195327877345139 26070609445792991816017709)
          ·
            refine ⟨9776478542172371931006641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26070609445792991816017709 9776478542172371931006641)
            ·
              refine ⟨7332358906629278948254981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9776478542172371931006641 7332358906629278948254981)
              ·
                refine ⟨1374817294992989802797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7332358906629278948254981 1374817294992989802797809)
                ·
                  refine ⟨1031112971244742352098357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374817294992989802797809 1031112971244742352098357)
                  ·
                    refine ⟨96666841054194595509221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1031112971244742352098357 96666841054194595509221)
                    ·
                      rfl

theorem cell22_282387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_282387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282387 prefixEnd_282387 := by exact prefixLift 282387
  have htrace : WordTrace (prefixWord ++ tailWord_282387) baseStart_282387 baseEnd_282387 := by
    simpa [prefixWord, tailWord_282387, baseEnd_282387] using wordTrace_append hprefix tailTrace_282387
  have hstable : (prefixWord ++ tailWord_282387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282387).length < 2 ^ (prefixWord ++ tailWord_282387).sum := by decide
  have hdescent : baseEnd_282387 < baseStart_282387 := by decide
  rcases family_descends (prefixWord ++ tailWord_282387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282466 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_282466 : Nat := 118140960795 + 282466 * 2 ^ 59
def prefixEnd_282466 : Nat := 4983230072969 + 3 ^ 40 * 282466 * 2
def baseEnd_282466 : Nat := 96693884368664722783979

theorem tailTrace_282466 : CollatzResearch.WordTrace tailWord_282466 prefixEnd_282466 96693884368664722783979 := by
  unfold tailWord_282466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575595348670349549304813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6868254263120932131479501 2575595348670349549304813)
  ·
    refine ⟨965848255751381080989305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2575595348670349549304813 965848255751381080989305)
    ·
      refine ⟨724386191813535810741979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 965848255751381080989305 724386191813535810741979)
      ·
        refine ⟨1086579287720303716112969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724386191813535810741979 1086579287720303716112969)
        ·
          refine ⟨814934465790227787084727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086579287720303716112969 814934465790227787084727)
          ·
            refine ⟨1222401698685341680627091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814934465790227787084727 1222401698685341680627091)
            ·
              refine ⟨1833602548028012520940637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222401698685341680627091 1833602548028012520940637)
              ·
                refine ⟨687600955510504695352739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1833602548028012520940637 687600955510504695352739)
                ·
                  refine ⟨1031401433265757043029109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687600955510504695352739 1031401433265757043029109)
                  ·
                    refine ⟨96693884368664722783979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1031401433265757043029109 96693884368664722783979)
                    ·
                      rfl

theorem cell22_282466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_282466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282466 prefixEnd_282466 := by exact prefixLift 282466
  have htrace : WordTrace (prefixWord ++ tailWord_282466) baseStart_282466 baseEnd_282466 := by
    simpa [prefixWord, tailWord_282466, baseEnd_282466] using wordTrace_append hprefix tailTrace_282466
  have hstable : (prefixWord ++ tailWord_282466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282466).length < 2 ^ (prefixWord ++ tailWord_282466).sum := by decide
  have hdescent : baseEnd_282466 < baseStart_282466 := by decide
  rcases family_descends (prefixWord ++ tailWord_282466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282530 : List Nat := [3, 3, 1, 2, 4, 1, 2, 6]
def baseStart_282530 : Nat := 118140960795 + 282530 * 2 ^ 59
def prefixEnd_282530 : Nat := 4983230072969 + 3 ^ 40 * 282530 * 2
def baseEnd_282530 : Nat := 10746199208509987687087

theorem tailTrace_282530 : CollatzResearch.WordTrace tailWord_282530 prefixEnd_282530 10746199208509987687087 := by
  unfold tailWord_282530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576178916612384281887261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6869810444299691418366029 2576178916612384281887261)
  ·
    refine ⟨966067093729644105707723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2576178916612384281887261 966067093729644105707723)
    ·
      refine ⟨1449100640594466158561585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966067093729644105707723 1449100640594466158561585)
      ·
        refine ⟨1086825480445849618921189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1449100640594466158561585 1086825480445849618921189)
        ·
          refine ⟨203779777583596803547723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1086825480445849618921189 203779777583596803547723)
          ·
            refine ⟨305669666375395205321585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203779777583596803547723 305669666375395205321585)
            ·
              refine ⟨229252249781546403991189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305669666375395205321585 229252249781546403991189)
              ·
                refine ⟨10746199208509987687087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229252249781546403991189 10746199208509987687087)
                ·
                  rfl

theorem cell22_282530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_282530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282530 prefixEnd_282530 := by exact prefixLift 282530
  have htrace : WordTrace (prefixWord ++ tailWord_282530) baseStart_282530 baseEnd_282530 := by
    simpa [prefixWord, tailWord_282530, baseEnd_282530] using wordTrace_append hprefix tailTrace_282530
  have hstable : (prefixWord ++ tailWord_282530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282530).length < 2 ^ (prefixWord ++ tailWord_282530).sum := by decide
  have hdescent : baseEnd_282530 < baseStart_282530 := by decide
  rcases family_descends (prefixWord ++ tailWord_282530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282545 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_282545 : Nat := 118140960795 + 282545 * 2 ^ 59
def prefixEnd_282545 : Nat := 4983230072969 + 3 ^ 40 * 282545 * 2
def baseEnd_282545 : Nat := 96720927683134850058737

theorem tailTrace_282545 : CollatzResearch.WordTrace tailWord_282545 prefixEnd_282545 96720927683134850058737 := by
  unfold tailWord_282545
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305262761395194689345089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6870175174263463126230059 10305262761395194689345089)
  ·
    refine ⟨7728947071046396017008817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10305262761395194689345089 7728947071046396017008817)
    ·
      refine ⟨5796710303284797012756613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7728947071046396017008817 5796710303284797012756613)
      ·
        refine ⟨1086883181865899439891865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5796710303284797012756613 1086883181865899439891865)
        ·
          refine ⟨815162386399424579918899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086883181865899439891865 815162386399424579918899)
          ·
            refine ⟨1222743579599136869878349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815162386399424579918899 1222743579599136869878349)
            ·
              refine ⟨458528842349676326204381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1222743579599136869878349 458528842349676326204381)
              ·
                refine ⟨171948315881128622326643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 458528842349676326204381 171948315881128622326643)
                ·
                  refine ⟨257922473821692933489965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171948315881128622326643 257922473821692933489965)
                  ·
                    refine ⟨96720927683134850058737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 257922473821692933489965 96720927683134850058737)
                    ·
                      rfl

theorem cell22_282545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_282545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282545 prefixEnd_282545 := by exact prefixLift 282545
  have htrace : WordTrace (prefixWord ++ tailWord_282545) baseStart_282545 baseEnd_282545 := by
    simpa [prefixWord, tailWord_282545, baseEnd_282545] using wordTrace_append hprefix tailTrace_282545
  have hstable : (prefixWord ++ tailWord_282545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282545).length < 2 ^ (prefixWord ++ tailWord_282545).sum := by decide
  have hdescent : baseEnd_282545 < baseStart_282545 := by decide
  rcases family_descends (prefixWord ++ tailWord_282545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282616 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_282616 : Nat := 118140960795 + 282616 * 2 ^ 59
def prefixEnd_282616 : Nat := 4983230072969 + 3 ^ 40 * 282616 * 2
def baseEnd_282616 : Nat := 96745232434114331533519

theorem tailTrace_282616 : CollatzResearch.WordTrace tailWord_282616 prefixEnd_282616 96745232434114331533519 := by
  unfold tailWord_282616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153926172068986907589851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6871901562758649210119801 5153926172068986907589851)
  ·
    refine ⟨7730889258103480361384777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5153926172068986907589851 7730889258103480361384777)
    ·
      refine ⟨5798166943577610271038583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7730889258103480361384777 5798166943577610271038583)
      ·
        refine ⟨8697250415366415406557875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798166943577610271038583 8697250415366415406557875)
        ·
          refine ⟨13045875623049623109836813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8697250415366415406557875 13045875623049623109836813)
          ·
            refine ⟨4892203358643608666188805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13045875623049623109836813 4892203358643608666188805)
            ·
              refine ⟨917288129745676624910401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4892203358643608666188805 917288129745676624910401)
              ·
                refine ⟨687966097309257468682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917288129745676624910401 687966097309257468682801)
                ·
                  refine ⟨515974572981943101512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687966097309257468682801 515974572981943101512101)
                  ·
                    refine ⟨96745232434114331533519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515974572981943101512101 96745232434114331533519)
                    ·
                      rfl

theorem cell22_282616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_282616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282616 prefixEnd_282616 := by exact prefixLift 282616
  have htrace : WordTrace (prefixWord ++ tailWord_282616) baseStart_282616 baseEnd_282616 := by
    simpa [prefixWord, tailWord_282616, baseEnd_282616] using wordTrace_append hprefix tailTrace_282616
  have hstable : (prefixWord ++ tailWord_282616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282616).length < 2 ^ (prefixWord ++ tailWord_282616).sum := by decide
  have hdescent : baseEnd_282616 < baseStart_282616 := by decide
  rcases family_descends (prefixWord ++ tailWord_282616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282631 : List Nat := [1, 1, 4, 3, 1, 2, 3, 7]
def baseStart_282631 : Nat := 118140960795 + 282631 * 2 ^ 59
def prefixEnd_282631 : Nat := 4983230072969 + 3 ^ 40 * 282631 * 2
def baseEnd_282631 : Nat := 10750040804517699156497

theorem tailTrace_282631 : CollatzResearch.WordTrace tailWord_282631 prefixEnd_282631 10750040804517699156497 := by
  unfold tailWord_282631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308399439083631376975747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6872266292722420917983831 10308399439083631376975747)
  ·
    refine ⟨15462599158625447065463621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10308399439083631376975747 15462599158625447065463621)
    ·
      refine ⟨2899237342242271324774429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15462599158625447065463621 2899237342242271324774429)
      ·
        refine ⟨1087214003340851746790411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2899237342242271324774429 1087214003340851746790411)
        ·
          refine ⟨1630821005011277620185617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087214003340851746790411 1630821005011277620185617)
          ·
            refine ⟨1223115753758458215139213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630821005011277620185617 1223115753758458215139213)
            ·
              refine ⟨458668407659421830677205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223115753758458215139213 458668407659421830677205)
              ·
                refine ⟨10750040804517699156497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 458668407659421830677205 10750040804517699156497)
                ·
                  rfl

theorem cell22_282631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 7].length) (baseStart_282631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282631 prefixEnd_282631 := by exact prefixLift 282631
  have htrace : WordTrace (prefixWord ++ tailWord_282631) baseStart_282631 baseEnd_282631 := by
    simpa [prefixWord, tailWord_282631, baseEnd_282631] using wordTrace_append hprefix tailTrace_282631
  have hstable : (prefixWord ++ tailWord_282631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282631).length < 2 ^ (prefixWord ++ tailWord_282631).sum := by decide
  have hdescent : baseEnd_282631 < baseStart_282631 := by decide
  rcases family_descends (prefixWord ++ tailWord_282631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282637 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 6]
def baseStart_282637 : Nat := 118140960795 + 282637 * 2 ^ 59
def prefixEnd_282637 : Nat := 4983230072969 + 3 ^ 40 * 282637 * 2
def baseEnd_282637 : Nat := 32250807054425758919485

theorem tailTrace_282637 : CollatzResearch.WordTrace tailWord_282637 prefixEnd_282637 32250807054425758919485 := by
  unfold tailWord_282637
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308618277061894401694165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6872412184707929601129443 10308618277061894401694165)
  ·
    refine ⟨241608240868638150039707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10308618277061894401694165 241608240868638150039707)
    ·
      refine ⟨362412361302957225059561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241608240868638150039707 362412361302957225059561)
      ·
        refine ⟨271809270977217918794671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362412361302957225059561 271809270977217918794671)
        ·
          refine ⟨407713906465826878192007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271809270977217918794671 407713906465826878192007)
          ·
            refine ⟨611570859698740317288011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407713906465826878192007 611570859698740317288011)
            ·
              refine ⟨917356289548110475932017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611570859698740317288011 917356289548110475932017)
              ·
                refine ⟨688017217161082856949013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917356289548110475932017 688017217161082856949013)
                ·
                  refine ⟨32250807054425758919485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 688017217161082856949013 32250807054425758919485)
                  ·
                    rfl

theorem cell22_282637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_282637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282637 prefixEnd_282637 := by exact prefixLift 282637
  have htrace : WordTrace (prefixWord ++ tailWord_282637) baseStart_282637 baseEnd_282637 := by
    simpa [prefixWord, tailWord_282637, baseEnd_282637] using wordTrace_append hprefix tailTrace_282637
  have hstable : (prefixWord ++ tailWord_282637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282637).length < 2 ^ (prefixWord ++ tailWord_282637).sum := by decide
  have hdescent : baseEnd_282637 < baseStart_282637 := by decide
  rcases family_descends (prefixWord ++ tailWord_282637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282680 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_282680 : Nat := 118140960795 + 282680 * 2 ^ 59
def prefixEnd_282680 : Nat := 4983230072969 + 3 ^ 40 * 282680 * 2
def baseEnd_282680 : Nat := 96767140942039497933323

theorem tailTrace_282680 : CollatzResearch.WordTrace tailWord_282680 prefixEnd_282680 96767140942039497933323 := by
  unfold tailWord_282680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155093307953056372754747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6873457743937408497006329 5155093307953056372754747)
  ·
    refine ⟨7732639961929584559132121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5155093307953056372754747 7732639961929584559132121)
    ·
      refine ⟨5799479971447188419349091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7732639961929584559132121 5799479971447188419349091)
      ·
        refine ⟨8699219957170782629023637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5799479971447188419349091 8699219957170782629023637)
        ·
          refine ⟨407775935492380435735483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8699219957170782629023637 407775935492380435735483)
          ·
            refine ⟨611663903238570653603225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407775935492380435735483 611663903238570653603225)
            ·
              refine ⟨458747927428927990202419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611663903238570653603225 458747927428927990202419)
              ·
                refine ⟨688121891143391985303629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458747927428927990202419 688121891143391985303629)
                ·
                  refine ⟨258045709178771994488861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688121891143391985303629 258045709178771994488861)
                  ·
                    refine ⟨96767140942039497933323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258045709178771994488861 96767140942039497933323)
                    ·
                      rfl

theorem cell22_282680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_282680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282680 prefixEnd_282680 := by exact prefixLift 282680
  have htrace : WordTrace (prefixWord ++ tailWord_282680) baseStart_282680 baseEnd_282680 := by
    simpa [prefixWord, tailWord_282680, baseEnd_282680] using wordTrace_append hprefix tailTrace_282680
  have hstable : (prefixWord ++ tailWord_282680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282680).length < 2 ^ (prefixWord ++ tailWord_282680).sum := by decide
  have hdescent : baseEnd_282680 < baseStart_282680 := by decide
  rcases family_descends (prefixWord ++ tailWord_282680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282710 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_282710 : Nat := 118140960795 + 282710 * 2 ^ 59
def prefixEnd_282710 : Nat := 4983230072969 + 3 ^ 40 * 282710 * 2
def baseEnd_282710 : Nat := 32259136851709806561077

theorem tailTrace_282710 : CollatzResearch.WordTrace tailWord_282710 prefixEnd_282710 32259136851709806561077 := by
  unfold tailWord_282710
  simp only [CollatzResearch.WordTrace]
  refine ⟨644455050362339241818849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6874187203864951912734389 644455050362339241818849)
  ·
    refine ⟨483341287771754431364137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644455050362339241818849 483341287771754431364137)
    ·
      refine ⟨362505965828815823523103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483341287771754431364137 362505965828815823523103)
      ·
        refine ⟨543758948743223735284655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362505965828815823523103 543758948743223735284655)
        ·
          refine ⟨815638423114835602926983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543758948743223735284655 815638423114835602926983)
          ·
            refine ⟨1223457634672253404390475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815638423114835602926983 1223457634672253404390475)
            ·
              refine ⟨1835186452008380106585713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223457634672253404390475 1835186452008380106585713)
              ·
                refine ⟨1376389839006285079939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835186452008380106585713 1376389839006285079939285)
                ·
                  refine ⟨32259136851709806561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1376389839006285079939285 32259136851709806561077)
                  ·
                    rfl

theorem cell22_282710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_282710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282710 prefixEnd_282710 := by exact prefixLift 282710
  have htrace : WordTrace (prefixWord ++ tailWord_282710) baseStart_282710 baseEnd_282710 := by
    simpa [prefixWord, tailWord_282710, baseEnd_282710] using wordTrace_append hprefix tailTrace_282710
  have hstable : (prefixWord ++ tailWord_282710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282710).length < 2 ^ (prefixWord ++ tailWord_282710).sum := by decide
  have hdescent : baseEnd_282710 < baseStart_282710 := by decide
  rcases family_descends (prefixWord ++ tailWord_282710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282723 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 1, 4]
def baseStart_282723 : Nat := 118140960795 + 282723 * 2 ^ 59
def prefixEnd_282723 : Nat := 4983230072969 + 3 ^ 40 * 282723 * 2
def baseEnd_282723 : Nat := 96781860720801719108191

theorem tailTrace_282723 : CollatzResearch.WordTrace tailWord_282723 prefixEnd_282723 96781860720801719108191 := by
  unfold tailWord_282723
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311754954750331089324823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6874503303166887392883215 10311754954750331089324823)
  ·
    refine ⟨15467632432125496633987235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311754954750331089324823 15467632432125496633987235)
    ·
      refine ⟨23201448648188244950980853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467632432125496633987235 23201448648188244950980853)
      ·
        refine ⟨2175135810767647964154455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23201448648188244950980853 2175135810767647964154455)
        ·
          refine ⟨3262703716151471946231683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175135810767647964154455 3262703716151471946231683)
          ·
            refine ⟨4894055574227207919347525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262703716151471946231683 4894055574227207919347525)
            ·
              refine ⟨917635420167601484877661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4894055574227207919347525 917635420167601484877661)
              ·
                refine ⟨344113282562850556829123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917635420167601484877661 344113282562850556829123)
                ·
                  refine ⟨516169923844275835243685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344113282562850556829123 516169923844275835243685)
                  ·
                    refine ⟨96781860720801719108191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516169923844275835243685 96781860720801719108191)
                    ·
                      rfl

theorem cell22_282723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_282723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282723 prefixEnd_282723 := by exact prefixLift 282723
  have htrace : WordTrace (prefixWord ++ tailWord_282723) baseStart_282723 baseEnd_282723 := by
    simpa [prefixWord, tailWord_282723, baseEnd_282723] using wordTrace_append hprefix tailTrace_282723
  have hstable : (prefixWord ++ tailWord_282723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282723).length < 2 ^ (prefixWord ++ tailWord_282723).sum := by decide
  have hdescent : baseEnd_282723 < baseStart_282723 := by decide
  rcases family_descends (prefixWord ++ tailWord_282723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282738 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_282738 : Nat := 118140960795 + 282738 * 2 ^ 59
def prefixEnd_282738 : Nat := 4983230072969 + 3 ^ 40 * 282738 * 2
def baseEnd_282738 : Nat := 32262331842448893327715

theorem tailTrace_282738 : CollatzResearch.WordTrace tailWord_282738 prefixEnd_282738 32262331842448893327715 := by
  unfold tailWord_282738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578075512423997162780217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6874868033130659100747245 2578075512423997162780217)
  ·
    refine ⟨1933556634317997872085163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2578075512423997162780217 1933556634317997872085163)
    ·
      refine ⟨2900334951476996808127745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933556634317997872085163 2900334951476996808127745)
      ·
        refine ⟨2175251213607747606095809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2900334951476996808127745 2175251213607747606095809)
        ·
          refine ⟨1631438410205810704571857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175251213607747606095809 1631438410205810704571857)
          ·
            refine ⟨1223578807654358028428893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1631438410205810704571857 1223578807654358028428893)
            ·
              refine ⟨458842052870384260660835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223578807654358028428893 458842052870384260660835)
              ·
                refine ⟨688263079305576390991253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458842052870384260660835 688263079305576390991253)
                ·
                  refine ⟨32262331842448893327715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 688263079305576390991253 32262331842448893327715)
                  ·
                    rfl

theorem cell22_282738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_282738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282738 prefixEnd_282738 := by exact prefixLift 282738
  have htrace : WordTrace (prefixWord ++ tailWord_282738) baseStart_282738 baseEnd_282738 := by
    simpa [prefixWord, tailWord_282738, baseEnd_282738] using wordTrace_append hprefix tailTrace_282738
  have hstable : (prefixWord ++ tailWord_282738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282738).length < 2 ^ (prefixWord ++ tailWord_282738).sum := by decide
  have hdescent : baseEnd_282738 < baseStart_282738 := by decide
  rcases family_descends (prefixWord ++ tailWord_282738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282768 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_282768 : Nat := 118140960795 + 282768 * 2 ^ 59
def prefixEnd_282768 : Nat := 4983230072969 + 3 ^ 40 * 282768 * 2
def baseEnd_282768 : Nat := 96797265140436601733053

theorem tailTrace_282768 : CollatzResearch.WordTrace tailWord_282768 prefixEnd_282768 96797265140436601733053 := by
  unfold tailWord_282768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156698119793651887356479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6875597493058202516475305 5156698119793651887356479)
  ·
    refine ⟨7735047179690477831034719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156698119793651887356479 7735047179690477831034719)
    ·
      refine ⟨11602570769535716746552079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735047179690477831034719 11602570769535716746552079)
      ·
        refine ⟨17403856154303575119828119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11602570769535716746552079 17403856154303575119828119)
        ·
          refine ⟨26105784231455362679742179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17403856154303575119828119 26105784231455362679742179)
          ·
            refine ⟨39158676347183044019613269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26105784231455362679742179 39158676347183044019613269)
            ·
              refine ⟨458890738443551297104843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 39158676347183044019613269 458890738443551297104843)
              ·
                refine ⟨688336107665326945657265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458890738443551297104843 688336107665326945657265)
                ·
                  refine ⟨516252080748995209242949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688336107665326945657265 516252080748995209242949)
                  ·
                    refine ⟨96797265140436601733053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516252080748995209242949 96797265140436601733053)
                    ·
                      rfl

theorem cell22_282768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_282768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282768 prefixEnd_282768 := by exact prefixLift 282768
  have htrace : WordTrace (prefixWord ++ tailWord_282768) baseStart_282768 baseEnd_282768 := by
    simpa [prefixWord, tailWord_282768, baseEnd_282768] using wordTrace_append hprefix tailTrace_282768
  have hstable : (prefixWord ++ tailWord_282768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282768).length < 2 ^ (prefixWord ++ tailWord_282768).sum := by decide
  have hdescent : baseEnd_282768 < baseStart_282768 := by decide
  rcases family_descends (prefixWord ++ tailWord_282768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282817 : List Nat := [1, 2, 6, 1, 2, 1, 3, 6]
def baseStart_282817 : Nat := 118140960795 + 282817 * 2 ^ 59
def prefixEnd_282817 : Nat := 4983230072969 + 3 ^ 40 * 282817 * 2
def baseEnd_282817 : Nat := 10757115426868534139767

theorem tailTrace_282817 : CollatzResearch.WordTrace tailWord_282817 prefixEnd_282817 10757115426868534139767 := by
  unfold tailWord_282817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10315183416409785143246705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6876788944273190095497803 10315183416409785143246705)
  ·
    refine ⟨7736387562307338857435029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10315183416409785143246705 7736387562307338857435029)
    ·
      refine ⟨362643166983156508942267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7736387562307338857435029 362643166983156508942267)
      ·
        refine ⟨543964750474734763413401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362643166983156508942267 543964750474734763413401)
        ·
          refine ⟨407973562856051072560051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543964750474734763413401 407973562856051072560051)
          ·
            refine ⟨611960344284076608840077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407973562856051072560051 611960344284076608840077)
            ·
              refine ⟨229485129106528728315029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611960344284076608840077 229485129106528728315029)
              ·
                refine ⟨10757115426868534139767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229485129106528728315029 10757115426868534139767)
                ·
                  rfl

theorem cell22_282817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 6].length) (baseStart_282817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282817 prefixEnd_282817 := by exact prefixLift 282817
  have htrace : WordTrace (prefixWord ++ tailWord_282817) baseStart_282817 baseEnd_282817 := by
    simpa [prefixWord, tailWord_282817, baseEnd_282817] using wordTrace_append hprefix tailTrace_282817
  have hstable : (prefixWord ++ tailWord_282817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282817).length < 2 ^ (prefixWord ++ tailWord_282817).sum := by decide
  have hdescent : baseEnd_282817 < baseStart_282817 := by decide
  rcases family_descends (prefixWord ++ tailWord_282817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282845 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 7]
def baseStart_282845 : Nat := 118140960795 + 282845 * 2 ^ 59
def prefixEnd_282845 : Nat := 4983230072969 + 3 ^ 40 * 282845 * 2
def baseEnd_282845 : Nat := 32274541271344689185939

theorem tailTrace_282845 : CollatzResearch.WordTrace tailWord_282845 prefixEnd_282845 32274541271344689185939 := by
  unfold tailWord_282845
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316204660308345925265989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6877469773538897283510659 10316204660308345925265989)
  ·
    refine ⟨1934288373807814860987373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10316204660308345925265989 1934288373807814860987373)
    ·
      refine ⟨725358140177930572870265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1934288373807814860987373 725358140177930572870265)
      ·
        refine ⟨544018605133447929652699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725358140177930572870265 544018605133447929652699)
        ·
          refine ⟨816027907700171894479049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544018605133447929652699 816027907700171894479049)
          ·
            refine ⟨612020930775128920859287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816027907700171894479049 612020930775128920859287)
            ·
              refine ⟨918031396162693381288931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612020930775128920859287 918031396162693381288931)
              ·
                refine ⟨1377047094244040071933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918031396162693381288931 1377047094244040071933397)
                ·
                  refine ⟨32274541271344689185939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1377047094244040071933397 32274541271344689185939)
                  ·
                    rfl

theorem cell22_282845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_282845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282845 prefixEnd_282845 := by exact prefixLift 282845
  have htrace : WordTrace (prefixWord ++ tailWord_282845) baseStart_282845 baseEnd_282845 := by
    simpa [prefixWord, tailWord_282845, baseEnd_282845] using wordTrace_append hprefix tailTrace_282845
  have hstable : (prefixWord ++ tailWord_282845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282845).length < 2 ^ (prefixWord ++ tailWord_282845).sum := by decide
  have hdescent : baseEnd_282845 < baseStart_282845 := by decide
  rcases family_descends (prefixWord ++ tailWord_282845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282926 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_282926 : Nat := 118140960795 + 282926 * 2 ^ 59
def prefixEnd_282926 : Nat := 4983230072969 + 3 ^ 40 * 282926 * 2
def baseEnd_282926 : Nat := 96851351769376856282569

theorem tailTrace_282926 : CollatzResearch.WordTrace tailWord_282926 prefixEnd_282926 96851351769376856282569 := by
  unfold tailWord_282926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289894871626862094870579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6879439315343264505976421 1289894871626862094870579)
  ·
    refine ⟨1934842307440293142305869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289894871626862094870579 1934842307440293142305869)
    ·
      refine ⟨725565865290109928364701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1934842307440293142305869 725565865290109928364701)
      ·
        refine ⟨272087199483791223136763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 725565865290109928364701 272087199483791223136763)
        ·
          refine ⟨408130799225686834705145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272087199483791223136763 408130799225686834705145)
          ·
            refine ⟨306098099419265126028859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408130799225686834705145 306098099419265126028859)
            ·
              refine ⟨459147149128897689043289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306098099419265126028859 459147149128897689043289)
              ·
                refine ⟨344360361846673266782467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459147149128897689043289 344360361846673266782467)
                ·
                  refine ⟨516540542770009900173701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344360361846673266782467 516540542770009900173701)
                  ·
                    refine ⟨96851351769376856282569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516540542770009900173701 96851351769376856282569)
                    ·
                      rfl

theorem cell22_282926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_282926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282926 prefixEnd_282926 := by exact prefixLift 282926
  have htrace : WordTrace (prefixWord ++ tailWord_282926) baseStart_282926 baseEnd_282926 := by
    simpa [prefixWord, tailWord_282926, baseEnd_282926] using wordTrace_append hprefix tailTrace_282926
  have hstable : (prefixWord ++ tailWord_282926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282926).length < 2 ^ (prefixWord ++ tailWord_282926).sum := by decide
  have hdescent : baseEnd_282926 < baseStart_282926 := by decide
  rcases family_descends (prefixWord ++ tailWord_282926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282937 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_282937 : Nat := 118140960795 + 282937 * 2 ^ 59
def prefixEnd_282937 : Nat := 4983230072969 + 3 ^ 40 * 282937 * 2
def baseEnd_282937 : Nat := 96855117294176494257535

theorem tailTrace_282937 : CollatzResearch.WordTrace tailWord_282937 prefixEnd_282937 96855117294176494257535 := by
  unfold tailWord_282937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319560175975045637615065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6879706783983363758410043 10319560175975045637615065)
  ·
    refine ⟨7739670131981284228211299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10319560175975045637615065 7739670131981284228211299)
    ·
      refine ⟨11609505197971926342316949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7739670131981284228211299 11609505197971926342316949)
      ·
        refine ⟨544195556154934047296107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11609505197971926342316949 544195556154934047296107)
        ·
          refine ⟨816293334232401070944161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544195556154934047296107 816293334232401070944161)
          ·
            refine ⟨612220000674300803208121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816293334232401070944161 612220000674300803208121)
            ·
              refine ⟨459165000505725602406091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612220000674300803208121 459165000505725602406091)
              ·
                refine ⟨688747500758588403609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459165000505725602406091 688747500758588403609137)
                ·
                  refine ⟨516560625568941302706853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688747500758588403609137 516560625568941302706853)
                  ·
                    refine ⟨96855117294176494257535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516560625568941302706853 96855117294176494257535)
                    ·
                      rfl

theorem cell22_282937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_282937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282937 prefixEnd_282937 := by exact prefixLift 282937
  have htrace : WordTrace (prefixWord ++ tailWord_282937) baseStart_282937 baseEnd_282937 := by
    simpa [prefixWord, tailWord_282937, baseEnd_282937] using wordTrace_append hprefix tailTrace_282937
  have hstable : (prefixWord ++ tailWord_282937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282937).length < 2 ^ (prefixWord ++ tailWord_282937).sum := by decide
  have hdescent : baseEnd_282937 < baseStart_282937 := by decide
  rcases family_descends (prefixWord ++ tailWord_282937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282980 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_282980 : Nat := 118140960795 + 282980 * 2 ^ 59
def prefixEnd_282980 : Nat := 4983230072969 + 3 ^ 40 * 282980 * 2
def baseEnd_282980 : Nat := 32289945690979571810801

theorem tailTrace_282980 : CollatzResearch.WordTrace tailWord_282980 prefixEnd_282980 32289945690979571810801 := by
  unfold tailWord_282980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160564257409631990715197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6880752343212842654286929 5160564257409631990715197)
  ·
    refine ⟨1935211596528611996518199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5160564257409631990715197 1935211596528611996518199)
    ·
      refine ⟨2902817394792917994777299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935211596528611996518199 2902817394792917994777299)
      ·
        refine ⟨4354226092189376992165949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2902817394792917994777299 4354226092189376992165949)
        ·
          refine ⟨1632834784571016372062231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4354226092189376992165949 1632834784571016372062231)
          ·
            refine ⟨2449252176856524558093347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632834784571016372062231 2449252176856524558093347)
            ·
              refine ⟨3673878265284786837140021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449252176856524558093347 3673878265284786837140021)
              ·
                refine ⟨344426087370448765981877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3673878265284786837140021 344426087370448765981877)
                ·
                  refine ⟨32289945690979571810801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344426087370448765981877 32289945690979571810801)
                  ·
                    rfl

theorem cell22_282980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_282980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_282980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_282980 prefixEnd_282980 := by exact prefixLift 282980
  have htrace : WordTrace (prefixWord ++ tailWord_282980) baseStart_282980 baseEnd_282980 := by
    simpa [prefixWord, tailWord_282980, baseEnd_282980] using wordTrace_append hprefix tailTrace_282980
  have hstable : (prefixWord ++ tailWord_282980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282980).length < 2 ^ (prefixWord ++ tailWord_282980).sum := by decide
  have hdescent : baseEnd_282980 < baseStart_282980 := by decide
  rcases family_descends (prefixWord ++ tailWord_282980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283057 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_283057 : Nat := 118140960795 + 283057 * 2 ^ 59
def prefixEnd_283057 : Nat := 4983230072969 + 3 ^ 40 * 283057 * 2
def baseEnd_283057 : Nat := 96896195746536181257167

theorem tailTrace_283057 : CollatzResearch.WordTrace tailWord_283057 prefixEnd_283057 96896195746536181257167 := by
  unfold tailWord_283057
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323936935540306131983425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6882624623693537421322283 10323936935540306131983425)
  ·
    refine ⟨7742952701655229598987569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10323936935540306131983425 7742952701655229598987569)
    ·
      refine ⟨5807214526241422199240677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7742952701655229598987569 5807214526241422199240677)
      ·
        refine ⟨1088852723670266662357627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5807214526241422199240677 1088852723670266662357627)
        ·
          refine ⟨1633279085505399993536441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088852723670266662357627 1633279085505399993536441)
          ·
            refine ⟨1224959314129049995152331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633279085505399993536441 1224959314129049995152331)
            ·
              refine ⟨1837438971193574992728497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224959314129049995152331 1837438971193574992728497)
              ·
                refine ⟨1378079228395181244546373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1837438971193574992728497 1378079228395181244546373)
                ·
                  refine ⟨258389855324096483352445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378079228395181244546373 258389855324096483352445)
                  ·
                    refine ⟨96896195746536181257167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258389855324096483352445 96896195746536181257167)
                    ·
                      rfl

theorem cell22_283057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_283057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283057 prefixEnd_283057 := by exact prefixLift 283057
  have htrace : WordTrace (prefixWord ++ tailWord_283057) baseStart_283057 baseEnd_283057 := by
    simpa [prefixWord, tailWord_283057, baseEnd_283057] using wordTrace_append hprefix tailTrace_283057
  have hstable : (prefixWord ++ tailWord_283057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283057).length < 2 ^ (prefixWord ++ tailWord_283057).sum := by decide
  have hdescent : baseEnd_283057 < baseStart_283057 := by decide
  rcases family_descends (prefixWord ++ tailWord_283057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283070 : List Nat := [4, 2, 1, 1, 1, 1, 12]
def baseStart_283070 : Nat := 118140960795 + 283070 * 2 ^ 59
def prefixEnd_283070 : Nat := 4983230072969 + 3 ^ 40 * 283070 * 2
def baseEnd_283070 : Nat := 3588912811563277062301

theorem tailTrace_283070 : CollatzResearch.WordTrace tailWord_283070 prefixEnd_283070 3588912811563277062301 := by
  unfold tailWord_283070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290551385561651169025833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6882940722995472901471109 1290551385561651169025833)
  ·
    refine ⟨967913539171238376769375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1290551385561651169025833 967913539171238376769375)
    ·
      refine ⟨1451870308756857565154063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967913539171238376769375 1451870308756857565154063)
      ·
        refine ⟨2177805463135286347731095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451870308756857565154063 2177805463135286347731095)
        ·
          refine ⟨3266708194702929521596643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177805463135286347731095 3266708194702929521596643)
          ·
            refine ⟨4900062292054394282394965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266708194702929521596643 4900062292054394282394965)
            ·
              refine ⟨3588912811563277062301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 4900062292054394282394965 3588912811563277062301)
              ·
                rfl

theorem cell22_283070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 12].length) (baseStart_283070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283070 prefixEnd_283070 := by exact prefixLift 283070
  have htrace : WordTrace (prefixWord ++ tailWord_283070) baseStart_283070 baseEnd_283070 := by
    simpa [prefixWord, tailWord_283070, baseEnd_283070] using wordTrace_append hprefix tailTrace_283070
  have hstable : (prefixWord ++ tailWord_283070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283070).length < 2 ^ (prefixWord ++ tailWord_283070).sum := by decide
  have hdescent : baseEnd_283070 < baseStart_283070 := by decide
  rcases family_descends (prefixWord ++ tailWord_283070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283076 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_283076 : Nat := 118140960795 + 283076 * 2 ^ 59
def prefixEnd_283076 : Nat := 4983230072969 + 3 ^ 40 * 283076 * 2
def baseEnd_283076 : Nat := 32300899944942155010703

theorem tailTrace_283076 : CollatzResearch.WordTrace tailWord_283076 prefixEnd_283076 32300899944942155010703 := by
  unfold tailWord_283076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162314961235736188462541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6883086614980981584616721 5162314961235736188462541)
  ·
    refine ⟨1935868110463401070673453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5162314961235736188462541 1935868110463401070673453)
    ·
      refine ⟨725950541423775401502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1935868110463401070673453 725950541423775401502545)
      ·
        refine ⟨544462906067831551126909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725950541423775401502545 544462906067831551126909)
        ·
          refine ⟨204173589775436831672591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544462906067831551126909 204173589775436831672591)
          ·
            refine ⟨306260384663155247508887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204173589775436831672591 306260384663155247508887)
            ·
              refine ⟨459390576994732871263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306260384663155247508887 459390576994732871263331)
              ·
                refine ⟨689085865492099306894997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459390576994732871263331 689085865492099306894997)
                ·
                  refine ⟨32300899944942155010703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 689085865492099306894997 32300899944942155010703)
                  ·
                    rfl

theorem cell22_283076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_283076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283076 prefixEnd_283076 := by exact prefixLift 283076
  have htrace : WordTrace (prefixWord ++ tailWord_283076) baseStart_283076 baseEnd_283076 := by
    simpa [prefixWord, tailWord_283076, baseEnd_283076] using wordTrace_append hprefix tailTrace_283076
  have hstable : (prefixWord ++ tailWord_283076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283076).length < 2 ^ (prefixWord ++ tailWord_283076).sum := by decide
  have hdescent : baseEnd_283076 < baseStart_283076 := by decide
  rcases family_descends (prefixWord ++ tailWord_283076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283119 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 1, 3]
def baseStart_283119 : Nat := 118140960795 + 283119 * 2 ^ 59
def prefixEnd_283119 : Nat := 4983230072969 + 3 ^ 40 * 283119 * 2
def baseEnd_283119 : Nat := 96917419613588686206977

theorem tailTrace_283119 : CollatzResearch.WordTrace tailWord_283119 prefixEnd_283119 96917419613588686206977 := by
  unfold tailWord_283119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326198261315690720740411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6884132174210460480493607 10326198261315690720740411)
  ·
    refine ⟨15489297391973536081110617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10326198261315690720740411 15489297391973536081110617)
    ·
      refine ⟨11616973043980152060832963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489297391973536081110617 11616973043980152060832963)
      ·
        refine ⟨17425459565970228091249445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11616973043980152060832963 17425459565970228091249445)
        ·
          refine ⟨3267273668619417767109271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17425459565970228091249445 3267273668619417767109271)
          ·
            refine ⟨4900910502929126650663907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267273668619417767109271 4900910502929126650663907)
            ·
              refine ⟨7351365754393689975995861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900910502929126650663907 7351365754393689975995861)
              ·
                refine ⟨172297634868602108812403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7351365754393689975995861 172297634868602108812403)
                ·
                  refine ⟨258446452302903163218605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172297634868602108812403 258446452302903163218605)
                  ·
                    refine ⟨96917419613588686206977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258446452302903163218605 96917419613588686206977)
                    ·
                      rfl

theorem cell22_283119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_283119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283119 prefixEnd_283119 := by exact prefixLift 283119
  have htrace : WordTrace (prefixWord ++ tailWord_283119) baseStart_283119 baseEnd_283119 := by
    simpa [prefixWord, tailWord_283119, baseEnd_283119] using wordTrace_append hprefix tailTrace_283119
  have hstable : (prefixWord ++ tailWord_283119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283119).length < 2 ^ (prefixWord ++ tailWord_283119).sum := by decide
  have hdescent : baseEnd_283119 < baseStart_283119 := by decide
  rcases family_descends (prefixWord ++ tailWord_283119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283147 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_283147 : Nat := 118140960795 + 283147 * 2 ^ 59
def prefixEnd_283147 : Nat := 4983230072969 + 3 ^ 40 * 283147 * 2
def baseEnd_283147 : Nat := 96927004585805946506891

theorem tailTrace_283147 : CollatzResearch.WordTrace tailWord_283147 prefixEnd_283147 96927004585805946506891 := by
  unfold tailWord_283147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327219505214251502759695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6884813003476167668506463 10327219505214251502759695)
  ·
    refine ⟨15490829257821377254139543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10327219505214251502759695 15490829257821377254139543)
    ·
      refine ⟨23236243886732065881209315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15490829257821377254139543 23236243886732065881209315)
      ·
        refine ⟨34854365830098098821813973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23236243886732065881209315 34854365830098098821813973)
        ·
          refine ⟨816899199142924191136265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34854365830098098821813973 816899199142924191136265)
          ·
            refine ⟨612674399357193143352199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816899199142924191136265 612674399357193143352199)
            ·
              refine ⟨919011599035789715028299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612674399357193143352199 919011599035789715028299)
              ·
                refine ⟨1378517398553684572542449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919011599035789715028299 1378517398553684572542449)
                ·
                  refine ⟨1033888048915263429406837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378517398553684572542449 1033888048915263429406837)
                  ·
                    refine ⟨96927004585805946506891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1033888048915263429406837 96927004585805946506891)
                    ·
                      rfl

theorem cell22_283147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_283147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283147 prefixEnd_283147 := by exact prefixLift 283147
  have htrace : WordTrace (prefixWord ++ tailWord_283147) baseStart_283147 baseEnd_283147 := by
    simpa [prefixWord, tailWord_283147, baseEnd_283147] using wordTrace_append hprefix tailTrace_283147
  have hstable : (prefixWord ++ tailWord_283147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283147).length < 2 ^ (prefixWord ++ tailWord_283147).sum := by decide
  have hdescent : baseEnd_283147 < baseStart_283147 := by decide
  rcases family_descends (prefixWord ++ tailWord_283147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283162 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_283162 : Nat := 118140960795 + 283162 * 2 ^ 59
def prefixEnd_283162 : Nat := 4983230072969 + 3 ^ 40 * 283162 * 2
def baseEnd_283162 : Nat := 96932139392350907381845

theorem tailTrace_283162 : CollatzResearch.WordTrace tailWord_283162 prefixEnd_283162 96932139392350907381845 := by
  unfold tailWord_283162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581941650039977266138935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6885177733439939376370493 2581941650039977266138935)
  ·
    refine ⟨3872912475059965899208403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2581941650039977266138935 3872912475059965899208403)
    ·
      refine ⟨5809368712589948848812605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872912475059965899208403 5809368712589948848812605)
      ·
        refine ⟨2178513267221230818304727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5809368712589948848812605 2178513267221230818304727)
        ·
          refine ⟨3267769900831846227457091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178513267221230818304727 3267769900831846227457091)
          ·
            refine ⟨4901654851247769341185637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267769900831846227457091 4901654851247769341185637)
            ·
              refine ⟨919060284608956751472307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4901654851247769341185637 919060284608956751472307)
              ·
                refine ⟨1378590426913435127208461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919060284608956751472307 1378590426913435127208461)
                ·
                  refine ⟨516971410092538172703173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1378590426913435127208461 516971410092538172703173)
                  ·
                    refine ⟨96932139392350907381845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516971410092538172703173 96932139392350907381845)
                    ·
                      rfl

theorem cell22_283162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_283162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283162 prefixEnd_283162 := by exact prefixLift 283162
  have htrace : WordTrace (prefixWord ++ tailWord_283162) baseStart_283162 baseEnd_283162 := by
    simpa [prefixWord, tailWord_283162, baseEnd_283162] using wordTrace_append hprefix tailTrace_283162
  have hstable : (prefixWord ++ tailWord_283162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283162).length < 2 ^ (prefixWord ++ tailWord_283162).sum := by decide
  have hdescent : baseEnd_283162 < baseStart_283162 := by decide
  rcases family_descends (prefixWord ++ tailWord_283162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283194 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_283194 : Nat := 118140960795 + 283194 * 2 ^ 59
def prefixEnd_283194 : Nat := 4983230072969 + 3 ^ 40 * 283194 * 2
def baseEnd_283194 : Nat := 32314364548771163527249

theorem tailTrace_283194 : CollatzResearch.WordTrace tailWord_283194 prefixEnd_283194 32314364548771163527249 := by
  unfold tailWord_283194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582233434010994632430159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6885955824029319019813757 2582233434010994632430159)
  ·
    refine ⟨3873350151016491948645239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582233434010994632430159 3873350151016491948645239)
    ·
      refine ⟨5810025226524737922967859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873350151016491948645239 5810025226524737922967859)
      ·
        refine ⟨8715037839787106884451789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810025226524737922967859 8715037839787106884451789)
        ·
          refine ⟨3268139189920165081669421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8715037839787106884451789 3268139189920165081669421)
          ·
            refine ⟨1225552196220061905626033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3268139189920165081669421 1225552196220061905626033)
            ·
              refine ⟨919164147165046429219525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225552196220061905626033 919164147165046429219525)
              ·
                refine ⟨172343277593446205478661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 919164147165046429219525 172343277593446205478661)
                ·
                  refine ⟨32314364548771163527249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172343277593446205478661 32314364548771163527249)
                  ·
                    rfl

theorem cell22_283194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_283194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283194 prefixEnd_283194 := by exact prefixLift 283194
  have htrace : WordTrace (prefixWord ++ tailWord_283194) baseStart_283194 baseEnd_283194 := by
    simpa [prefixWord, tailWord_283194, baseEnd_283194] using wordTrace_append hprefix tailTrace_283194
  have hstable : (prefixWord ++ tailWord_283194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283194).length < 2 ^ (prefixWord ++ tailWord_283194).sum := by decide
  have hdescent : baseEnd_283194 < baseStart_283194 := by decide
  rcases family_descends (prefixWord ++ tailWord_283194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283207 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_283207 : Nat := 118140960795 + 283207 * 2 ^ 59
def prefixEnd_283207 : Nat := 4983230072969 + 3 ^ 40 * 283207 * 2
def baseEnd_283207 : Nat := 96947543811985790006707

theorem tailTrace_283207 : CollatzResearch.WordTrace tailWord_283207 prefixEnd_283207 96947543811985790006707 := by
  unfold tailWord_283207
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329407884996881749943875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886271923331254499962583 10329407884996881749943875)
  ·
    refine ⟨15494111827495322624915813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10329407884996881749943875 15494111827495322624915813)
    ·
      refine ⟨2905145967655372992171715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15494111827495322624915813 2905145967655372992171715)
      ·
        refine ⟨4357718951483059488257573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905145967655372992171715 4357718951483059488257573)
        ·
          refine ⟨817072303403073654048295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4357718951483059488257573 817072303403073654048295)
          ·
            refine ⟨1225608455104610481072443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817072303403073654048295 1225608455104610481072443)
            ·
              refine ⟨1838412682656915721608665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225608455104610481072443 1838412682656915721608665)
              ·
                refine ⟨1378809511992686791206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838412682656915721608665 1378809511992686791206499)
                ·
                  refine ⟨2068214267989030186809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378809511992686791206499 2068214267989030186809749)
                  ·
                    refine ⟨96947543811985790006707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2068214267989030186809749 96947543811985790006707)
                    ·
                      rfl

theorem cell22_283207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_283207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283207 prefixEnd_283207 := by exact prefixLift 283207
  have htrace : WordTrace (prefixWord ++ tailWord_283207) baseStart_283207 baseEnd_283207 := by
    simpa [prefixWord, tailWord_283207, baseEnd_283207] using wordTrace_append hprefix tailTrace_283207
  have hstable : (prefixWord ++ tailWord_283207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283207).length < 2 ^ (prefixWord ++ tailWord_283207).sum := by decide
  have hdescent : baseEnd_283207 < baseStart_283207 := by decide
  rcases family_descends (prefixWord ++ tailWord_283207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283228 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_283228 : Nat := 118140960795 + 283228 * 2 ^ 59
def prefixEnd_283228 : Nat := 4983230072969 + 3 ^ 40 * 283228 * 2
def baseEnd_283228 : Nat := 32318244180382911743881

theorem tailTrace_283228 : CollatzResearch.WordTrace tailWord_283228 prefixEnd_283228 32318244180382911743881 := by
  unfold tailWord_283228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165086908960401168229169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6886782545280534890972225 5165086908960401168229169)
  ·
    refine ⟨3873815181720300876171877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5165086908960401168229169 3873815181720300876171877)
    ·
      refine ⟨726340346572556414282227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3873815181720300876171877 726340346572556414282227)
      ·
        refine ⟨1089510519858834621423341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726340346572556414282227 1089510519858834621423341)
        ·
          refine ⟨408566444947062983033753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089510519858834621423341 408566444947062983033753)
          ·
            refine ⟨306424833710297237275315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408566444947062983033753 306424833710297237275315)
            ·
              refine ⟨459637250565445855912973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306424833710297237275315 459637250565445855912973)
              ·
                refine ⟨172363968962042195967365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459637250565445855912973 172363968962042195967365)
                ·
                  refine ⟨32318244180382911743881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172363968962042195967365 32318244180382911743881)
                  ·
                    rfl

theorem cell22_283228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_283228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283228 prefixEnd_283228 := by exact prefixLift 283228
  have htrace : WordTrace (prefixWord ++ tailWord_283228) baseStart_283228 baseEnd_283228 := by
    simpa [prefixWord, tailWord_283228, baseEnd_283228] using wordTrace_append hprefix tailTrace_283228
  have hstable : (prefixWord ++ tailWord_283228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283228).length < 2 ^ (prefixWord ++ tailWord_283228).sum := by decide
  have hdescent : baseEnd_283228 < baseStart_283228 := by decide
  rcases family_descends (prefixWord ++ tailWord_283228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283312 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_283312 : Nat := 118140960795 + 283312 * 2 ^ 59
def prefixEnd_283312 : Nat := 4983230072969 + 3 ^ 40 * 283312 * 2
def baseEnd_283312 : Nat := 32327829152600172043795

theorem tailTrace_283312 : CollatzResearch.WordTrace tailWord_283312 prefixEnd_283312 32327829152600172043795 := by
  unfold tailWord_283312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5166618774808242341258095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6888825033077656455010793 5166618774808242341258095)
  ·
    refine ⟨7749928162212363511887143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5166618774808242341258095 7749928162212363511887143)
    ·
      refine ⟨11624892243318545267830715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749928162212363511887143 11624892243318545267830715)
      ·
        refine ⟨17437338364977817901746073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11624892243318545267830715 17437338364977817901746073)
        ·
          refine ⟨13078003773733363426309555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17437338364977817901746073 13078003773733363426309555)
          ·
            refine ⟨19617005660600045139464333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13078003773733363426309555 19617005660600045139464333)
            ·
              refine ⟨7356377122725016927299125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19617005660600045139464333 7356377122725016927299125)
              ·
                refine ⟨689660355255470336934293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7356377122725016927299125 689660355255470336934293)
                ·
                  refine ⟨32327829152600172043795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 689660355255470336934293 32327829152600172043795)
                  ·
                    rfl

theorem cell22_283312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_283312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283312 prefixEnd_283312 := by exact prefixLift 283312
  have htrace : WordTrace (prefixWord ++ tailWord_283312) baseStart_283312 baseEnd_283312 := by
    simpa [prefixWord, tailWord_283312, baseEnd_283312] using wordTrace_append hprefix tailTrace_283312
  have hstable : (prefixWord ++ tailWord_283312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283312).length < 2 ^ (prefixWord ++ tailWord_283312).sum := by decide
  have hdescent : baseEnd_283312 < baseStart_283312 := by decide
  rcases family_descends (prefixWord ++ tailWord_283312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283348 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_283348 : Nat := 118140960795 + 283348 * 2 ^ 59
def prefixEnd_283348 : Nat := 4983230072969 + 3 ^ 40 * 283348 * 2
def baseEnd_283348 : Nat := 96995810993508422231275

theorem tailTrace_283348 : CollatzResearch.WordTrace tailWord_283348 prefixEnd_283348 96995810993508422231275 := by
  unfold tailWord_283348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167275288743031415413349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6889700384990708553884465 5167275288743031415413349)
  ·
    refine ⟨968864116639318390390003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5167275288743031415413349 968864116639318390390003)
    ·
      refine ⟨1453296174958977585585005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968864116639318390390003 1453296174958977585585005)
      ·
        refine ⟨544986065609616594594377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1453296174958977585585005 544986065609616594594377)
        ·
          refine ⟨408739549207212445945783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544986065609616594594377 408739549207212445945783)
          ·
            refine ⟨613109323810818668918675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408739549207212445945783 613109323810818668918675)
            ·
              refine ⟨919663985716228003378013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613109323810818668918675 919663985716228003378013)
              ·
                refine ⟨344873994643585501266755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919663985716228003378013 344873994643585501266755)
                ·
                  refine ⟨517310991965378251900133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344873994643585501266755 517310991965378251900133)
                  ·
                    refine ⟨96995810993508422231275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517310991965378251900133 96995810993508422231275)
                    ·
                      rfl

theorem cell22_283348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_283348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283348 prefixEnd_283348 := by exact prefixLift 283348
  have htrace : WordTrace (prefixWord ++ tailWord_283348) baseStart_283348 baseEnd_283348 := by
    simpa [prefixWord, tailWord_283348, baseEnd_283348] using wordTrace_append hprefix tailTrace_283348
  have hstable : (prefixWord ++ tailWord_283348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283348).length < 2 ^ (prefixWord ++ tailWord_283348).sum := by decide
  have hdescent : baseEnd_283348 < baseStart_283348 := by decide
  rcases family_descends (prefixWord ++ tailWord_283348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283361 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_283361 : Nat := 118140960795 + 283361 * 2 ^ 59
def prefixEnd_283361 : Nat := 4983230072969 + 3 ^ 40 * 283361 * 2
def baseEnd_283361 : Nat := 97000261159180721656235

theorem tailTrace_283361 : CollatzResearch.WordTrace tailWord_283361 prefixEnd_283361 97000261159180721656235 := by
  unfold tailWord_283361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335024726438966051049937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6890016484292644034033291 10335024726438966051049937)
  ·
    refine ⟨7751268544829224538287453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10335024726438966051049937 7751268544829224538287453)
    ·
      refine ⟨2906725704310959201857795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7751268544829224538287453 2906725704310959201857795)
      ·
        refine ⟨4360088556466438802786693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906725704310959201857795 4360088556466438802786693)
        ·
          refine ⟨817516604337457275522505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4360088556466438802786693 817516604337457275522505)
          ·
            refine ⟨613137453253092956641879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817516604337457275522505 613137453253092956641879)
            ·
              refine ⟨919706179879639434962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613137453253092956641879 919706179879639434962819)
              ·
                refine ⟨1379559269819459152444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919706179879639434962819 1379559269819459152444229)
                ·
                  refine ⟨258667363091148591083293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379559269819459152444229 258667363091148591083293)
                  ·
                    refine ⟨97000261159180721656235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258667363091148591083293 97000261159180721656235)
                    ·
                      rfl

theorem cell22_283361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_283361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283361 prefixEnd_283361 := by exact prefixLift 283361
  have htrace : WordTrace (prefixWord ++ tailWord_283361) baseStart_283361 baseEnd_283361 := by
    simpa [prefixWord, tailWord_283361, baseEnd_283361] using wordTrace_append hprefix tailTrace_283361
  have hstable : (prefixWord ++ tailWord_283361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283361).length < 2 ^ (prefixWord ++ tailWord_283361).sum := by decide
  have hdescent : baseEnd_283361 < baseStart_283361 := by decide
  rcases family_descends (prefixWord ++ tailWord_283361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283387 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_283387 : Nat := 118140960795 + 283387 * 2 ^ 59
def prefixEnd_283387 : Nat := 4983230072969 + 3 ^ 40 * 283387 * 2
def baseEnd_283387 : Nat := 97009161490525320506155

theorem tailTrace_283387 : CollatzResearch.WordTrace tailWord_283387 prefixEnd_283387 97009161490525320506155 := by
  unfold tailWord_283387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335973024344772491496415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6890648682896514994330943 10335973024344772491496415)
  ·
    refine ⟨15503959536517158737244623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10335973024344772491496415 15503959536517158737244623)
    ·
      refine ⟨23255939304775738105866935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15503959536517158737244623 23255939304775738105866935)
      ·
        refine ⟨34883908957163607158800403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23255939304775738105866935 34883908957163607158800403)
        ·
          refine ⟨52325863435745410738200605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34883908957163607158800403 52325863435745410738200605)
          ·
            refine ⟨19622198788404529026825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52325863435745410738200605 19622198788404529026825227)
            ·
              refine ⟨29433298182606793540237841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19622198788404529026825227 29433298182606793540237841)
              ·
                refine ⟨22074973636955095155178381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29433298182606793540237841 22074973636955095155178381)
                ·
                  refine ⟨8278115113858160683191893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22074973636955095155178381 8278115113858160683191893)
                  ·
                    refine ⟨97009161490525320506155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8278115113858160683191893 97009161490525320506155)
                    ·
                      rfl

theorem cell22_283387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_283387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283387 prefixEnd_283387 := by exact prefixLift 283387
  have htrace : WordTrace (prefixWord ++ tailWord_283387) baseStart_283387 baseEnd_283387 := by
    simpa [prefixWord, tailWord_283387, baseEnd_283387] using wordTrace_append hprefix tailTrace_283387
  have hstable : (prefixWord ++ tailWord_283387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283387).length < 2 ^ (prefixWord ++ tailWord_283387).sum := by decide
  have hdescent : baseEnd_283387 < baseStart_283387 := by decide
  rcases family_descends (prefixWord ++ tailWord_283387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283423 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 3, 3]
def baseStart_283423 : Nat := 118140960795 + 283423 * 2 ^ 59
def prefixEnd_283423 : Nat := 4983230072969 + 3 ^ 40 * 283423 * 2
def baseEnd_283423 : Nat := 97021485026233226606045

theorem tailTrace_283423 : CollatzResearch.WordTrace tailWord_283423 prefixEnd_283423 97021485026233226606045 := by
  unfold tailWord_283423
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337286052214350639806923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6891524034809567093204615 10337286052214350639806923)
  ·
    refine ⟨15505929078321525959710385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10337286052214350639806923 15505929078321525959710385)
    ·
      refine ⟨11629446808741144469782789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15505929078321525959710385 11629446808741144469782789)
      ·
        refine ⟨2180521276638964588084273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11629446808741144469782789 2180521276638964588084273)
        ·
          refine ⟨1635390957479223441063205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180521276638964588084273 1635390957479223441063205)
          ·
            refine ⟨306635804527354395199351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1635390957479223441063205 306635804527354395199351)
            ·
              refine ⟨459953706791031592799027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306635804527354395199351 459953706791031592799027)
              ·
                refine ⟨689930560186547389198541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459953706791031592799027 689930560186547389198541)
                ·
                  refine ⟨258723960069955270949453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689930560186547389198541 258723960069955270949453)
                  ·
                    refine ⟨97021485026233226606045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258723960069955270949453 97021485026233226606045)
                    ·
                      rfl

theorem cell22_283423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_283423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283423 prefixEnd_283423 := by exact prefixLift 283423
  have htrace : WordTrace (prefixWord ++ tailWord_283423) baseStart_283423 baseEnd_283423 := by
    simpa [prefixWord, tailWord_283423, baseEnd_283423] using wordTrace_append hprefix tailTrace_283423
  have hstable : (prefixWord ++ tailWord_283423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283423).length < 2 ^ (prefixWord ++ tailWord_283423).sum := by decide
  have hdescent : baseEnd_283423 < baseStart_283423 := by decide
  rcases family_descends (prefixWord ++ tailWord_283423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283496 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_283496 : Nat := 118140960795 + 283496 * 2 ^ 59
def prefixEnd_283496 : Nat := 4983230072969 + 3 ^ 40 * 283496 * 2
def baseEnd_283496 : Nat := 97046474418085369530821

theorem tailTrace_283496 : CollatzResearch.WordTrace tailWord_283496 prefixEnd_283496 97046474418085369530821 := by
  unfold tailWord_283496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169974290474942053607171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6893299053966589404809561 5169974290474942053607171)
  ·
    refine ⟨7754961435712413080410757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169974290474942053607171 7754961435712413080410757)
    ·
      refine ⟨1454055269196077452577017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7754961435712413080410757 1454055269196077452577017)
      ·
        refine ⟨1090541451897058089432763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1454055269196077452577017 1090541451897058089432763)
        ·
          refine ⟨1635812177845587134149145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090541451897058089432763 1635812177845587134149145)
          ·
            refine ⟨1226859133384190350611859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635812177845587134149145 1226859133384190350611859)
            ·
              refine ⟨1840288700076285525917789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226859133384190350611859 1840288700076285525917789)
              ·
                refine ⟨690108262528607072219171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1840288700076285525917789 690108262528607072219171)
                ·
                  refine ⟨1035162393792910608328757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690108262528607072219171 1035162393792910608328757)
                  ·
                    refine ⟨97046474418085369530821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1035162393792910608328757 97046474418085369530821)
                    ·
                      rfl

theorem cell22_283496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_283496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283496 prefixEnd_283496 := by exact prefixLift 283496
  have htrace : WordTrace (prefixWord ++ tailWord_283496) baseStart_283496 baseEnd_283496 := by
    simpa [prefixWord, tailWord_283496, baseEnd_283496] using wordTrace_append hprefix tailTrace_283496
  have hstable : (prefixWord ++ tailWord_283496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283496).length < 2 ^ (prefixWord ++ tailWord_283496).sum := by decide
  have hdescent : baseEnd_283496 < baseStart_283496 := by decide
  rcases family_descends (prefixWord ++ tailWord_283496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283530 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_283530 : Nat := 118140960795 + 283530 * 2 ^ 59
def prefixEnd_283530 : Nat := 4983230072969 + 3 ^ 40 * 283530 * 2
def baseEnd_283530 : Nat := 97058113312920614180717

theorem tailTrace_283530 : CollatzResearch.WordTrace tailWord_283530 prefixEnd_283530 97058113312920614180717 := by
  unfold tailWord_283530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585297165706676978488011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6894125775217805275968029 2585297165706676978488011)
  ·
    refine ⟨3877945748560015467732017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585297165706676978488011 3877945748560015467732017)
    ·
      refine ⟨2908459311420011600799013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877945748560015467732017 2908459311420011600799013)
      ·
        refine ⟨545336120891252175149815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2908459311420011600799013 545336120891252175149815)
        ·
          refine ⟨818004181336878262724723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545336120891252175149815 818004181336878262724723)
          ·
            refine ⟨1227006272005317394087085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818004181336878262724723 1227006272005317394087085)
            ·
              refine ⟨460127352001994022782657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227006272005317394087085 460127352001994022782657)
              ·
                refine ⟨345095514001495517086993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460127352001994022782657 345095514001495517086993)
                ·
                  refine ⟨258821635501121637815245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345095514001495517086993 258821635501121637815245)
                  ·
                    refine ⟨97058113312920614180717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258821635501121637815245 97058113312920614180717)
                    ·
                      rfl

theorem cell22_283530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_283530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283530 prefixEnd_283530 := by exact prefixLift 283530
  have htrace : WordTrace (prefixWord ++ tailWord_283530) baseStart_283530 baseEnd_283530 := by
    simpa [prefixWord, tailWord_283530, baseEnd_283530] using wordTrace_append hprefix tailTrace_283530
  have hstable : (prefixWord ++ tailWord_283530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283530).length < 2 ^ (prefixWord ++ tailWord_283530).sum := by decide
  have hdescent : baseEnd_283530 < baseStart_283530 := by decide
  rcases family_descends (prefixWord ++ tailWord_283530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283539 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_283539 : Nat := 118140960795 + 283539 * 2 ^ 59
def prefixEnd_283539 : Nat := 4983230072969 + 3 ^ 40 * 283539 * 2
def baseEnd_283539 : Nat := 97061194196847590705689

theorem tailTrace_283539 : CollatzResearch.WordTrace tailWord_283539 prefixEnd_283539 97061194196847590705689 := by
  unfold tailWord_283539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341516919794102451029671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6894344613196068300686447 10341516919794102451029671)
  ·
    refine ⟨15512275379691153676544507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341516919794102451029671 15512275379691153676544507)
    ·
      refine ⟨23268413069536730514816761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15512275379691153676544507 23268413069536730514816761)
      ·
        refine ⟨17451309802152547886112571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23268413069536730514816761 17451309802152547886112571)
        ·
          refine ⟨26176964703228821829168857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17451309802152547886112571 26176964703228821829168857)
          ·
            refine ⟨19632723527421616371876643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26176964703228821829168857 19632723527421616371876643)
            ·
              refine ⟨29449085291132424557814965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19632723527421616371876643 29449085291132424557814965)
              ·
                refine ⟨2760851746043664802295153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29449085291132424557814965 2760851746043664802295153)
                ·
                  refine ⟨2070638809532748601721365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760851746043664802295153 2070638809532748601721365)
                  ·
                    refine ⟨97061194196847590705689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2070638809532748601721365 97061194196847590705689)
                    ·
                      rfl

theorem cell22_283539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_283539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283539 prefixEnd_283539 := by exact prefixLift 283539
  have htrace : WordTrace (prefixWord ++ tailWord_283539) baseStart_283539 baseEnd_283539 := by
    simpa [prefixWord, tailWord_283539, baseEnd_283539] using wordTrace_append hprefix tailTrace_283539
  have hstable : (prefixWord ++ tailWord_283539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283539).length < 2 ^ (prefixWord ++ tailWord_283539).sum := by decide
  have hdescent : baseEnd_283539 < baseStart_283539 := by decide
  rcases family_descends (prefixWord ++ tailWord_283539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283575 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 1, 3]
def baseStart_283575 : Nat := 118140960795 + 283575 * 2 ^ 59
def prefixEnd_283575 : Nat := 4983230072969 + 3 ^ 40 * 283575 * 2
def baseEnd_283575 : Nat := 97073517732555496805579

theorem tailTrace_283575 : CollatzResearch.WordTrace tailWord_283575 prefixEnd_283575 97073517732555496805579 := by
  unfold tailWord_283575
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342829947663680599340179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6895219965109120399560119 10342829947663680599340179)
  ·
    refine ⟨15514244921495520899010269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10342829947663680599340179 15514244921495520899010269)
    ·
      refine ⟨5817841845560820337128851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15514244921495520899010269 5817841845560820337128851)
      ·
        refine ⟨8726762768341230505693277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5817841845560820337128851 8726762768341230505693277)
        ·
          refine ⟨3272536038127961439634979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8726762768341230505693277 3272536038127961439634979)
          ·
            refine ⟨4908804057191942159452469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272536038127961439634979 4908804057191942159452469)
            ·
              refine ⟨460200380361744577448669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4908804057191942159452469 460200380361744577448669)
              ·
                refine ⟨172575142635654216543251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460200380361744577448669 172575142635654216543251)
                ·
                  refine ⟨258862713953481324814877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172575142635654216543251 258862713953481324814877)
                  ·
                    refine ⟨97073517732555496805579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258862713953481324814877 97073517732555496805579)
                    ·
                      rfl

theorem cell22_283575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_283575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283575 prefixEnd_283575 := by exact prefixLift 283575
  have htrace : WordTrace (prefixWord ++ tailWord_283575) baseStart_283575 baseEnd_283575 := by
    simpa [prefixWord, tailWord_283575, baseEnd_283575] using wordTrace_append hprefix tailTrace_283575
  have hstable : (prefixWord ++ tailWord_283575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283575).length < 2 ^ (prefixWord ++ tailWord_283575).sum := by decide
  have hdescent : baseEnd_283575 < baseStart_283575 := by decide
  rcases family_descends (prefixWord ++ tailWord_283575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283592 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_283592 : Nat := 118140960795 + 283592 * 2 ^ 59
def prefixEnd_283592 : Nat := 4983230072969 + 3 ^ 40 * 283592 * 2
def baseEnd_283592 : Nat := 97079337179973119130527

theorem tailTrace_283592 : CollatzResearch.WordTrace tailWord_283592 prefixEnd_283592 97079337179973119130527 := by
  unfold tailWord_283592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171724994301046251354515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6895633325734728335139353 5171724994301046251354515)
  ·
    refine ⟨7757587491451569377031773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5171724994301046251354515 7757587491451569377031773)
    ·
      refine ⟨2909095309294338516386915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7757587491451569377031773 2909095309294338516386915)
      ·
        refine ⟨4363642963941507774580373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909095309294338516386915 4363642963941507774580373)
        ·
          refine ⟨204545763934758176933455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4363642963941507774580373 204545763934758176933455)
          ·
            refine ⟨306818645902137265400183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204545763934758176933455 306818645902137265400183)
            ·
              refine ⟨460227968853205898100275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306818645902137265400183 460227968853205898100275)
              ·
                refine ⟨690341953279808847150413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460227968853205898100275 690341953279808847150413)
                ·
                  refine ⟨258878232479928317681405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690341953279808847150413 258878232479928317681405)
                  ·
                    refine ⟨97079337179973119130527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258878232479928317681405 97079337179973119130527)
                    ·
                      rfl

theorem cell22_283592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_283592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283592 prefixEnd_283592 := by exact prefixLift 283592
  have htrace : WordTrace (prefixWord ++ tailWord_283592) baseStart_283592 baseEnd_283592 := by
    simpa [prefixWord, tailWord_283592, baseEnd_283592] using wordTrace_append hprefix tailTrace_283592
  have hstable : (prefixWord ++ tailWord_283592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283592).length < 2 ^ (prefixWord ++ tailWord_283592).sum := by decide
  have hdescent : baseEnd_283592 < baseStart_283592 := by decide
  rcases family_descends (prefixWord ++ tailWord_283592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283601 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_283601 : Nat := 118140960795 + 283601 * 2 ^ 59
def prefixEnd_283601 : Nat := 4983230072969 + 3 ^ 40 * 283601 * 2
def baseEnd_283601 : Nat := 97082418063900095655499

theorem tailTrace_283601 : CollatzResearch.WordTrace tailWord_283601 prefixEnd_283601 97082418063900095655499 := by
  unfold tailWord_283601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343778245569487039786657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6895852163712991359857771 10343778245569487039786657)
  ·
    refine ⟨7757833684177115279839993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10343778245569487039786657 7757833684177115279839993)
    ·
      refine ⟨5818375263132836459879995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7757833684177115279839993 5818375263132836459879995)
      ·
        refine ⟨8727562894699254689819993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5818375263132836459879995 8727562894699254689819993)
        ·
          refine ⟨6545672171024441017364995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8727562894699254689819993 6545672171024441017364995)
          ·
            refine ⟨9818508256536661526047493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545672171024441017364995 9818508256536661526047493)
            ·
              refine ⟨1840970298100624036133905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9818508256536661526047493 1840970298100624036133905)
              ·
                refine ⟨1380727723575468027100429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840970298100624036133905 1380727723575468027100429)
                ·
                  refine ⟨517772896340800510162661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1380727723575468027100429 517772896340800510162661)
                  ·
                    refine ⟨97082418063900095655499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517772896340800510162661 97082418063900095655499)
                    ·
                      rfl

theorem cell22_283601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_283601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283601 prefixEnd_283601 := by exact prefixLift 283601
  have htrace : WordTrace (prefixWord ++ tailWord_283601) baseStart_283601 baseEnd_283601 := by
    simpa [prefixWord, tailWord_283601, baseEnd_283601] using wordTrace_append hprefix tailTrace_283601
  have hstable : (prefixWord ++ tailWord_283601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283601).length < 2 ^ (prefixWord ++ tailWord_283601).sum := by decide
  have hdescent : baseEnd_283601 < baseStart_283601 := by decide
  rcases family_descends (prefixWord ++ tailWord_283601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283631 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_283631 : Nat := 118140960795 + 283631 * 2 ^ 59
def prefixEnd_283631 : Nat := 4983230072969 + 3 ^ 40 * 283631 * 2
def baseEnd_283631 : Nat := 97092687676990017405407

theorem tailTrace_283631 : CollatzResearch.WordTrace tailWord_283631 prefixEnd_283631 97092687676990017405407 := by
  unfold tailWord_283631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344872435460802163378747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6896581623640534775585831 10344872435460802163378747)
  ·
    refine ⟨15517308653191203245068121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10344872435460802163378747 15517308653191203245068121)
    ·
      refine ⟨11637981489893402433801091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15517308653191203245068121 11637981489893402433801091)
      ·
        refine ⟨17456972234840103650701637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637981489893402433801091 17456972234840103650701637)
        ·
          refine ⟨3273182294032519434506557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17456972234840103650701637 3273182294032519434506557)
          ·
            refine ⟨1227443360262194787939959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3273182294032519434506557 1227443360262194787939959)
            ·
              refine ⟨1841165040393292181909939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227443360262194787939959 1841165040393292181909939)
              ·
                refine ⟨2761747560589938272864909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841165040393292181909939 2761747560589938272864909)
                ·
                  refine ⟨1035655335221226852324341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2761747560589938272864909 1035655335221226852324341)
                  ·
                    refine ⟨97092687676990017405407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1035655335221226852324341 97092687676990017405407)
                    ·
                      rfl

theorem cell22_283631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_283631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283631 prefixEnd_283631 := by exact prefixLift 283631
  have htrace : WordTrace (prefixWord ++ tailWord_283631) baseStart_283631 baseEnd_283631 := by
    simpa [prefixWord, tailWord_283631, baseEnd_283631] using wordTrace_append hprefix tailTrace_283631
  have hstable : (prefixWord ++ tailWord_283631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283631).length < 2 ^ (prefixWord ++ tailWord_283631).sum := by decide
  have hdescent : baseEnd_283631 < baseStart_283631 := by decide
  rcases family_descends (prefixWord ++ tailWord_283631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283680 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_283680 : Nat := 118140960795 + 283680 * 2 ^ 59
def prefixEnd_283680 : Nat := 4983230072969 + 3 ^ 40 * 283680 * 2
def baseEnd_283680 : Nat := 97109461378370222930257

theorem tailTrace_283680 : CollatzResearch.WordTrace tailWord_283680 prefixEnd_283680 97109461378370222930257 := by
  unfold tailWord_283680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173329806141641765956247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6897773074855522354608329 5173329806141641765956247)
  ·
    refine ⟨7759994709212462648934371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5173329806141641765956247 7759994709212462648934371)
    ·
      refine ⟨11639992063818693973401557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759994709212462648934371 11639992063818693973401557)
      ·
        refine ⟨272812313995750640001599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11639992063818693973401557 272812313995750640001599)
        ·
          refine ⟨409218470993625960002399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272812313995750640001599 409218470993625960002399)
          ·
            refine ⟨613827706490438940003599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409218470993625960002399 613827706490438940003599)
            ·
              refine ⟨920741559735658410005399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613827706490438940003599 920741559735658410005399)
              ·
                refine ⟨1381112339603487615008099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920741559735658410005399 1381112339603487615008099)
                ·
                  refine ⟨2071668509405231422512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381112339603487615008099 2071668509405231422512149)
                  ·
                    refine ⟨97109461378370222930257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2071668509405231422512149 97109461378370222930257)
                    ·
                      rfl

theorem cell22_283680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_283680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283680 prefixEnd_283680 := by exact prefixLift 283680
  have htrace : WordTrace (prefixWord ++ tailWord_283680) baseStart_283680 baseEnd_283680 := by
    simpa [prefixWord, tailWord_283680, baseEnd_283680] using wordTrace_append hprefix tailTrace_283680
  have hstable : (prefixWord ++ tailWord_283680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283680).length < 2 ^ (prefixWord ++ tailWord_283680).sum := by decide
  have hdescent : baseEnd_283680 < baseStart_283680 := by decide
  rcases family_descends (prefixWord ++ tailWord_283680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283721 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_283721 : Nat := 118140960795 + 283721 * 2 ^ 59
def prefixEnd_283721 : Nat := 4983230072969 + 3 ^ 40 * 283721 * 2
def baseEnd_283721 : Nat := 97123496516259782655131

theorem tailTrace_283721 : CollatzResearch.WordTrace tailWord_283721 prefixEnd_283721 97123496516259782655131 := by
  unfold tailWord_283721
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348155005134747534155017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6898770003423165022770011 10348155005134747534155017)
  ·
    refine ⟨7761116253851060650616263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10348155005134747534155017 7761116253851060650616263)
    ·
      refine ⟨11641674380776590975924395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761116253851060650616263 11641674380776590975924395)
      ·
        refine ⟨17462511571164886463886593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11641674380776590975924395 17462511571164886463886593)
        ·
          refine ⟨13096883678373664847914945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17462511571164886463886593 13096883678373664847914945)
          ·
            refine ⟨9822662758780248635936209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13096883678373664847914945 9822662758780248635936209)
            ·
              refine ⟨7366997069085186476952157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9822662758780248635936209 7366997069085186476952157)
              ·
                refine ⟨2762623900906944928857059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7366997069085186476952157 2762623900906944928857059)
                ·
                  refine ⟨4143935851360417393285589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762623900906944928857059 4143935851360417393285589)
                  ·
                    refine ⟨97123496516259782655131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4143935851360417393285589 97123496516259782655131)
                    ·
                      rfl

theorem cell22_283721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_283721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283721 prefixEnd_283721 := by exact prefixLift 283721
  have htrace : WordTrace (prefixWord ++ tailWord_283721) baseStart_283721 baseEnd_283721 := by
    simpa [prefixWord, tailWord_283721, baseEnd_283721] using wordTrace_append hprefix tailTrace_283721
  have hstable : (prefixWord ++ tailWord_283721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283721).length < 2 ^ (prefixWord ++ tailWord_283721).sum := by decide
  have hdescent : baseEnd_283721 < baseStart_283721 := by decide
  rcases family_descends (prefixWord ++ tailWord_283721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283768 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_283768 : Nat := 118140960795 + 283768 * 2 ^ 59
def prefixEnd_283768 : Nat := 4983230072969 + 3 ^ 40 * 283768 * 2
def baseEnd_283768 : Nat := 32379861858922442243329

theorem tailTrace_283768 : CollatzResearch.WordTrace tailWord_283768 prefixEnd_283768 32379861858922442243329 := by
  unfold tailWord_283768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174934617982237280557979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6899912823976316374077305 5174934617982237280557979)
  ·
    refine ⟨7762401926973355920836969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174934617982237280557979 7762401926973355920836969)
    ·
      refine ⟨5821801445230016940627727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7762401926973355920836969 5821801445230016940627727)
      ·
        refine ⟨8732702167845025410941591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821801445230016940627727 8732702167845025410941591)
        ·
          refine ⟨13099053251767538116412387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732702167845025410941591 13099053251767538116412387)
          ·
            refine ⟨19648579877651307174618581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13099053251767538116412387 19648579877651307174618581)
            ·
              refine ⟨460513590882452511905123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19648579877651307174618581 460513590882452511905123)
              ·
                refine ⟨690770386323678767857685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460513590882452511905123 690770386323678767857685)
                ·
                  refine ⟨32379861858922442243329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 690770386323678767857685 32379861858922442243329)
                  ·
                    rfl

theorem cell22_283768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_283768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283768 prefixEnd_283768 := by exact prefixLift 283768
  have htrace : WordTrace (prefixWord ++ tailWord_283768) baseStart_283768 baseEnd_283768 := by
    simpa [prefixWord, tailWord_283768, baseEnd_283768] using wordTrace_append hprefix tailTrace_283768
  have hstable : (prefixWord ++ tailWord_283768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283768).length < 2 ^ (prefixWord ++ tailWord_283768).sum := by decide
  have hdescent : baseEnd_283768 < baseStart_283768 := by decide
  rcases family_descends (prefixWord ++ tailWord_283768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283783 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_283783 : Nat := 118140960795 + 283783 * 2 ^ 59
def prefixEnd_283783 : Nat := 4983230072969 + 3 ^ 40 * 283783 * 2
def baseEnd_283783 : Nat := 97144720383312287604941

theorem tailTrace_283783 : CollatzResearch.WordTrace tailWord_283783 prefixEnd_283783 97144720383312287604941 := by
  unfold tailWord_283783
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350416330910132122912003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6900277553940088081941335 10350416330910132122912003)
  ·
    refine ⟨15525624496365198184368005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350416330910132122912003 15525624496365198184368005)
    ·
      refine ⟨2911054593068474659569001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15525624496365198184368005 2911054593068474659569001)
      ·
        refine ⟨2183290944801355994676751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2911054593068474659569001 2183290944801355994676751)
        ·
          refine ⟨3274936417202033992015127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183290944801355994676751 3274936417202033992015127)
          ·
            refine ⟨4912404625803050988022691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3274936417202033992015127 4912404625803050988022691)
            ·
              refine ⟨7368606938704576482034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912404625803050988022691 7368606938704576482034037)
              ·
                refine ⟨690806900503554045190691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7368606938704576482034037 690806900503554045190691)
                ·
                  refine ⟨1036210350755331067786037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690806900503554045190691 1036210350755331067786037)
                  ·
                    refine ⟨97144720383312287604941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1036210350755331067786037 97144720383312287604941)
                    ·
                      rfl

theorem cell22_283783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_283783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283783 prefixEnd_283783 := by exact prefixLift 283783
  have htrace : WordTrace (prefixWord ++ tailWord_283783) baseStart_283783 baseEnd_283783 := by
    simpa [prefixWord, tailWord_283783, baseEnd_283783] using wordTrace_append hprefix tailTrace_283783
  have hstable : (prefixWord ++ tailWord_283783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283783).length < 2 ^ (prefixWord ++ tailWord_283783).sum := by decide
  have hdescent : baseEnd_283783 < baseStart_283783 := by decide
  rcases family_descends (prefixWord ++ tailWord_283783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283800 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_283800 : Nat := 118140960795 + 283800 * 2 ^ 59
def prefixEnd_283800 : Nat := 4983230072969 + 3 ^ 40 * 283800 * 2
def baseEnd_283800 : Nat := 97150539830729909929889

theorem tailTrace_283800 : CollatzResearch.WordTrace tailWord_283800 prefixEnd_283800 97150539830729909929889 := by
  unfold tailWord_283800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175518185924272013140427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6900690914565696017520569 5175518185924272013140427)
  ·
    refine ⟨7763277278886408019710641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175518185924272013140427 7763277278886408019710641)
    ·
      refine ⟨5822457959164806014782981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7763277278886408019710641 5822457959164806014782981)
      ·
        refine ⟨1091710867343401127771809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5822457959164806014782981 1091710867343401127771809)
        ·
          refine ⟨818783150507550845828857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091710867343401127771809 818783150507550845828857)
          ·
            refine ⟨614087362880663134371643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818783150507550845828857 614087362880663134371643)
            ·
              refine ⟨921131044320994701557465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614087362880663134371643 921131044320994701557465)
              ·
                refine ⟨690848283240746026168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921131044320994701557465 690848283240746026168099)
                ·
                  refine ⟨1036272424861119039252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690848283240746026168099 1036272424861119039252149)
                  ·
                    refine ⟨97150539830729909929889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1036272424861119039252149 97150539830729909929889)
                    ·
                      rfl

theorem cell22_283800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_283800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283800 prefixEnd_283800 := by exact prefixLift 283800
  have htrace : WordTrace (prefixWord ++ tailWord_283800) baseStart_283800 baseEnd_283800 := by
    simpa [prefixWord, tailWord_283800, baseEnd_283800] using wordTrace_append hprefix tailTrace_283800
  have hstable : (prefixWord ++ tailWord_283800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283800).length < 2 ^ (prefixWord ++ tailWord_283800).sum := by decide
  have hdescent : baseEnd_283800 < baseStart_283800 := by decide
  rcases family_descends (prefixWord ++ tailWord_283800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283879 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 3, 3]
def baseStart_283879 : Nat := 118140960795 + 283879 * 2 ^ 59
def prefixEnd_283879 : Nat := 4983230072969 + 3 ^ 40 * 283879 * 2
def baseEnd_283879 : Nat := 97177583145200037204647

theorem tailTrace_283879 : CollatzResearch.WordTrace tailWord_283879 prefixEnd_283879 97177583145200037204647 := by
  unfold tailWord_283879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353917738562340518406691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6902611825708227012271127 10353917738562340518406691)
  ·
    refine ⟨15530876607843510777610037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10353917738562340518406691 15530876607843510777610037)
    ·
      refine ⟨1456019681985329135400941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15530876607843510777610037 1456019681985329135400941)
      ·
        refine ⟨546007380744498425775353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456019681985329135400941 546007380744498425775353)
        ·
          refine ⟨409505535558373819331515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546007380744498425775353 409505535558373819331515)
          ·
            refine ⟨614258303337560728997273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409505535558373819331515 614258303337560728997273)
            ·
              refine ⟨460693727503170546747955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614258303337560728997273 460693727503170546747955)
              ·
                refine ⟨691040591254755820121933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460693727503170546747955 691040591254755820121933)
                ·
                  refine ⟨259140221720533432545725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691040591254755820121933 259140221720533432545725)
                  ·
                    refine ⟨97177583145200037204647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259140221720533432545725 97177583145200037204647)
                    ·
                      rfl

theorem cell22_283879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_283879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283879 prefixEnd_283879 := by exact prefixLift 283879
  have htrace : WordTrace (prefixWord ++ tailWord_283879) baseStart_283879 baseEnd_283879 := by
    simpa [prefixWord, tailWord_283879, baseEnd_283879] using wordTrace_append hprefix tailTrace_283879
  have hstable : (prefixWord ++ tailWord_283879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283879).length < 2 ^ (prefixWord ++ tailWord_283879).sum := by decide
  have hdescent : baseEnd_283879 < baseStart_283879 := by decide
  rcases family_descends (prefixWord ++ tailWord_283879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283952 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_283952 : Nat := 118140960795 + 283952 * 2 ^ 59
def prefixEnd_283952 : Nat := 4983230072969 + 3 ^ 40 * 283952 * 2
def baseEnd_283952 : Nat := 97202572537052180129423

theorem tailTrace_283952 : CollatzResearch.WordTrace tailWord_283952 prefixEnd_283952 97202572537052180129423 := by
  unfold tailWord_283952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178290133648936992907055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6904386844865249323876073 5178290133648936992907055)
  ·
    refine ⟨7767435200473405489360583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178290133648936992907055 7767435200473405489360583)
    ·
      refine ⟨11651152800710108234040875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7767435200473405489360583 11651152800710108234040875)
      ·
        refine ⟨17476729201065162351061313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11651152800710108234040875 17476729201065162351061313)
        ·
          refine ⟨13107546900798871763295985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17476729201065162351061313 13107546900798871763295985)
          ·
            refine ⟨9830660175599153822471989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13107546900798871763295985 9830660175599153822471989)
            ·
              refine ⟨921624391462420670856749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9830660175599153822471989 921624391462420670856749)
              ·
                refine ⟨345609146798407751571281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 921624391462420670856749 345609146798407751571281)
                ·
                  refine ⟨259206860098805813678461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345609146798407751571281 259206860098805813678461)
                  ·
                    refine ⟨97202572537052180129423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259206860098805813678461 97202572537052180129423)
                    ·
                      rfl

theorem cell22_283952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_283952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283952 prefixEnd_283952 := by exact prefixLift 283952
  have htrace : WordTrace (prefixWord ++ tailWord_283952) baseStart_283952 baseEnd_283952 := by
    simpa [prefixWord, tailWord_283952, baseEnd_283952] using wordTrace_append hprefix tailTrace_283952
  have hstable : (prefixWord ++ tailWord_283952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283952).length < 2 ^ (prefixWord ++ tailWord_283952).sum := by decide
  have hdescent : baseEnd_283952 < baseStart_283952 := by decide
  rcases family_descends (prefixWord ++ tailWord_283952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283967 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_283967 : Nat := 118140960795 + 283967 * 2 ^ 59
def prefixEnd_283967 : Nat := 4983230072969 + 3 ^ 40 * 283967 * 2
def baseEnd_283967 : Nat := 97207707343597141004377

theorem tailTrace_283967 : CollatzResearch.WordTrace tailWord_283967 prefixEnd_283967 97207707343597141004377 := by
  unfold tailWord_283967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357127362243531547610155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6904751574829021031740103 10357127362243531547610155)
  ·
    refine ⟨15535691043365297321415233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10357127362243531547610155 15535691043365297321415233)
    ·
      refine ⟨11651768282523972991061425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15535691043365297321415233 11651768282523972991061425)
      ·
        refine ⟨8738826211892979743296069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11651768282523972991061425 8738826211892979743296069)
        ·
          refine ⟨1638529914729933701868013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8738826211892979743296069 1638529914729933701868013)
          ·
            refine ⟨614448718023725138200505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1638529914729933701868013 614448718023725138200505)
            ·
              refine ⟨460836538517793853650379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614448718023725138200505 460836538517793853650379)
              ·
                refine ⟨691254807776690780475569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460836538517793853650379 691254807776690780475569)
                ·
                  refine ⟨518441105832518085356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691254807776690780475569 518441105832518085356677)
                  ·
                    refine ⟨97207707343597141004377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 518441105832518085356677 97207707343597141004377)
                    ·
                      rfl

theorem cell22_283967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_283967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_283967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_283967 prefixEnd_283967 := by exact prefixLift 283967
  have htrace : WordTrace (prefixWord ++ tailWord_283967) baseStart_283967 baseEnd_283967 := by
    simpa [prefixWord, tailWord_283967, baseEnd_283967] using wordTrace_append hprefix tailTrace_283967
  have hstable : (prefixWord ++ tailWord_283967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283967).length < 2 ^ (prefixWord ++ tailWord_283967).sum := by decide
  have hdescent : baseEnd_283967 < baseStart_283967 := by decide
  rcases family_descends (prefixWord ++ tailWord_283967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284087 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 6, 3]
def baseStart_284087 : Nat := 118140960795 + 284087 * 2 ^ 59
def prefixEnd_284087 : Nat := 4983230072969 + 3 ^ 40 * 284087 * 2
def baseEnd_284087 : Nat := 97248785795956828004009

theorem tailTrace_284087 : CollatzResearch.WordTrace tailWord_284087 prefixEnd_284087 97248785795956828004009 := by
  unfold tailWord_284087
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361504121808792041978515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6907669414539194694652343 10361504121808792041978515)
  ·
    refine ⟨15542256182713188062967773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361504121808792041978515 15542256182713188062967773)
    ·
      refine ⟨5828346068517445523612915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15542256182713188062967773 5828346068517445523612915)
      ·
        refine ⟨8742519102776168285419373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828346068517445523612915 8742519102776168285419373)
        ·
          refine ⟨3278444663541063107032265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8742519102776168285419373 3278444663541063107032265)
          ·
            refine ⟨2458833497655797330274199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3278444663541063107032265 2458833497655797330274199)
            ·
              refine ⟨3688250246483695995411299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458833497655797330274199 3688250246483695995411299)
              ·
                refine ⟨5532375369725543993116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688250246483695995411299 5532375369725543993116949)
                ·
                  refine ⟨259330095455884874677357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5532375369725543993116949 259330095455884874677357)
                  ·
                    refine ⟨97248785795956828004009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259330095455884874677357 97248785795956828004009)
                    ·
                      rfl

theorem cell22_284087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_284087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284087 prefixEnd_284087 := by exact prefixLift 284087
  have htrace : WordTrace (prefixWord ++ tailWord_284087) baseStart_284087 baseEnd_284087 := by
    simpa [prefixWord, tailWord_284087, baseEnd_284087] using wordTrace_append hprefix tailTrace_284087
  have hstable : (prefixWord ++ tailWord_284087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284087).length < 2 ^ (prefixWord ++ tailWord_284087).sum := by decide
  have hdescent : baseEnd_284087 < baseStart_284087 := by decide
  rcases family_descends (prefixWord ++ tailWord_284087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284104 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_284104 : Nat := 118140960795 + 284104 * 2 ^ 59
def prefixEnd_284104 : Nat := 4983230072969 + 3 ^ 40 * 284104 * 2
def baseEnd_284104 : Nat := 97254605243374450328957

theorem tailTrace_284104 : CollatzResearch.WordTrace tailWord_284104 prefixEnd_284104 97254605243374450328957 := by
  unfold tailWord_284104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181062081373601972673683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6908082775164802630231577 5181062081373601972673683)
  ·
    refine ⟨7771593122060402959010525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5181062081373601972673683 7771593122060402959010525)
    ·
      refine ⟨2914347420772651109628947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7771593122060402959010525 2914347420772651109628947)
      ·
        refine ⟨4371521131158976664443421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914347420772651109628947 4371521131158976664443421)
        ·
          refine ⟨1639320424184616249166283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371521131158976664443421 1639320424184616249166283)
          ·
            refine ⟨2458980636276924373749425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639320424184616249166283 2458980636276924373749425)
            ·
              refine ⟨1844235477207693280312069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458980636276924373749425 1844235477207693280312069)
              ·
                refine ⟨345794151976442490058513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1844235477207693280312069 345794151976442490058513)
                ·
                  refine ⟨259345613982331867543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345794151976442490058513 259345613982331867543885)
                  ·
                    refine ⟨97254605243374450328957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259345613982331867543885 97254605243374450328957)
                    ·
                      rfl

theorem cell22_284104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_284104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284104 prefixEnd_284104 := by exact prefixLift 284104
  have htrace : WordTrace (prefixWord ++ tailWord_284104) baseStart_284104 baseEnd_284104 := by
    simpa [prefixWord, tailWord_284104, baseEnd_284104] using wordTrace_append hprefix tailTrace_284104
  have hstable : (prefixWord ++ tailWord_284104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284104).length < 2 ^ (prefixWord ++ tailWord_284104).sum := by decide
  have hdescent : baseEnd_284104 < baseStart_284104 := by decide
  rcases family_descends (prefixWord ++ tailWord_284104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284106 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_284106 : Nat := 118140960795 + 284106 * 2 ^ 59
def prefixEnd_284106 : Nat := 4983230072969 + 3 ^ 40 * 284106 * 2
def baseEnd_284106 : Nat := 32418429961415703926317

theorem tailTrace_284106 : CollatzResearch.WordTrace tailWord_284106 prefixEnd_284106 32418429961415703926317 := by
  unfold tailWord_284106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590549277184989571730043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6908131405826638857946781 2590549277184989571730043)
  ·
    refine ⟨3885823915777484357595065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590549277184989571730043 3885823915777484357595065)
    ·
      refine ⟨2914367936833113268196299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3885823915777484357595065 2914367936833113268196299)
      ·
        refine ⟨4371551905249669902294449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914367936833113268196299 4371551905249669902294449)
        ·
          refine ⟨3278663928937252426720837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4371551905249669902294449 3278663928937252426720837)
          ·
            refine ⟨614749486675734830010157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3278663928937252426720837 614749486675734830010157)
            ·
              refine ⟨230531057503400561253809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614749486675734830010157 230531057503400561253809)
              ·
                refine ⟨172898293127550420940357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230531057503400561253809 172898293127550420940357)
                ·
                  refine ⟨32418429961415703926317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172898293127550420940357 32418429961415703926317)
                  ·
                    rfl

theorem cell22_284106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_284106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284106 prefixEnd_284106 := by exact prefixLift 284106
  have htrace : WordTrace (prefixWord ++ tailWord_284106) baseStart_284106 baseEnd_284106 := by
    simpa [prefixWord, tailWord_284106, baseEnd_284106] using wordTrace_append hprefix tailTrace_284106
  have hstable : (prefixWord ++ tailWord_284106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284106).length < 2 ^ (prefixWord ++ tailWord_284106).sum := by decide
  have hdescent : baseEnd_284106 < baseStart_284106 := by decide
  rcases family_descends (prefixWord ++ tailWord_284106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284117 : List Nat := [1, 3, 2, 3, 1, 1, 4, 7]
def baseStart_284117 : Nat := 118140960795 + 284117 * 2 ^ 59
def prefixEnd_284117 : Nat := 4983230072969 + 3 ^ 40 * 284117 * 2
def baseEnd_284117 : Nat := 10806561712116305528213

theorem tailTrace_284117 : CollatzResearch.WordTrace tailWord_284117 prefixEnd_284117 10806561712116305528213 := by
  unfold tailWord_284117
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362598311700107165570605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6908398874466738110380403 10362598311700107165570605)
  ·
    refine ⟨3885974366887540187088977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10362598311700107165570605 3885974366887540187088977)
    ·
      refine ⟨2914480775165655140316733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3885974366887540187088977 2914480775165655140316733)
      ·
        refine ⟨1092930290687120677618775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2914480775165655140316733 1092930290687120677618775)
        ·
          refine ⟨1639395436030681016428163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092930290687120677618775 1639395436030681016428163)
          ·
            refine ⟨2459093154046021524642245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639395436030681016428163 2459093154046021524642245)
            ·
              refine ⟨461079966383629035870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2459093154046021524642245 461079966383629035870421)
              ·
                refine ⟨10806561712116305528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 461079966383629035870421 10806561712116305528213)
                ·
                  rfl

theorem cell22_284117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 7].length) (baseStart_284117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284117 prefixEnd_284117 := by exact prefixLift 284117
  have htrace : WordTrace (prefixWord ++ tailWord_284117) baseStart_284117 baseEnd_284117 := by
    simpa [prefixWord, tailWord_284117, baseEnd_284117] using wordTrace_append hprefix tailTrace_284117
  have hstable : (prefixWord ++ tailWord_284117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284117).length < 2 ^ (prefixWord ++ tailWord_284117).sum := by decide
  have hdescent : baseEnd_284117 < baseStart_284117 := by decide
  rcases family_descends (prefixWord ++ tailWord_284117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284121 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_284121 : Nat := 118140960795 + 284121 * 2 ^ 59
def prefixEnd_284121 : Nat := 4983230072969 + 3 ^ 40 * 284121 * 2
def baseEnd_284121 : Nat := 97260424690792072653905

theorem tailTrace_284121 : CollatzResearch.WordTrace tailWord_284121 prefixEnd_284121 97260424690792072653905 := by
  unfold tailWord_284121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362744203685615848716217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6908496135790410565810811 10362744203685615848716217)
  ·
    refine ⟨7772058152764211886537163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10362744203685615848716217 7772058152764211886537163)
    ·
      refine ⟨11658087229146317829805745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7772058152764211886537163 11658087229146317829805745)
      ·
        refine ⟨8743565421859738372354309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11658087229146317829805745 8743565421859738372354309)
        ·
          refine ⟨1639418516598700944816433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8743565421859738372354309 1639418516598700944816433)
          ·
            refine ⟨1229563887449025708612325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639418516598700944816433 1229563887449025708612325)
            ·
              refine ⟨230543228896692320364811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1229563887449025708612325 230543228896692320364811)
              ·
                refine ⟨345814843345038480547217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230543228896692320364811 345814843345038480547217)
                ·
                  refine ⟨259361132508778860410413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345814843345038480547217 259361132508778860410413)
                  ·
                    refine ⟨97260424690792072653905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259361132508778860410413 97260424690792072653905)
                    ·
                      rfl

theorem cell22_284121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_284121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284121 prefixEnd_284121 := by exact prefixLift 284121
  have htrace : WordTrace (prefixWord ++ tailWord_284121) baseStart_284121 baseEnd_284121 := by
    simpa [prefixWord, tailWord_284121, baseEnd_284121] using wordTrace_append hprefix tailTrace_284121
  have hstable : (prefixWord ++ tailWord_284121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284121).length < 2 ^ (prefixWord ++ tailWord_284121).sum := by decide
  have hdescent : baseEnd_284121 < baseStart_284121 := by decide
  rcases family_descends (prefixWord ++ tailWord_284121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284177 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_284177 : Nat := 118140960795 + 284177 * 2 ^ 59
def prefixEnd_284177 : Nat := 4983230072969 + 3 ^ 40 * 284177 * 2
def baseEnd_284177 : Nat := 97279594635226593253733

theorem tailTrace_284177 : CollatzResearch.WordTrace tailWord_284177 prefixEnd_284177 97279594635226593253733 := by
  unfold tailWord_284177
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364786691482737412754785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6909857794321824941836523 10364786691482737412754785)
  ·
    refine ⟨7773590018612053059566089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10364786691482737412754785 7773590018612053059566089)
    ·
      refine ⟨5830192513959039794674567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7773590018612053059566089 5830192513959039794674567)
      ·
        refine ⟨8745288770938559692011851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830192513959039794674567 8745288770938559692011851)
        ·
          refine ⟨13117933156407839538017777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745288770938559692011851 13117933156407839538017777)
          ·
            refine ⟨9838449867305879653513333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13117933156407839538017777 9838449867305879653513333)
            ·
              refine ⟨922354675059926217516875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9838449867305879653513333 922354675059926217516875)
              ·
                refine ⟨1383532012589889326275313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922354675059926217516875 1383532012589889326275313)
                ·
                  refine ⟨1037649009442416994706485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383532012589889326275313 1037649009442416994706485)
                  ·
                    refine ⟨97279594635226593253733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1037649009442416994706485 97279594635226593253733)
                    ·
                      rfl

theorem cell22_284177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_284177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284177 prefixEnd_284177 := by exact prefixLift 284177
  have htrace : WordTrace (prefixWord ++ tailWord_284177) baseStart_284177 baseEnd_284177 := by
    simpa [prefixWord, tailWord_284177, baseEnd_284177] using wordTrace_append hprefix tailTrace_284177
  have hstable : (prefixWord ++ tailWord_284177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284177).length < 2 ^ (prefixWord ++ tailWord_284177).sum := by decide
  have hdescent : baseEnd_284177 < baseStart_284177 := by decide
  rcases family_descends (prefixWord ++ tailWord_284177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284200 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_284200 : Nat := 118140960795 + 284200 * 2 ^ 59
def prefixEnd_284200 : Nat := 4983230072969 + 3 ^ 40 * 284200 * 2
def baseEnd_284200 : Nat := 97287468005262199928663

theorem tailTrace_284200 : CollatzResearch.WordTrace tailWord_284200 prefixEnd_284200 97287468005262199928663 := by
  unfold tailWord_284200
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182812785199706170421027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6910417046932941560561369 5182812785199706170421027)
  ·
    refine ⟨7774219177799559255631541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5182812785199706170421027 7774219177799559255631541)
    ·
      refine ⟨728833047918708680215457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7774219177799559255631541 728833047918708680215457)
      ·
        refine ⟨546624785939031510161593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728833047918708680215457 546624785939031510161593)
        ·
          refine ⟨409968589454273632621195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546624785939031510161593 409968589454273632621195)
          ·
            refine ⟨614952884181410448931793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409968589454273632621195 614952884181410448931793)
            ·
              refine ⟨461214663136057836698845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614952884181410448931793 461214663136057836698845)
              ·
                refine ⟨172955498676021688762067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461214663136057836698845 172955498676021688762067)
                ·
                  refine ⟨259433248014032533143101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172955498676021688762067 259433248014032533143101)
                  ·
                    refine ⟨97287468005262199928663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259433248014032533143101 97287468005262199928663)
                    ·
                      rfl

theorem cell22_284200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_284200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284200 prefixEnd_284200 := by exact prefixLift 284200
  have htrace : WordTrace (prefixWord ++ tailWord_284200) baseStart_284200 baseEnd_284200 := by
    simpa [prefixWord, tailWord_284200, baseEnd_284200] using wordTrace_append hprefix tailTrace_284200
  have hstable : (prefixWord ++ tailWord_284200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284200).length < 2 ^ (prefixWord ++ tailWord_284200).sum := by decide
  have hdescent : baseEnd_284200 < baseStart_284200 := by decide
  rcases family_descends (prefixWord ++ tailWord_284200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284230 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_284230 : Nat := 118140960795 + 284230 * 2 ^ 59
def prefixEnd_284230 : Nat := 4983230072969 + 3 ^ 40 * 284230 * 2
def baseEnd_284230 : Nat := 32432579206117373892857

theorem tailTrace_284230 : CollatzResearch.WordTrace tailWord_284230 prefixEnd_284230 32432579206117373892857 := by
  unfold tailWord_284230
  simp only [CollatzResearch.WordTrace]
  refine ⟨323959992509085233263567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6911146506860484976289429 323959992509085233263567)
  ·
    refine ⟨485939988763627849895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 323959992509085233263567 485939988763627849895351)
    ·
      refine ⟨728909983145441774843027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485939988763627849895351 728909983145441774843027)
      ·
        refine ⟨1093364974718162662264541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728909983145441774843027 1093364974718162662264541)
        ·
          refine ⟨410011865519310998349203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1093364974718162662264541 410011865519310998349203)
          ·
            refine ⟨615017798278966497523805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410011865519310998349203 615017798278966497523805)
            ·
              refine ⟨230631674354612436571427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 615017798278966497523805 230631674354612436571427)
              ·
                refine ⟨345947511531918654857141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230631674354612436571427 345947511531918654857141)
                ·
                  refine ⟨32432579206117373892857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345947511531918654857141 32432579206117373892857)
                  ·
                    rfl

theorem cell22_284230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_284230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284230 prefixEnd_284230 := by exact prefixLift 284230
  have htrace : WordTrace (prefixWord ++ tailWord_284230) baseStart_284230 baseEnd_284230 := by
    simpa [prefixWord, tailWord_284230, baseEnd_284230] using wordTrace_append hprefix tailTrace_284230
  have hstable : (prefixWord ++ tailWord_284230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284230).length < 2 ^ (prefixWord ++ tailWord_284230).sum := by decide
  have hdescent : baseEnd_284230 < baseStart_284230 := by decide
  rcases family_descends (prefixWord ++ tailWord_284230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284359 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 6]
def baseStart_284359 : Nat := 118140960795 + 284359 * 2 ^ 59
def prefixEnd_284359 : Nat := 4983230072969 + 3 ^ 40 * 284359 * 2
def baseEnd_284359 : Nat := 32447298984879595067725

theorem tailTrace_284359 : CollatzResearch.WordTrace tailWord_284359 prefixEnd_284359 32447298984879595067725 := by
  unfold tailWord_284359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371424776823382495880131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6914283184548921663920087 10371424776823382495880131)
  ·
    refine ⟨15557137165235073743820197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10371424776823382495880131 15557137165235073743820197)
    ·
      refine ⟨2916963218481576326966287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15557137165235073743820197 2916963218481576326966287)
      ·
        refine ⟨4375444827722364490449431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916963218481576326966287 4375444827722364490449431)
        ·
          refine ⟨6563167241583546735674147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375444827722364490449431 6563167241583546735674147)
          ·
            refine ⟨9844750862375320103511221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6563167241583546735674147 9844750862375320103511221)
            ·
              refine ⟨922945393347686259704177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9844750862375320103511221 922945393347686259704177)
              ·
                refine ⟨692209045010764694778133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922945393347686259704177 692209045010764694778133)
                ·
                  refine ⟨32447298984879595067725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 692209045010764694778133 32447298984879595067725)
                  ·
                    rfl

theorem cell22_284359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_284359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284359 prefixEnd_284359 := by exact prefixLift 284359
  have htrace : WordTrace (prefixWord ++ tailWord_284359) baseStart_284359 baseEnd_284359 := by
    simpa [prefixWord, tailWord_284359, baseEnd_284359] using wordTrace_append hprefix tailTrace_284359
  have hstable : (prefixWord ++ tailWord_284359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284359).length < 2 ^ (prefixWord ++ tailWord_284359).sum := by decide
  have hdescent : baseEnd_284359 < baseStart_284359 := by decide
  rcases family_descends (prefixWord ++ tailWord_284359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284378 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_284378 : Nat := 118140960795 + 284378 * 2 ^ 59
def prefixEnd_284378 : Nat := 4983230072969 + 3 ^ 40 * 284378 * 2
def baseEnd_284378 : Nat := 97348401042929068978117

theorem tailTrace_284378 : CollatzResearch.WordTrace tailWord_284378 prefixEnd_284378 97348401042929068978117 := by
  unfold tailWord_284378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593029440938637185205447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6914745175836365827214525 2593029440938637185205447)
  ·
    refine ⟨3889544161407955777808171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593029440938637185205447 3889544161407955777808171)
    ·
      refine ⟨5834316242111933666712257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889544161407955777808171 5834316242111933666712257)
      ·
        refine ⟨4375737181583950250034193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834316242111933666712257 4375737181583950250034193)
        ·
          refine ⟨3281802886187962687525645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4375737181583950250034193 3281802886187962687525645)
          ·
            refine ⟨1230676082320486007822117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3281802886187962687525645 1230676082320486007822117)
            ·
              refine ⟨230751765435091126466647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1230676082320486007822117 230751765435091126466647)
              ·
                refine ⟨346127648152636689699971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230751765435091126466647 346127648152636689699971)
                ·
                  refine ⟨519191472228955034549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346127648152636689699971 519191472228955034549957)
                  ·
                    refine ⟨97348401042929068978117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 519191472228955034549957 97348401042929068978117)
                    ·
                      rfl

theorem cell22_284378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_284378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284378 prefixEnd_284378 := by exact prefixLift 284378
  have htrace : WordTrace (prefixWord ++ tailWord_284378) baseStart_284378 baseEnd_284378 := by
    simpa [prefixWord, tailWord_284378, baseEnd_284378] using wordTrace_append hprefix tailTrace_284378
  have hstable : (prefixWord ++ tailWord_284378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284378).length < 2 ^ (prefixWord ++ tailWord_284378).sum := by decide
  have hdescent : baseEnd_284378 < baseStart_284378 := by decide
  rcases family_descends (prefixWord ++ tailWord_284378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284406 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_284406 : Nat := 118140960795 + 284406 * 2 ^ 59
def prefixEnd_284406 : Nat := 4983230072969 + 3 ^ 40 * 284406 * 2
def baseEnd_284406 : Nat := 97357986015146329278031

theorem tailTrace_284406 : CollatzResearch.WordTrace tailWord_284406 prefixEnd_284406 97357986015146329278031 := by
  unfold tailWord_284406
  simp only [CollatzResearch.WordTrace]
  refine ⟨648321187978319345177567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6915426005102073015227381 648321187978319345177567)
  ·
    refine ⟨972481781967479017766351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 648321187978319345177567 972481781967479017766351)
    ·
      refine ⟨1458722672951218526649527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972481781967479017766351 1458722672951218526649527)
      ·
        refine ⟨2188084009426827789974291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458722672951218526649527 2188084009426827789974291)
        ·
          refine ⟨3282126014140241684961437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188084009426827789974291 3282126014140241684961437)
          ·
            refine ⟨1230797255302590631860539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3282126014140241684961437 1230797255302590631860539)
            ·
              refine ⟨1846195882953885947790809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230797255302590631860539 1846195882953885947790809)
              ·
                refine ⟨1384646912215414460843107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846195882953885947790809 1384646912215414460843107)
                ·
                  refine ⟨2076970368323121691264661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384646912215414460843107 2076970368323121691264661)
                  ·
                    refine ⟨97357986015146329278031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2076970368323121691264661 97357986015146329278031)
                    ·
                      rfl

theorem cell22_284406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_284406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284406 prefixEnd_284406 := by exact prefixLift 284406
  have htrace : WordTrace (prefixWord ++ tailWord_284406) baseStart_284406 baseEnd_284406 := by
    simpa [prefixWord, tailWord_284406, baseEnd_284406] using wordTrace_append hprefix tailTrace_284406
  have hstable : (prefixWord ++ tailWord_284406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284406).length < 2 ^ (prefixWord ++ tailWord_284406).sum := by decide
  have hdescent : baseEnd_284406 < baseStart_284406 := by decide
  rcases family_descends (prefixWord ++ tailWord_284406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284453 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_284453 : Nat := 118140960795 + 284453 * 2 ^ 59
def prefixEnd_284453 : Nat := 4983230072969 + 3 ^ 40 * 284453 * 2
def baseEnd_284453 : Nat := 97374075075653873352887

theorem tailTrace_284453 : CollatzResearch.WordTrace tailWord_284453 prefixEnd_284453 97374075075653873352887 := by
  unfold tailWord_284453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374853238482836549802013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6916568825655224366534675 10374853238482836549802013)
  ·
    refine ⟨3890569964431063706175755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10374853238482836549802013 3890569964431063706175755)
    ·
      refine ⟨5835854946646595559263633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890569964431063706175755 5835854946646595559263633)
      ·
        refine ⟨4376891209984946669447725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5835854946646595559263633 4376891209984946669447725)
        ·
          refine ⟨1641334203744355001042897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4376891209984946669447725 1641334203744355001042897)
          ·
            refine ⟨1231000652808266250782173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641334203744355001042897 1231000652808266250782173)
            ·
              refine ⟨461625244803099844043315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1231000652808266250782173 461625244803099844043315)
              ·
                refine ⟨692437867204649766064973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461625244803099844043315 692437867204649766064973)
                ·
                  refine ⟨259664200201743662274365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692437867204649766064973 259664200201743662274365)
                  ·
                    refine ⟨97374075075653873352887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259664200201743662274365 97374075075653873352887)
                    ·
                      rfl

theorem cell22_284453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_284453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284453 prefixEnd_284453 := by exact prefixLift 284453
  have htrace : WordTrace (prefixWord ++ tailWord_284453) baseStart_284453 baseEnd_284453 := by
    simpa [prefixWord, tailWord_284453, baseEnd_284453] using wordTrace_append hprefix tailTrace_284453
  have hstable : (prefixWord ++ tailWord_284453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284453).length < 2 ^ (prefixWord ++ tailWord_284453).sum := by decide
  have hdescent : baseEnd_284453 < baseStart_284453 := by decide
  rcases family_descends (prefixWord ++ tailWord_284453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284577 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_284577 : Nat := 118140960795 + 284577 * 2 ^ 59
def prefixEnd_284577 : Nat := 4983230072969 + 3 ^ 40 * 284577 * 2
def baseEnd_284577 : Nat := 97416522809758883252507

theorem tailTrace_284577 : CollatzResearch.WordTrace tailWord_284577 prefixEnd_284577 97416522809758883252507 := by
  unfold tailWord_284577
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379375890033605727315985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6919583926689070484877323 10379375890033605727315985)
  ·
    refine ⟨7784531917525204295486989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10379375890033605727315985 7784531917525204295486989)
    ·
      refine ⟨2919199469071951610807621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7784531917525204295486989 2919199469071951610807621)
      ·
        refine ⟨547349900450990927026429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2919199469071951610807621 547349900450990927026429)
        ·
          refine ⟨205256212669121597634911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 547349900450990927026429 205256212669121597634911)
          ·
            refine ⟨307884319003682396452367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205256212669121597634911 307884319003682396452367)
            ·
              refine ⟨461826478505523594678551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307884319003682396452367 461826478505523594678551)
              ·
                refine ⟨692739717758285392017827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461826478505523594678551 692739717758285392017827)
                ·
                  refine ⟨1039109576637428088026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692739717758285392017827 1039109576637428088026741)
                  ·
                    refine ⟨97416522809758883252507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1039109576637428088026741 97416522809758883252507)
                    ·
                      rfl

theorem cell22_284577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_284577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284577 prefixEnd_284577 := by exact prefixLift 284577
  have htrace : WordTrace (prefixWord ++ tailWord_284577) baseStart_284577 baseEnd_284577 := by
    simpa [prefixWord, tailWord_284577, baseEnd_284577] using wordTrace_append hprefix tailTrace_284577
  have hstable : (prefixWord ++ tailWord_284577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284577).length < 2 ^ (prefixWord ++ tailWord_284577).sum := by decide
  have hdescent : baseEnd_284577 < baseStart_284577 := by decide
  rcases family_descends (prefixWord ++ tailWord_284577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284596 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_284596 : Nat := 118140960795 + 284596 * 2 ^ 59
def prefixEnd_284596 : Nat := 4983230072969 + 3 ^ 40 * 284596 * 2
def baseEnd_284596 : Nat := 32474342299349722342483

theorem tailTrace_284596 : CollatzResearch.WordTrace tailWord_284596 prefixEnd_284596 32474342299349722342483 := by
  unfold tailWord_284596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190034438482385986128821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6920045917976514648171761 5190034438482385986128821)
  ·
    refine ⟨486565728607723686199577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5190034438482385986128821 486565728607723686199577)
    ·
      refine ⟨364924296455792764649683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486565728607723686199577 364924296455792764649683)
      ·
        refine ⟨547386444683689146974525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364924296455792764649683 547386444683689146974525)
        ·
          refine ⟨205269916756383430115447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 547386444683689146974525 205269916756383430115447)
          ·
            refine ⟨307904875134575145173171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205269916756383430115447 307904875134575145173171)
            ·
              refine ⟨461857312701862717759757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307904875134575145173171 461857312701862717759757)
              ·
                refine ⟨173196492263198519159909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461857312701862717759757 173196492263198519159909)
                ·
                  refine ⟨32474342299349722342483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173196492263198519159909 32474342299349722342483)
                  ·
                    rfl

theorem cell22_284596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_284596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284596 prefixEnd_284596 := by exact prefixLift 284596
  have htrace : WordTrace (prefixWord ++ tailWord_284596) baseStart_284596 baseEnd_284596 := by
    simpa [prefixWord, tailWord_284596, baseEnd_284596] using wordTrace_append hprefix tailTrace_284596
  have hstable : (prefixWord ++ tailWord_284596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284596).length < 2 ^ (prefixWord ++ tailWord_284596).sum := by decide
  have hdescent : baseEnd_284596 < baseStart_284596 := by decide
  rcases family_descends (prefixWord ++ tailWord_284596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284601 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 9]
def baseStart_284601 : Nat := 118140960795 + 284601 * 2 ^ 59
def prefixEnd_284601 : Nat := 4983230072969 + 3 ^ 40 * 284601 * 2
def baseEnd_284601 : Nat := 32474912833410273550811

theorem tailTrace_284601 : CollatzResearch.WordTrace tailWord_284601 prefixEnd_284601 32474912833410273550811 := by
  unfold tailWord_284601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380251241946657826189657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6920167494631105217459771 10380251241946657826189657)
  ·
    refine ⟨7785188431459993369642243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10380251241946657826189657 7785188431459993369642243)
    ·
      refine ⟨11677782647189990054463365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7785188431459993369642243 11677782647189990054463365)
      ·
        refine ⟨2189584246348123135211881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11677782647189990054463365 2189584246348123135211881)
        ·
          refine ⟨1642188184761092351408911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2189584246348123135211881 1642188184761092351408911)
          ·
            refine ⟨2463282277141638527113367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642188184761092351408911 2463282277141638527113367)
            ·
              refine ⟨3694923415712457790670051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463282277141638527113367 3694923415712457790670051)
              ·
                refine ⟨5542385123568686686005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694923415712457790670051 5542385123568686686005077)
                ·
                  refine ⟨32474912833410273550811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5542385123568686686005077 32474912833410273550811)
                  ·
                    rfl

theorem cell22_284601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_284601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284601 prefixEnd_284601 := by exact prefixLift 284601
  have htrace : WordTrace (prefixWord ++ tailWord_284601) baseStart_284601 baseEnd_284601 := by
    simpa [prefixWord, tailWord_284601, baseEnd_284601] using wordTrace_append hprefix tailTrace_284601
  have hstable : (prefixWord ++ tailWord_284601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284601).length < 2 ^ (prefixWord ++ tailWord_284601).sum := by decide
  have hdescent : baseEnd_284601 < baseStart_284601 := by decide
  rcases family_descends (prefixWord ++ tailWord_284601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284680 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_284680 : Nat := 118140960795 + 284680 * 2 ^ 59
def prefixEnd_284680 : Nat := 4983230072969 + 3 ^ 40 * 284680 * 2
def baseEnd_284680 : Nat := 32483927271566982642397

theorem tailTrace_284680 : CollatzResearch.WordTrace tailWord_284680 prefixEnd_284680 32483927271566982642397 := by
  unfold tailWord_284680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191566304330227159157747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6922088405773636212210329 5191566304330227159157747)
  ·
    refine ⟨7787349456495340738736621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5191566304330227159157747 7787349456495340738736621)
    ·
      refine ⟨2920256046185752777026233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7787349456495340738736621 2920256046185752777026233)
      ·
        refine ⟨2190192034639314582769675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920256046185752777026233 2190192034639314582769675)
        ·
          refine ⟨3285288051958971874154513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190192034639314582769675 3285288051958971874154513)
          ·
            refine ⟨2463966038969228905615885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285288051958971874154513 2463966038969228905615885)
            ·
              refine ⟨923987264613460839605957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2463966038969228905615885 923987264613460839605957)
              ·
                refine ⟨173247612115023907426117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 923987264613460839605957 173247612115023907426117)
                ·
                  refine ⟨32483927271566982642397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173247612115023907426117 32483927271566982642397)
                  ·
                    rfl

theorem cell22_284680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_284680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284680 prefixEnd_284680 := by exact prefixLift 284680
  have htrace : WordTrace (prefixWord ++ tailWord_284680) baseStart_284680 baseEnd_284680 := by
    simpa [prefixWord, tailWord_284680, baseEnd_284680] using wordTrace_append hprefix tailTrace_284680
  have hstable : (prefixWord ++ tailWord_284680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284680).length < 2 ^ (prefixWord ++ tailWord_284680).sum := by decide
  have hdescent : baseEnd_284680 < baseStart_284680 := by decide
  rcases family_descends (prefixWord ++ tailWord_284680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284729 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_284729 : Nat := 118140960795 + 284729 * 2 ^ 59
def prefixEnd_284729 : Nat := 4983230072969 + 3 ^ 40 * 284729 * 2
def baseEnd_284729 : Nat := 97468555516081153452041

theorem tailTrace_284729 : CollatzResearch.WordTrace tailWord_284729 prefixEnd_284729 97468555516081153452041 := by
  unfold tailWord_284729
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384919785482935686849241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6923279856988623791232827 10384919785482935686849241)
  ·
    refine ⟨7788689839112201765136931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10384919785482935686849241 7788689839112201765136931)
    ·
      refine ⟨11683034758668302647705397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788689839112201765136931 11683034758668302647705397)
      ·
        refine ⟨1095284508625153373222381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11683034758668302647705397 1095284508625153373222381)
        ·
          refine ⟨410731690734432514958393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1095284508625153373222381 410731690734432514958393)
          ·
            refine ⟨308048768050824386218795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410731690734432514958393 308048768050824386218795)
            ·
              refine ⟨462073152076236579328193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308048768050824386218795 462073152076236579328193)
              ·
                refine ⟨346554864057177434496145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462073152076236579328193 346554864057177434496145)
                ·
                  refine ⟨259916148042883075872109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346554864057177434496145 259916148042883075872109)
                  ·
                    refine ⟨97468555516081153452041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259916148042883075872109 97468555516081153452041)
                    ·
                      rfl

theorem cell22_284729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_284729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284729 prefixEnd_284729 := by exact prefixLift 284729
  have htrace : WordTrace (prefixWord ++ tailWord_284729) baseStart_284729 baseEnd_284729 := by
    simpa [prefixWord, tailWord_284729, baseEnd_284729] using wordTrace_append hprefix tailTrace_284729
  have hstable : (prefixWord ++ tailWord_284729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284729).length < 2 ^ (prefixWord ++ tailWord_284729).sum := by decide
  have hdescent : baseEnd_284729 < baseStart_284729 := by decide
  rcases family_descends (prefixWord ++ tailWord_284729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284849 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 4]
def baseStart_284849 : Nat := 118140960795 + 284849 * 2 ^ 59
def prefixEnd_284849 : Nat := 4983230072969 + 3 ^ 40 * 284849 * 2
def baseEnd_284849 : Nat := 32503211322813613483891

theorem tailTrace_284849 : CollatzResearch.WordTrace tailWord_284849 prefixEnd_284849 32503211322813613483891 := by
  unfold tailWord_284849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389296545048196181217601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6926197696698797454145067 10389296545048196181217601)
  ·
    refine ⟨7791972408786147135913201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10389296545048196181217601 7791972408786147135913201)
    ·
      refine ⟨5843979306589610351934901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7791972408786147135913201 5843979306589610351934901)
      ·
        refine ⟨547873059992775970493897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5843979306589610351934901 547873059992775970493897)
        ·
          refine ⟨410904794994581977870423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547873059992775970493897 410904794994581977870423)
          ·
            refine ⟨616357192491872966805635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410904794994581977870423 616357192491872966805635)
            ·
              refine ⟨924535788737809450208453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616357192491872966805635 924535788737809450208453)
              ·
                refine ⟨173350460388339271914085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 924535788737809450208453 173350460388339271914085)
                ·
                  refine ⟨32503211322813613483891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173350460388339271914085 32503211322813613483891)
                  ·
                    rfl

theorem cell22_284849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_284849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284849 prefixEnd_284849 := by exact prefixLift 284849
  have htrace : WordTrace (prefixWord ++ tailWord_284849) baseStart_284849 baseEnd_284849 := by
    simpa [prefixWord, tailWord_284849, baseEnd_284849] using wordTrace_append hprefix tailTrace_284849
  have hstable : (prefixWord ++ tailWord_284849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284849).length < 2 ^ (prefixWord ++ tailWord_284849).sum := by decide
  have hdescent : baseEnd_284849 < baseStart_284849 := by decide
  rcases family_descends (prefixWord ++ tailWord_284849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284898 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_284898 : Nat := 118140960795 + 284898 * 2 ^ 59
def prefixEnd_284898 : Nat := 4983230072969 + 3 ^ 40 * 284898 * 2
def baseEnd_284898 : Nat := 97526407669821045976523

theorem tailTrace_284898 : CollatzResearch.WordTrace tailWord_284898 prefixEnd_284898 97526407669821045976523 := by
  unfold tailWord_284898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597770930467669387437837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6927389147913785033167565 2597770930467669387437837)
  ·
    refine ⟨974164098925376020289189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2597770930467669387437837 974164098925376020289189)
    ·
      refine ⟨182655768548508003804223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 974164098925376020289189 182655768548508003804223)
      ·
        refine ⟨273983652822762005706335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182655768548508003804223 273983652822762005706335)
        ·
          refine ⟨410975479234143008559503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273983652822762005706335 410975479234143008559503)
          ·
            refine ⟨616463218851214512839255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410975479234143008559503 616463218851214512839255)
            ·
              refine ⟨924694828276821769258883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616463218851214512839255 924694828276821769258883)
              ·
                refine ⟨1387042242415232653888325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924694828276821769258883 1387042242415232653888325)
                ·
                  refine ⟨260070420452856122604061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387042242415232653888325 260070420452856122604061)
                  ·
                    refine ⟨97526407669821045976523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260070420452856122604061 97526407669821045976523)
                    ·
                      rfl

theorem cell22_284898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_284898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284898 prefixEnd_284898 := by exact prefixLift 284898
  have htrace : WordTrace (prefixWord ++ tailWord_284898) baseStart_284898 baseEnd_284898 := by
    simpa [prefixWord, tailWord_284898, baseEnd_284898] using wordTrace_append hprefix tailTrace_284898
  have hstable : (prefixWord ++ tailWord_284898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284898).length < 2 ^ (prefixWord ++ tailWord_284898).sum := by decide
  have hdescent : baseEnd_284898 < baseStart_284898 := by decide
  rcases family_descends (prefixWord ++ tailWord_284898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284952 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_284952 : Nat := 118140960795 + 284952 * 2 ^ 59
def prefixEnd_284952 : Nat := 4983230072969 + 3 ^ 40 * 284952 * 2
def baseEnd_284952 : Nat := 97544892973382905126357

theorem tailTrace_284952 : CollatzResearch.WordTrace tailWord_284952 prefixEnd_284952 97544892973382905126357 := by
  unfold tailWord_284952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196526631837522386108555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6928702175783363181478073 5196526631837522386108555)
  ·
    refine ⟨7794789947756283579162833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196526631837522386108555 7794789947756283579162833)
    ·
      refine ⟨5846092460817212684372125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7794789947756283579162833 5846092460817212684372125)
      ·
        refine ⟨2192284672806454756639547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5846092460817212684372125 2192284672806454756639547)
        ·
          refine ⟨3288427009209682134959321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192284672806454756639547 3288427009209682134959321)
          ·
            refine ⟨2466320256907261601219491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288427009209682134959321 2466320256907261601219491)
            ·
              refine ⟨3699480385360892401829237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466320256907261601219491 3699480385360892401829237)
              ·
                refine ⟨346826286127583662671491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3699480385360892401829237 346826286127583662671491)
                ·
                  refine ⟨520239429191375494007237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346826286127583662671491 520239429191375494007237)
                  ·
                    refine ⟨97544892973382905126357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520239429191375494007237 97544892973382905126357)
                    ·
                      rfl

theorem cell22_284952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_284952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284952 prefixEnd_284952 := by exact prefixLift 284952
  have htrace : WordTrace (prefixWord ++ tailWord_284952) baseStart_284952 baseEnd_284952 := by
    simpa [prefixWord, tailWord_284952, baseEnd_284952] using wordTrace_append hprefix tailTrace_284952
  have hstable : (prefixWord ++ tailWord_284952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284952).length < 2 ^ (prefixWord ++ tailWord_284952).sum := by decide
  have hdescent : baseEnd_284952 < baseStart_284952 := by decide
  rcases family_descends (prefixWord ++ tailWord_284952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284973 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 5]
def baseStart_284973 : Nat := 118140960795 + 284973 * 2 ^ 59
def prefixEnd_284973 : Nat := 4983230072969 + 3 ^ 40 * 284973 * 2
def baseEnd_284973 : Nat := 32517360567515283450431

theorem tailTrace_284973 : CollatzResearch.WordTrace tailWord_284973 prefixEnd_284973 32517360567515283450431 := by
  unfold tailWord_284973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10393819196598965358731573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6929212797732643572487715 10393819196598965358731573)
  ·
    refine ⟨974420549681153002381085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10393819196598965358731573 974420549681153002381085)
    ·
      refine ⟨365407706130432375892907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 974420549681153002381085 365407706130432375892907)
      ·
        refine ⟨548111559195648563839361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365407706130432375892907 548111559195648563839361)
        ·
          refine ⟨411083669396736422879521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548111559195648563839361 411083669396736422879521)
          ·
            refine ⟨308312752047552317159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411083669396736422879521 308312752047552317159641)
            ·
              refine ⟨231234564035664237869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308312752047552317159641 231234564035664237869731)
              ·
                refine ⟨346851846053496356804597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231234564035664237869731 346851846053496356804597)
                ·
                  refine ⟨32517360567515283450431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 346851846053496356804597 32517360567515283450431)
                  ·
                    rfl

theorem cell22_284973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_284973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284973 prefixEnd_284973 := by exact prefixLift 284973
  have htrace : WordTrace (prefixWord ++ tailWord_284973) baseStart_284973 baseEnd_284973 := by
    simpa [prefixWord, tailWord_284973, baseEnd_284973] using wordTrace_append hprefix tailTrace_284973
  have hstable : (prefixWord ++ tailWord_284973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284973).length < 2 ^ (prefixWord ++ tailWord_284973).sum := by decide
  have hdescent : baseEnd_284973 < baseStart_284973 := by decide
  rcases family_descends (prefixWord ++ tailWord_284973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284995 : List Nat := [1, 1, 1, 3, 1, 3, 4, 8]
def baseStart_284995 : Nat := 118140960795 + 284995 * 2 ^ 59
def prefixEnd_284995 : Nat := 4983230072969 + 3 ^ 40 * 284995 * 2
def baseEnd_284995 : Nat := 10839956972460569589025

theorem tailTrace_284995 : CollatzResearch.WordTrace tailWord_284995 prefixEnd_284995 10839956972460569589025 := by
  unfold tailWord_284995
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394621602519263116032439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6929747735012842077354959 10394621602519263116032439)
  ·
    refine ⟨15591932403778894674048659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394621602519263116032439 15591932403778894674048659)
    ·
      refine ⟨23387898605668342011072989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591932403778894674048659 23387898605668342011072989)
      ·
        refine ⟨8770461977125628254152371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23387898605668342011072989 8770461977125628254152371)
        ·
          refine ⟨13155692965688442381228557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8770461977125628254152371 13155692965688442381228557)
          ·
            refine ⟨4933384862133165892960709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13155692965688442381228557 4933384862133165892960709)
            ·
              refine ⟨925009661649968604930133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4933384862133165892960709 925009661649968604930133)
              ·
                refine ⟨10839956972460569589025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 925009661649968604930133 10839956972460569589025)
                ·
                  rfl

theorem cell22_284995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_284995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_284995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_284995 prefixEnd_284995 := by exact prefixLift 284995
  have htrace : WordTrace (prefixWord ++ tailWord_284995) baseStart_284995 baseEnd_284995 := by
    simpa [prefixWord, tailWord_284995, baseEnd_284995] using wordTrace_append hprefix tailTrace_284995
  have hstable : (prefixWord ++ tailWord_284995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284995).length < 2 ^ (prefixWord ++ tailWord_284995).sum := by decide
  have hdescent : baseEnd_284995 < baseStart_284995 := by decide
  rcases family_descends (prefixWord ++ tailWord_284995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285149 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_285149 : Nat := 118140960795 + 285149 * 2 ^ 59
def prefixEnd_285149 : Nat := 4983230072969 + 3 ^ 40 * 285149 * 2
def baseEnd_285149 : Nat := 97612330099340057950753

theorem tailTrace_285149 : CollatzResearch.WordTrace tailWord_285149 prefixEnd_285149 97612330099340057950753 := by
  unfold tailWord_285149
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400238443961347417138501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6933492295974231611425667 10400238443961347417138501)
  ·
    refine ⟨1950044708242752640713469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10400238443961347417138501 1950044708242752640713469)
    ·
      refine ⟨731266765591032240267551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1950044708242752640713469 731266765591032240267551)
      ·
        refine ⟨1096900148386548360401327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731266765591032240267551 1096900148386548360401327)
        ·
          refine ⟨1645350222579822540601991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096900148386548360401327 1645350222579822540601991)
          ·
            refine ⟨2468025333869733810902987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645350222579822540601991 2468025333869733810902987)
            ·
              refine ⟨3702038000804600716354481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468025333869733810902987 3702038000804600716354481)
              ·
                refine ⟨2776528500603450537265861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702038000804600716354481 2776528500603450537265861)
                ·
                  refine ⟨520599093863146975737349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2776528500603450537265861 520599093863146975737349)
                  ·
                    refine ⟨97612330099340057950753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520599093863146975737349 97612330099340057950753)
                    ·
                      rfl

theorem cell22_285149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_285149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285149 prefixEnd_285149 := by exact prefixLift 285149
  have htrace : WordTrace (prefixWord ++ tailWord_285149) baseStart_285149 baseEnd_285149 := by
    simpa [prefixWord, tailWord_285149, baseEnd_285149] using wordTrace_append hprefix tailTrace_285149
  have hstable : (prefixWord ++ tailWord_285149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285149).length < 2 ^ (prefixWord ++ tailWord_285149).sum := by decide
  have hdescent : baseEnd_285149 < baseStart_285149 := by decide
  rcases family_descends (prefixWord ++ tailWord_285149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285151 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 2, 3]
def baseStart_285151 : Nat := 118140960795 + 285151 * 2 ^ 59
def prefixEnd_285151 : Nat := 4983230072969 + 3 ^ 40 * 285151 * 2
def baseEnd_285151 : Nat := 97613014740212719400747

theorem tailTrace_285151 : CollatzResearch.WordTrace tailWord_285151 prefixEnd_285151 97613014740212719400747 := by
  unfold tailWord_285151
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400311389954101758711307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6933540926636067839140871 10400311389954101758711307)
  ·
    refine ⟨15600467084931152638066961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400311389954101758711307 15600467084931152638066961)
    ·
      refine ⟨11700350313698364478550221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15600467084931152638066961 11700350313698364478550221)
      ·
        refine ⟨4387631367636886679456333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11700350313698364478550221 4387631367636886679456333)
        ·
          refine ⟨1645361762863832504796125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387631367636886679456333 1645361762863832504796125)
          ·
            refine ⟨617010661073937189298547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1645361762863832504796125 617010661073937189298547)
            ·
              refine ⟨925515991610905783947821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617010661073937189298547 925515991610905783947821)
              ·
                refine ⟨347068496854089668980433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925515991610905783947821 347068496854089668980433)
                ·
                  refine ⟨260301372640567251735325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347068496854089668980433 260301372640567251735325)
                  ·
                    refine ⟨97613014740212719400747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260301372640567251735325 97613014740212719400747)
                    ·
                      rfl

theorem cell22_285151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_285151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285151 prefixEnd_285151 := by exact prefixLift 285151
  have htrace : WordTrace (prefixWord ++ tailWord_285151) baseStart_285151 baseEnd_285151 := by
    simpa [prefixWord, tailWord_285151, baseEnd_285151] using wordTrace_append hprefix tailTrace_285151
  have hstable : (prefixWord ++ tailWord_285151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285151).length < 2 ^ (prefixWord ++ tailWord_285151).sum := by decide
  have hdescent : baseEnd_285151 < baseStart_285151 := by decide
  rcases family_descends (prefixWord ++ tailWord_285151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285166 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_285166 : Nat := 118140960795 + 285166 * 2 ^ 59
def prefixEnd_285166 : Nat := 4983230072969 + 3 ^ 40 * 285166 * 2
def baseEnd_285166 : Nat := 97618149546757680275701

theorem tailTrace_285166 : CollatzResearch.WordTrace tailWord_285166 prefixEnd_285166 97618149546757680275701 := by
  unfold tailWord_285166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300107310612469915063419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6933905656599839547004901 1300107310612469915063419)
  ·
    refine ⟨1950160965918704872595129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300107310612469915063419 1950160965918704872595129)
    ·
      refine ⟨1462620724439028654446347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1950160965918704872595129 1462620724439028654446347)
      ·
        refine ⟨2193931086658542981669521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462620724439028654446347 2193931086658542981669521)
        ·
          refine ⟨1645448314993907236252141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193931086658542981669521 1645448314993907236252141)
          ·
            refine ⟨617043118122715213594553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1645448314993907236252141 617043118122715213594553)
            ·
              refine ⟨462782338592036410195915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617043118122715213594553 462782338592036410195915)
              ·
                refine ⟨694173507888054615293873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462782338592036410195915 694173507888054615293873)
                ·
                  refine ⟨520630130916040961470405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694173507888054615293873 520630130916040961470405)
                  ·
                    refine ⟨97618149546757680275701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520630130916040961470405 97618149546757680275701)
                    ·
                      rfl

theorem cell22_285166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_285166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285166 prefixEnd_285166 := by exact prefixLift 285166
  have htrace : WordTrace (prefixWord ++ tailWord_285166) baseStart_285166 baseEnd_285166 := by
    simpa [prefixWord, tailWord_285166, baseEnd_285166] using wordTrace_append hprefix tailTrace_285166
  have hstable : (prefixWord ++ tailWord_285166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285166).length < 2 ^ (prefixWord ++ tailWord_285166).sum := by decide
  have hdescent : baseEnd_285166 < baseStart_285166 := by decide
  rcases family_descends (prefixWord ++ tailWord_285166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285284 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_285284 : Nat := 118140960795 + 285284 * 2 ^ 59
def prefixEnd_285284 : Nat := 4983230072969 + 3 ^ 40 * 285284 * 2
def baseEnd_285284 : Nat := 97658543358244705825339

theorem tailTrace_285284 : CollatzResearch.WordTrace tailWord_285284 prefixEnd_285284 97658543358244705825339 := by
  unfold tailWord_285284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202581149236132736651453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6936774865648176982201937 5202581149236132736651453)
  ·
    refine ⟨1950967930963549776244295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5202581149236132736651453 1950967930963549776244295)
    ·
      refine ⟨2926451896445324664366443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950967930963549776244295 2926451896445324664366443)
      ·
        refine ⟨4389677844667986996549665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926451896445324664366443 4389677844667986996549665)
        ·
          refine ⟨3292258383500990247412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4389677844667986996549665 3292258383500990247412249)
          ·
            refine ⟨2469193787625742685559187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292258383500990247412249 2469193787625742685559187)
            ·
              refine ⟨3703790681438614028338781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469193787625742685559187 3703790681438614028338781)
              ·
                refine ⟨1388921505539480260627043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3703790681438614028338781 1388921505539480260627043)
                ·
                  refine ⟨2083382258309220390940565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388921505539480260627043 2083382258309220390940565)
                  ·
                    refine ⟨97658543358244705825339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2083382258309220390940565 97658543358244705825339)
                    ·
                      rfl

theorem cell22_285284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_285284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285284 prefixEnd_285284 := by exact prefixLift 285284
  have htrace : WordTrace (prefixWord ++ tailWord_285284) baseStart_285284 baseEnd_285284 := by
    simpa [prefixWord, tailWord_285284, baseEnd_285284] using wordTrace_append hprefix tailTrace_285284
  have hstable : (prefixWord ++ tailWord_285284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285284).length < 2 ^ (prefixWord ++ tailWord_285284).sum := by decide
  have hdescent : baseEnd_285284 < baseStart_285284 := by decide
  rcases family_descends (prefixWord ++ tailWord_285284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285316 : List Nat := [2, 3, 2, 1, 3, 2, 2, 7]
def baseStart_285316 : Nat := 118140960795 + 285316 * 2 ^ 59
def prefixEnd_285316 : Nat := 4983230072969 + 3 ^ 40 * 285316 * 2
def baseEnd_285316 : Nat := 10852166401356365447249

theorem tailTrace_285316 : CollatzResearch.WordTrace tailWord_285316 prefixEnd_285316 10852166401356365447249 := by
  unfold tailWord_285316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203164717178167469233901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6937552956237556625645201 5203164717178167469233901)
  ·
    refine ⟨1951186768941812800962713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5203164717178167469233901 1951186768941812800962713)
    ·
      refine ⟨1463390076706359600722035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1951186768941812800962713 1463390076706359600722035)
      ·
        refine ⟨2195085115059539401083053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463390076706359600722035 2195085115059539401083053)
        ·
          refine ⟨823156918147327275406145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2195085115059539401083053 823156918147327275406145)
          ·
            refine ⟨617367688610495456554609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823156918147327275406145 617367688610495456554609)
            ·
              refine ⟨463025766457871592415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617367688610495456554609 463025766457871592415957)
              ·
                refine ⟨10852166401356365447249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 463025766457871592415957 10852166401356365447249)
                ·
                  rfl

theorem cell22_285316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_285316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285316 prefixEnd_285316 := by exact prefixLift 285316
  have htrace : WordTrace (prefixWord ++ tailWord_285316) baseStart_285316 baseEnd_285316 := by
    simpa [prefixWord, tailWord_285316, baseEnd_285316] using wordTrace_append hprefix tailTrace_285316
  have hstable : (prefixWord ++ tailWord_285316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285316).length < 2 ^ (prefixWord ++ tailWord_285316).sum := by decide
  have hdescent : baseEnd_285316 < baseStart_285316 := by decide
  rcases family_descends (prefixWord ++ tailWord_285316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285376 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_285376 : Nat := 118140960795 + 285376 * 2 ^ 59
def prefixEnd_285376 : Nat := 4983230072969 + 3 ^ 40 * 285376 * 2
def baseEnd_285376 : Nat := 97690036838387132525057

theorem tailTrace_285376 : CollatzResearch.WordTrace tailWord_285376 prefixEnd_285376 97690036838387132525057 := by
  unfold tailWord_285376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204258907069482592825991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6939011876092643457101321 5204258907069482592825991)
  ·
    refine ⟨7806388360604223889238987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5204258907069482592825991 7806388360604223889238987)
    ·
      refine ⟨11709582540906335833858481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806388360604223889238987 11709582540906335833858481)
      ·
        refine ⟨8782186905679751875393861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11709582540906335833858481 8782186905679751875393861)
        ·
          refine ⟨1646660044814953476636349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8782186905679751875393861 1646660044814953476636349)
          ·
            refine ⟨617497516805607553738631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1646660044814953476636349 617497516805607553738631)
            ·
              refine ⟨926246275208411330607947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617497516805607553738631 926246275208411330607947)
              ·
                refine ⟨1389369412812616995911921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926246275208411330607947 1389369412812616995911921)
                ·
                  refine ⟨1042027059609462746933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389369412812616995911921 1042027059609462746933941)
                  ·
                    refine ⟨97690036838387132525057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042027059609462746933941 97690036838387132525057)
                    ·
                      rfl

theorem cell22_285376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_285376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285376 prefixEnd_285376 := by exact prefixLift 285376
  have htrace : WordTrace (prefixWord ++ tailWord_285376) baseStart_285376 baseEnd_285376 := by
    simpa [prefixWord, tailWord_285376, baseEnd_285376] using wordTrace_append hprefix tailTrace_285376
  have hstable : (prefixWord ++ tailWord_285376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285376).length < 2 ^ (prefixWord ++ tailWord_285376).sum := by decide
  have hdescent : baseEnd_285376 < baseStart_285376 := by decide
  rcases family_descends (prefixWord ++ tailWord_285376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285423 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 4]
def baseStart_285423 : Nat := 118140960795 + 285423 * 2 ^ 59
def prefixEnd_285423 : Nat := 4983230072969 + 3 ^ 40 * 285423 * 2
def baseEnd_285423 : Nat := 32568708632964892199971

theorem tailTrace_285423 : CollatzResearch.WordTrace tailWord_285423 prefixEnd_285423 32568708632964892199971 := by
  unfold tailWord_285423
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410232044968692212612923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6940154696645794808408615 10410232044968692212612923)
  ·
    refine ⟨15615348067453038318919385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10410232044968692212612923 15615348067453038318919385)
    ·
      refine ⟨11711511050589778739189539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15615348067453038318919385 11711511050589778739189539)
      ·
        refine ⟨17567266575884668108784309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11711511050589778739189539 17567266575884668108784309)
        ·
          refine ⟨1646931241489187635198529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17567266575884668108784309 1646931241489187635198529)
          ·
            refine ⟨1235198431116890726398897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646931241489187635198529 1235198431116890726398897)
            ·
              refine ⟨926398823337668044799173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235198431116890726398897 926398823337668044799173)
              ·
                refine ⟨173699779375812758399845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 926398823337668044799173 173699779375812758399845)
                ·
                  refine ⟨32568708632964892199971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173699779375812758399845 32568708632964892199971)
                  ·
                    rfl

theorem cell22_285423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 4].length) (baseStart_285423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285423 prefixEnd_285423 := by exact prefixLift 285423
  have htrace : WordTrace (prefixWord ++ tailWord_285423) baseStart_285423 baseEnd_285423 := by
    simpa [prefixWord, tailWord_285423, baseEnd_285423] using wordTrace_append hprefix tailTrace_285423
  have hstable : (prefixWord ++ tailWord_285423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285423).length < 2 ^ (prefixWord ++ tailWord_285423).sum := by decide
  have hdescent : baseEnd_285423 < baseStart_285423 := by decide
  rcases family_descends (prefixWord ++ tailWord_285423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285429 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 5]
def baseStart_285429 : Nat := 118140960795 + 285429 * 2 ^ 59
def prefixEnd_285429 : Nat := 4983230072969 + 3 ^ 40 * 285429 * 2
def baseEnd_285429 : Nat := 32569393273837553649965

theorem tailTrace_285429 : CollatzResearch.WordTrace tailWord_285429 prefixEnd_285429 32569393273837553649965 := by
  unfold tailWord_285429
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410450882946955237331341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6940300588631303491554227 10410450882946955237331341)
  ·
    refine ⟨3903919081105108213999253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10410450882946955237331341 3903919081105108213999253)
    ·
      refine ⟨182996206926801947531215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3903919081105108213999253 182996206926801947531215)
      ·
        refine ⟨274494310390202921296823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182996206926801947531215 274494310390202921296823)
        ·
          refine ⟨411741465585304381945235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274494310390202921296823 411741465585304381945235)
          ·
            refine ⟨617612198377956572917853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411741465585304381945235 617612198377956572917853)
            ·
              refine ⟨231604574391733714844195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 617612198377956572917853 231604574391733714844195)
              ·
                refine ⟨347406861587600572266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231604574391733714844195 347406861587600572266293)
                ·
                  refine ⟨32569393273837553649965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 347406861587600572266293 32569393273837553649965)
                  ·
                    rfl

theorem cell22_285429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_285429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285429 prefixEnd_285429 := by exact prefixLift 285429
  have htrace : WordTrace (prefixWord ++ tailWord_285429) baseStart_285429 baseEnd_285429 := by
    simpa [prefixWord, tailWord_285429, baseEnd_285429] using wordTrace_append hprefix tailTrace_285429
  have hstable : (prefixWord ++ tailWord_285429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285429).length < 2 ^ (prefixWord ++ tailWord_285429).sum := by decide
  have hdescent : baseEnd_285429 < baseStart_285429 := by decide
  rcases family_descends (prefixWord ++ tailWord_285429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285436 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_285436 : Nat := 118140960795 + 285436 * 2 ^ 59
def prefixEnd_285436 : Nat := 4983230072969 + 3 ^ 40 * 285436 * 2
def baseEnd_285436 : Nat := 97710576064566976024873

theorem tailTrace_285436 : CollatzResearch.WordTrace tailWord_285436 prefixEnd_285436 97710576064566976024873 := by
  unfold tailWord_285436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205353096960797716418081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6940470795947730288557441 5205353096960797716418081)
  ·
    refine ⟨3904014822720598287313561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5205353096960797716418081 3904014822720598287313561)
    ·
      refine ⟨2928011117040448715485171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3904014822720598287313561 2928011117040448715485171)
      ·
        refine ⟨4392016675560673073227757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928011117040448715485171 4392016675560673073227757)
        ·
          refine ⟨1647006253335252402460409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4392016675560673073227757 1647006253335252402460409)
          ·
            refine ⟨1235254690001439301845307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647006253335252402460409 1235254690001439301845307)
            ·
              refine ⟨1852882035002158952767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235254690001439301845307 1852882035002158952767961)
              ·
                refine ⟨1389661526251619214575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852882035002158952767961 1389661526251619214575971)
                ·
                  refine ⟨2084492289377428821863957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389661526251619214575971 2084492289377428821863957)
                  ·
                    refine ⟨97710576064566976024873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2084492289377428821863957 97710576064566976024873)
                    ·
                      rfl

theorem cell22_285436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_285436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285436 prefixEnd_285436 := by exact prefixLift 285436
  have htrace : WordTrace (prefixWord ++ tailWord_285436) baseStart_285436 baseEnd_285436 := by
    simpa [prefixWord, tailWord_285436, baseEnd_285436] using wordTrace_append hprefix tailTrace_285436
  have hstable : (prefixWord ++ tailWord_285436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285436).length < 2 ^ (prefixWord ++ tailWord_285436).sum := by decide
  have hdescent : baseEnd_285436 < baseStart_285436 := by decide
  rcases family_descends (prefixWord ++ tailWord_285436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285511 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_285511 : Nat := 118140960795 + 285511 * 2 ^ 59
def prefixEnd_285511 : Nat := 4983230072969 + 3 ^ 40 * 285511 * 2
def baseEnd_285511 : Nat := 97736250097291780399643

theorem tailTrace_285511 : CollatzResearch.WordTrace tailWord_285511 prefixEnd_285511 97736250097291780399643 := by
  unfold tailWord_285511
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413441668649883241816387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6942294445766588827877591 10413441668649883241816387)
  ·
    refine ⟨15620162502974824862724581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413441668649883241816387 15620162502974824862724581)
    ·
      refine ⟨2928780469307779661760859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15620162502974824862724581 2928780469307779661760859)
      ·
        refine ⟨4393170703961669492641289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928780469307779661760859 4393170703961669492641289)
        ·
          refine ⟨3294878027971252119480967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4393170703961669492641289 3294878027971252119480967)
          ·
            refine ⟨4942317041956878179221451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294878027971252119480967 4942317041956878179221451)
            ·
              refine ⟨7413475562935317268832177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942317041956878179221451 7413475562935317268832177)
              ·
                refine ⟨5560106672201487951624133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7413475562935317268832177 5560106672201487951624133)
                ·
                  refine ⟨1042520001037778990929525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5560106672201487951624133 1042520001037778990929525)
                  ·
                    refine ⟨97736250097291780399643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042520001037778990929525 97736250097291780399643)
                    ·
                      rfl

theorem cell22_285511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_285511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285511 prefixEnd_285511 := by exact prefixLift 285511
  have htrace : WordTrace (prefixWord ++ tailWord_285511) baseStart_285511 baseEnd_285511 := by
    simpa [prefixWord, tailWord_285511, baseEnd_285511] using wordTrace_append hprefix tailTrace_285511
  have hstable : (prefixWord ++ tailWord_285511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285511).length < 2 ^ (prefixWord ++ tailWord_285511).sum := by decide
  have hdescent : baseEnd_285511 < baseStart_285511 := by decide
  rcases family_descends (prefixWord ++ tailWord_285511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285543 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_285543 : Nat := 118140960795 + 285543 * 2 ^ 59
def prefixEnd_285543 : Nat := 4983230072969 + 3 ^ 40 * 285543 * 2
def baseEnd_285543 : Nat := 97747204351254363599545

theorem tailTrace_285543 : CollatzResearch.WordTrace tailWord_285543 prefixEnd_285543 97747204351254363599545 := by
  unfold tailWord_285543
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414608804533952706981283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943072536355968471320855 10414608804533952706981283)
  ·
    refine ⟨15621913206800929060471925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10414608804533952706981283 15621913206800929060471925)
    ·
      refine ⟨1464554363137587099419243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15621913206800929060471925 1464554363137587099419243)
      ·
        refine ⟨2196831544706380649128865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464554363137587099419243 2196831544706380649128865)
        ·
          refine ⟨1647623658529785486846649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196831544706380649128865 1647623658529785486846649)
          ·
            refine ⟨1235717743897339115134987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647623658529785486846649 1235717743897339115134987)
            ·
              refine ⟨1853576615846008672702481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235717743897339115134987 1853576615846008672702481)
              ·
                refine ⟨1390182461884506504526861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853576615846008672702481 1390182461884506504526861)
                ·
                  refine ⟨521318423206689939197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1390182461884506504526861 521318423206689939197573)
                  ·
                    refine ⟨97747204351254363599545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521318423206689939197573 97747204351254363599545)
                    ·
                      rfl

theorem cell22_285543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_285543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285543 prefixEnd_285543 := by exact prefixLift 285543
  have htrace : WordTrace (prefixWord ++ tailWord_285543) baseStart_285543 baseEnd_285543 := by
    simpa [prefixWord, tailWord_285543, baseEnd_285543] using wordTrace_append hprefix tailTrace_285543
  have hstable : (prefixWord ++ tailWord_285543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285543).length < 2 ^ (prefixWord ++ tailWord_285543).sum := by decide
  have hdescent : baseEnd_285543 < baseStart_285543 := by decide
  rcases family_descends (prefixWord ++ tailWord_285543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285573 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_285573 : Nat := 118140960795 + 285573 * 2 ^ 59
def prefixEnd_285573 : Nat := 4983230072969 + 3 ^ 40 * 285573 * 2
def baseEnd_285573 : Nat := 97757473964344285349453

theorem tailTrace_285573 : CollatzResearch.WordTrace tailWord_285573 prefixEnd_285573 97757473964344285349453 := by
  unfold tailWord_285573
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415702994425267830573373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943801996283511887048915 10415702994425267830573373)
  ·
    refine ⟨3905888622909475436465015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10415702994425267830573373 3905888622909475436465015)
    ·
      refine ⟨5858832934364213154697523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3905888622909475436465015 5858832934364213154697523)
      ·
        refine ⟨8788249401546319732046285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5858832934364213154697523 8788249401546319732046285)
        ·
          refine ⟨3295593525579869899517357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8788249401546319732046285 3295593525579869899517357)
          ·
            refine ⟨1235847572092451212319009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3295593525579869899517357 1235847572092451212319009)
            ·
              refine ⟨926885679069338409239257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235847572092451212319009 926885679069338409239257)
              ·
                refine ⟨695164259302003806929443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926885679069338409239257 695164259302003806929443)
                ·
                  refine ⟨1042746388953005710394165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695164259302003806929443 1042746388953005710394165)
                  ·
                    refine ⟨97757473964344285349453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042746388953005710394165 97757473964344285349453)
                    ·
                      rfl

theorem cell22_285573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_285573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285573 prefixEnd_285573 := by exact prefixLift 285573
  have htrace : WordTrace (prefixWord ++ tailWord_285573) baseStart_285573 baseEnd_285573 := by
    simpa [prefixWord, tailWord_285573, baseEnd_285573] using wordTrace_append hprefix tailTrace_285573
  have hstable : (prefixWord ++ tailWord_285573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285573).length < 2 ^ (prefixWord ++ tailWord_285573).sum := by decide
  have hdescent : baseEnd_285573 < baseStart_285573 := by decide
  rcases family_descends (prefixWord ++ tailWord_285573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285575 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 4]
def baseStart_285575 : Nat := 118140960795 + 285575 * 2 ^ 59
def prefixEnd_285575 : Nat := 4983230072969 + 3 ^ 40 * 285575 * 2
def baseEnd_285575 : Nat := 32586052868405648933149

theorem tailTrace_285575 : CollatzResearch.WordTrace tailWord_285575 prefixEnd_285575 32586052868405648933149 := by
  unfold tailWord_285575
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415775940418022172146179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943850626945348114764119 10415775940418022172146179)
  ·
    refine ⟨15623663910627033258219269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10415775940418022172146179 15623663910627033258219269)
    ·
      refine ⟨2929436983242568735916113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15623663910627033258219269 2929436983242568735916113)
      ·
        refine ⟨2197077737431926551937085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929436983242568735916113 2197077737431926551937085)
        ·
          refine ⟨823904151536972456976407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2197077737431926551937085 823904151536972456976407)
          ·
            refine ⟨1235856227305458685464611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823904151536972456976407 1235856227305458685464611)
            ·
              refine ⟨1853784340958188028196917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235856227305458685464611 1853784340958188028196917)
              ·
                refine ⟨173792281964830127643461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1853784340958188028196917 173792281964830127643461)
                ·
                  refine ⟨32586052868405648933149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173792281964830127643461 32586052868405648933149)
                  ·
                    rfl

theorem cell22_285575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 4].length) (baseStart_285575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285575 prefixEnd_285575 := by exact prefixLift 285575
  have htrace : WordTrace (prefixWord ++ tailWord_285575) baseStart_285575 baseEnd_285575 := by
    simpa [prefixWord, tailWord_285575, baseEnd_285575] using wordTrace_append hprefix tailTrace_285575
  have hstable : (prefixWord ++ tailWord_285575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285575).length < 2 ^ (prefixWord ++ tailWord_285575).sum := by decide
  have hdescent : baseEnd_285575 < baseStart_285575 := by decide
  rcases family_descends (prefixWord ++ tailWord_285575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285577 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_285577 : Nat := 118140960795 + 285577 * 2 ^ 59
def prefixEnd_285577 : Nat := 4983230072969 + 3 ^ 40 * 285577 * 2
def baseEnd_285577 : Nat := 97758843246089608249441

theorem tailTrace_285577 : CollatzResearch.WordTrace tailWord_285577 prefixEnd_285577 97758843246089608249441 := by
  unfold tailWord_285577
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415848886410776513718985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943899257607184342479323 10415848886410776513718985)
  ·
    refine ⟨7811886664808082385289239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10415848886410776513718985 7811886664808082385289239)
    ·
      refine ⟨11717829997212123577933859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7811886664808082385289239 11717829997212123577933859)
      ·
        refine ⟨17576744995818185366900789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11717829997212123577933859 17576744995818185366900789)
        ·
          refine ⟨1647819843357954878146949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17576744995818185366900789 1647819843357954878146949)
          ·
            refine ⟨308966220629616539652553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1647819843357954878146949 308966220629616539652553)
            ·
              refine ⟨231724665472212404739415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308966220629616539652553 231724665472212404739415)
              ·
                refine ⟨347586998208318607109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231724665472212404739415 347586998208318607109123)
                ·
                  refine ⟨521380497312477910663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347586998208318607109123 521380497312477910663685)
                  ·
                    refine ⟨97758843246089608249441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521380497312477910663685 97758843246089608249441)
                    ·
                      rfl

theorem cell22_285577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_285577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285577 prefixEnd_285577 := by exact prefixLift 285577
  have htrace : WordTrace (prefixWord ++ tailWord_285577) baseStart_285577 baseEnd_285577 := by
    simpa [prefixWord, tailWord_285577, baseEnd_285577] using wordTrace_append hprefix tailTrace_285577
  have hstable : (prefixWord ++ tailWord_285577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285577).length < 2 ^ (prefixWord ++ tailWord_285577).sum := by decide
  have hdescent : baseEnd_285577 < baseStart_285577 := by decide
  rcases family_descends (prefixWord ++ tailWord_285577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285607 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 5]
def baseStart_285607 : Nat := 118140960795 + 285607 * 2 ^ 59
def prefixEnd_285607 : Nat := 4983230072969 + 3 ^ 40 * 285607 * 2
def baseEnd_285607 : Nat := 97769112859179529999349

theorem tailTrace_285607 : CollatzResearch.WordTrace tailWord_285607 prefixEnd_285607 97769112859179529999349 := by
  unfold tailWord_285607
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416943076302091637311075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6944628717534727758207383 10416943076302091637311075)
  ·
    refine ⟨15625414614453137455966613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10416943076302091637311075 15625414614453137455966613)
    ·
      refine ⟨732441310052490818248435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15625414614453137455966613 732441310052490818248435)
      ·
        refine ⟨1098661965078736227372653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732441310052490818248435 1098661965078736227372653)
        ·
          refine ⟨411998236904526085264745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1098661965078736227372653 411998236904526085264745)
          ·
            refine ⟨308998677678394563948559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411998236904526085264745 308998677678394563948559)
            ·
              refine ⟨463498016517591845922839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308998677678394563948559 463498016517591845922839)
              ·
                refine ⟨695247024776387768884259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463498016517591845922839 695247024776387768884259)
                ·
                  refine ⟨1042870537164581653326389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695247024776387768884259 1042870537164581653326389)
                  ·
                    refine ⟨97769112859179529999349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042870537164581653326389 97769112859179529999349)
                    ·
                      rfl

theorem cell22_285607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_285607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285607 prefixEnd_285607 := by exact prefixLift 285607
  have htrace : WordTrace (prefixWord ++ tailWord_285607) baseStart_285607 baseEnd_285607 := by
    simpa [prefixWord, tailWord_285607, baseEnd_285607] using wordTrace_append hprefix tailTrace_285607
  have hstable : (prefixWord ++ tailWord_285607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285607).length < 2 ^ (prefixWord ++ tailWord_285607).sum := by decide
  have hdescent : baseEnd_285607 < baseStart_285607 := by decide
  rcases family_descends (prefixWord ++ tailWord_285607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285648 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_285648 : Nat := 118140960795 + 285648 * 2 ^ 59
def prefixEnd_285648 : Nat := 4983230072969 + 3 ^ 40 * 285648 * 2
def baseEnd_285648 : Nat := 32594382665689696574741

theorem tailTrace_285648 : CollatzResearch.WordTrace tailWord_285648 prefixEnd_285648 32594382665689696574741 := by
  unfold tailWord_285648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209219234576777819776799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6945625646102370426369065 5209219234576777819776799)
  ·
    refine ⟨7813828851865166729665199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5209219234576777819776799 7813828851865166729665199)
    ·
      refine ⟨11720743277797750094497799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7813828851865166729665199 11720743277797750094497799)
      ·
        refine ⟨17581114916696625141746699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11720743277797750094497799 17581114916696625141746699)
        ·
          refine ⟨26371672375044937712620049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17581114916696625141746699 26371672375044937712620049)
          ·
            refine ⟨19778754281283703284465037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26371672375044937712620049 19778754281283703284465037)
            ·
              refine ⟨7417032855481388731674389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19778754281283703284465037 7417032855481388731674389)
              ·
                refine ⟨347673415100690096797237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7417032855481388731674389 347673415100690096797237)
                ·
                  refine ⟨32594382665689696574741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 347673415100690096797237 32594382665689696574741)
                  ·
                    rfl

theorem cell22_285648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_285648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285648 prefixEnd_285648 := by exact prefixLift 285648
  have htrace : WordTrace (prefixWord ++ tailWord_285648) baseStart_285648 baseEnd_285648 := by
    simpa [prefixWord, tailWord_285648, baseEnd_285648] using wordTrace_append hprefix tailTrace_285648
  have hstable : (prefixWord ++ tailWord_285648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285648).length < 2 ^ (prefixWord ++ tailWord_285648).sum := by decide
  have hdescent : baseEnd_285648 < baseStart_285648 := by decide
  rcases family_descends (prefixWord ++ tailWord_285648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285652 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_285652 : Nat := 118140960795 + 285652 * 2 ^ 59
def prefixEnd_285652 : Nat := 4983230072969 + 3 ^ 40 * 285652 * 2
def baseEnd_285652 : Nat := 97784517278814412624211

theorem tailTrace_285652 : CollatzResearch.WordTrace tailWord_285652 prefixEnd_285652 97784517278814412624211 := by
  unfold tailWord_285652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209292180569532161349605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6945722907426042881799473 5209292180569532161349605)
  ·
    refine ⟨976742283856787280253051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5209292180569532161349605 976742283856787280253051)
    ·
      refine ⟨1465113425785180920379577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976742283856787280253051 1465113425785180920379577)
      ·
        refine ⟨1098835069338885690284683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465113425785180920379577 1098835069338885690284683)
        ·
          refine ⟨1648252604008328535427025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098835069338885690284683 1648252604008328535427025)
          ·
            refine ⟨1236189453006246401570269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648252604008328535427025 1236189453006246401570269)
            ·
              refine ⟨463571044877342400588851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236189453006246401570269 463571044877342400588851)
              ·
                refine ⟨695356567316013600883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463571044877342400588851 695356567316013600883277)
                ·
                  refine ⟨260758712743505100331229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695356567316013600883277 260758712743505100331229)
                  ·
                    refine ⟨97784517278814412624211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260758712743505100331229 97784517278814412624211)
                    ·
                      rfl

theorem cell22_285652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_285652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285652 prefixEnd_285652 := by exact prefixLift 285652
  have htrace : WordTrace (prefixWord ++ tailWord_285652) baseStart_285652 baseEnd_285652 := by
    simpa [prefixWord, tailWord_285652, baseEnd_285652] using wordTrace_append hprefix tailTrace_285652
  have hstable : (prefixWord ++ tailWord_285652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285652).length < 2 ^ (prefixWord ++ tailWord_285652).sum := by decide
  have hdescent : baseEnd_285652 < baseStart_285652 := by decide
  rcases family_descends (prefixWord ++ tailWord_285652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285742 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_285742 : Nat := 118140960795 + 285742 * 2 ^ 59
def prefixEnd_285742 : Nat := 4983230072969 + 3 ^ 40 * 285742 * 2
def baseEnd_285742 : Nat := 97815326118084177873935

theorem tailTrace_285742 : CollatzResearch.WordTrace tailWord_285742 prefixEnd_285742 97815326118084177873935 := by
  unfold tailWord_285742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302733366351626211684435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6947911287208673128983653 1302733366351626211684435)
  ·
    refine ⟨1954100049527439317526653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1302733366351626211684435 1954100049527439317526653)
    ·
      refine ⟨732787518572789744072495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1954100049527439317526653 732787518572789744072495)
      ·
        refine ⟨1099181277859184616108743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732787518572789744072495 1099181277859184616108743)
        ·
          refine ⟨1648771916788776924163115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099181277859184616108743 1648771916788776924163115)
          ·
            refine ⟨2473157875183165386244673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648771916788776924163115 2473157875183165386244673)
            ·
              refine ⟨1854868406387374039683505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473157875183165386244673 1854868406387374039683505)
              ·
                refine ⟨1391151304790530529762629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854868406387374039683505 1391151304790530529762629)
                ·
                  refine ⟨260840869648224474330493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391151304790530529762629 260840869648224474330493)
                  ·
                    refine ⟨97815326118084177873935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260840869648224474330493 97815326118084177873935)
                    ·
                      rfl

theorem cell22_285742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_285742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285742 prefixEnd_285742 := by exact prefixLift 285742
  have htrace : WordTrace (prefixWord ++ tailWord_285742) baseStart_285742 baseEnd_285742 := by
    simpa [prefixWord, tailWord_285742, baseEnd_285742] using wordTrace_append hprefix tailTrace_285742
  have hstable : (prefixWord ++ tailWord_285742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285742).length < 2 ^ (prefixWord ++ tailWord_285742).sum := by decide
  have hdescent : baseEnd_285742 < baseStart_285742 := by decide
  rcases family_descends (prefixWord ++ tailWord_285742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285821 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_285821 : Nat := 118140960795 + 285821 * 2 ^ 59
def prefixEnd_285821 : Nat := 4983230072969 + 3 ^ 40 * 285821 * 2
def baseEnd_285821 : Nat := 97842369432554305148693

theorem tailTrace_285821 : CollatzResearch.WordTrace tailWord_285821 prefixEnd_285821 97842369432554305148693 := by
  unfold tailWord_285821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424748297526806185601317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6949832198351204123734211 10424748297526806185601317)
  ·
    refine ⟨1954640305786276159800247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10424748297526806185601317 1954640305786276159800247)
    ·
      refine ⟨2931960458679414239700371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954640305786276159800247 2931960458679414239700371)
      ·
        refine ⟨4397940688019121359550557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931960458679414239700371 4397940688019121359550557)
        ·
          refine ⟨1649227758007170509831459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4397940688019121359550557 1649227758007170509831459)
          ·
            refine ⟨2473841637010755764747189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649227758007170509831459 2473841637010755764747189)
            ·
              refine ⟨231922653469758352945049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2473841637010755764747189 231922653469758352945049)
              ·
                refine ⟨173941990102318764708787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231922653469758352945049 173941990102318764708787)
                ·
                  refine ⟨260912985153478147063181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173941990102318764708787 260912985153478147063181)
                  ·
                    refine ⟨97842369432554305148693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260912985153478147063181 97842369432554305148693)
                    ·
                      rfl

theorem cell22_285821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_285821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285821 prefixEnd_285821 := by exact prefixLift 285821
  have htrace : WordTrace (prefixWord ++ tailWord_285821) baseStart_285821 baseEnd_285821 := by
    simpa [prefixWord, tailWord_285821, baseEnd_285821] using wordTrace_append hprefix tailTrace_285821
  have hstable : (prefixWord ++ tailWord_285821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285821).length < 2 ^ (prefixWord ++ tailWord_285821).sum := by decide
  have hdescent : baseEnd_285821 < baseStart_285821 := by decide
  rcases family_descends (prefixWord ++ tailWord_285821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285847 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_285847 : Nat := 118140960795 + 285847 * 2 ^ 59
def prefixEnd_285847 : Nat := 4983230072969 + 3 ^ 40 * 285847 * 2
def baseEnd_285847 : Nat := 97851269763898903998613

theorem tailTrace_285847 : CollatzResearch.WordTrace tailWord_285847 prefixEnd_285847 97851269763898903998613 := by
  unfold tailWord_285847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425696595432612626047795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6950464396955075084031863 10425696595432612626047795)
  ·
    refine ⟨15638544893148918939071693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10425696595432612626047795 15638544893148918939071693)
    ·
      refine ⟨5864454334930844602151885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15638544893148918939071693 5864454334930844602151885)
      ·
        refine ⟨2199170375599066725806957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5864454334930844602151885 2199170375599066725806957)
        ·
          refine ⟨824688890849650022177609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2199170375599066725806957 824688890849650022177609)
          ·
            refine ⟨618516668137237516633207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 824688890849650022177609 618516668137237516633207)
            ·
              refine ⟨927775002205856274949811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618516668137237516633207 927775002205856274949811)
              ·
                refine ⟨1391662503308784412424717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927775002205856274949811 1391662503308784412424717)
                ·
                  refine ⟨521873438740794154659269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1391662503308784412424717 521873438740794154659269)
                  ·
                    refine ⟨97851269763898903998613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521873438740794154659269 97851269763898903998613)
                    ·
                      rfl

theorem cell22_285847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_285847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285847 prefixEnd_285847 := by exact prefixLift 285847
  have htrace : WordTrace (prefixWord ++ tailWord_285847) baseStart_285847 baseEnd_285847 := by
    simpa [prefixWord, tailWord_285847, baseEnd_285847] using wordTrace_append hprefix tailTrace_285847
  have hstable : (prefixWord ++ tailWord_285847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285847).length < 2 ^ (prefixWord ++ tailWord_285847).sum := by decide
  have hdescent : baseEnd_285847 < baseStart_285847 := by decide
  rcases family_descends (prefixWord ++ tailWord_285847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285909 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_285909 : Nat := 118140960795 + 285909 * 2 ^ 59
def prefixEnd_285909 : Nat := 4983230072969 + 3 ^ 40 * 285909 * 2
def baseEnd_285909 : Nat := 97872493630951408948423

theorem tailTrace_285909 : CollatzResearch.WordTrace tailWord_285909 prefixEnd_285909 97872493630951408948423 := by
  unfold tailWord_285909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427957921207997214804781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6951971947471998143203187 10427957921207997214804781)
  ·
    refine ⟨3910484220452998955551793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10427957921207997214804781 3910484220452998955551793)
    ·
      refine ⟨2932863165339749216663845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3910484220452998955551793 2932863165339749216663845)
      ·
        refine ⟨549911843501202978124471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2932863165339749216663845 549911843501202978124471)
        ·
          refine ⟨824867765251804467186707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549911843501202978124471 824867765251804467186707)
          ·
            refine ⟨1237301647877706700780061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824867765251804467186707 1237301647877706700780061)
            ·
              refine ⟨463988117954140012792523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1237301647877706700780061 463988117954140012792523)
              ·
                refine ⟨695982176931210019188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463988117954140012792523 695982176931210019188785)
                ·
                  refine ⟨521986632698407514391589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695982176931210019188785 521986632698407514391589)
                  ·
                    refine ⟨97872493630951408948423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521986632698407514391589 97872493630951408948423)
                    ·
                      rfl

theorem cell22_285909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_285909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285909 prefixEnd_285909 := by exact prefixLift 285909
  have htrace : WordTrace (prefixWord ++ tailWord_285909) baseStart_285909 baseEnd_285909 := by
    simpa [prefixWord, tailWord_285909, baseEnd_285909] using wordTrace_append hprefix tailTrace_285909
  have hstable : (prefixWord ++ tailWord_285909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285909).length < 2 ^ (prefixWord ++ tailWord_285909).sum := by decide
  have hdescent : baseEnd_285909 < baseStart_285909 := by decide
  rcases family_descends (prefixWord ++ tailWord_285909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285939 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 3, 3]
def baseStart_285939 : Nat := 118140960795 + 285939 * 2 ^ 59
def prefixEnd_285939 : Nat := 4983230072969 + 3 ^ 40 * 285939 * 2
def baseEnd_285939 : Nat := 97882763244041330698331

theorem tailTrace_285939 : CollatzResearch.WordTrace tailWord_285939 prefixEnd_285939 97882763244041330698331 := by
  unfold tailWord_285939
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429052111099312338396871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6952701407399541558931247 10429052111099312338396871)
  ·
    refine ⟨15643578166648968507595307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10429052111099312338396871 15643578166648968507595307)
    ·
      refine ⟨23465367249973452761392961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15643578166648968507595307 23465367249973452761392961)
      ·
        refine ⟨17599025437480089571044721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23465367249973452761392961 17599025437480089571044721)
        ·
          refine ⟨13199269078110067178283541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17599025437480089571044721 13199269078110067178283541)
          ·
            refine ⟨618715738036409398982041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13199269078110067178283541 618715738036409398982041)
            ·
              refine ⟨464036803527307049236531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618715738036409398982041 464036803527307049236531)
              ·
                refine ⟨696055205290960573854797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464036803527307049236531 696055205290960573854797)
                ·
                  refine ⟨261020701984110215195549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696055205290960573854797 261020701984110215195549)
                  ·
                    refine ⟨97882763244041330698331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261020701984110215195549 97882763244041330698331)
                    ·
                      rfl

theorem cell22_285939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].length) (baseStart_285939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_285939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_285939 prefixEnd_285939 := by exact prefixLift 285939
  have htrace : WordTrace (prefixWord ++ tailWord_285939) baseStart_285939 baseEnd_285939 := by
    simpa [prefixWord, tailWord_285939, baseEnd_285939] using wordTrace_append hprefix tailTrace_285939
  have hstable : (prefixWord ++ tailWord_285939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285939).length < 2 ^ (prefixWord ++ tailWord_285939).sum := by decide
  have hdescent : baseEnd_285939 < baseStart_285939 := by decide
  rcases family_descends (prefixWord ++ tailWord_285939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286048 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_286048 : Nat := 118140960795 + 286048 * 2 ^ 59
def prefixEnd_286048 : Nat := 4983230072969 + 3 ^ 40 * 286048 * 2
def baseEnd_286048 : Nat := 32640025390533793240999

theorem tailTrace_286048 : CollatzResearch.WordTrace tailWord_286048 prefixEnd_286048 32640025390533793240999 := by
  unfold tailWord_286048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216513833852211977057399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6955351778469615969409865 5216513833852211977057399)
  ·
    refine ⟨7824770750778317965586099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5216513833852211977057399 7824770750778317965586099)
    ·
      refine ⟨11737156126167476948379149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7824770750778317965586099 11737156126167476948379149)
      ·
        refine ⟨4401433547312803855642181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11737156126167476948379149 4401433547312803855642181)
        ·
          refine ⟨825268790121150722932909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4401433547312803855642181 825268790121150722932909)
          ·
            refine ⟨309475796295431521099841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 825268790121150722932909 309475796295431521099841)
            ·
              refine ⟨232106847221573640824881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309475796295431521099841 232106847221573640824881)
              ·
                refine ⟨174080135416180230618661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232106847221573640824881 174080135416180230618661)
                ·
                  refine ⟨32640025390533793240999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174080135416180230618661 32640025390533793240999)
                  ·
                    rfl

theorem cell22_286048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_286048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286048 prefixEnd_286048 := by exact prefixLift 286048
  have htrace : WordTrace (prefixWord ++ tailWord_286048) baseStart_286048 baseEnd_286048 := by
    simpa [prefixWord, tailWord_286048, baseEnd_286048] using wordTrace_append hprefix tailTrace_286048
  have hstable : (prefixWord ++ tailWord_286048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286048).length < 2 ^ (prefixWord ++ tailWord_286048).sum := by decide
  have hdescent : baseEnd_286048 < baseStart_286048 := by decide
  rcases family_descends (prefixWord ++ tailWord_286048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286074 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_286074 : Nat := 118140960795 + 286074 * 2 ^ 59
def prefixEnd_286074 : Nat := 4983230072969 + 3 ^ 40 * 286074 * 2
def baseEnd_286074 : Nat := 97928976502945978572917

theorem tailTrace_286074 : CollatzResearch.WordTrace tailWord_286074 prefixEnd_286074 97928976502945978572917 := by
  unfold tailWord_286074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608493991402557598640319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6955983977073486929707517 2608493991402557598640319)
  ·
    refine ⟨3912740987103836397960479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2608493991402557598640319 3912740987103836397960479)
    ·
      refine ⟨5869111480655754596940719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912740987103836397960479 5869111480655754596940719)
      ·
        refine ⟨8803667220983631895411079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869111480655754596940719 8803667220983631895411079)
        ·
          refine ⟨13205500831475447843116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8803667220983631895411079 13205500831475447843116619)
          ·
            refine ⟨19808251247213171764674929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13205500831475447843116619 19808251247213171764674929)
            ·
              refine ⟨14856188435409878823506197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19808251247213171764674929 14856188435409878823506197)
              ·
                refine ⟨696383832909838069851853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14856188435409878823506197 696383832909838069851853)
                ·
                  refine ⟨261143937341189276194445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696383832909838069851853 261143937341189276194445)
                  ·
                    refine ⟨97928976502945978572917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261143937341189276194445 97928976502945978572917)
                    ·
                      rfl

theorem cell22_286074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_286074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286074 prefixEnd_286074 := by exact prefixLift 286074
  have htrace : WordTrace (prefixWord ++ tailWord_286074) baseStart_286074 baseEnd_286074 := by
    simpa [prefixWord, tailWord_286074, baseEnd_286074] using wordTrace_append hprefix tailTrace_286074
  have hstable : (prefixWord ++ tailWord_286074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286074).length < 2 ^ (prefixWord ++ tailWord_286074).sum := by decide
  have hdescent : baseEnd_286074 < baseStart_286074 := by decide
  rcases family_descends (prefixWord ++ tailWord_286074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286078 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_286078 : Nat := 118140960795 + 286078 * 2 ^ 59
def prefixEnd_286078 : Nat := 4983230072969 + 3 ^ 40 * 286078 * 2
def baseEnd_286078 : Nat := 97930345784691301472905

theorem tailTrace_286078 : CollatzResearch.WordTrace tailWord_286078 prefixEnd_286078 97930345784691301472905 := by
  unfold tailWord_286078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304265232199467384713361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6956081238397159385137925 1304265232199467384713361)
  ·
    refine ⟨978198924149600538535021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1304265232199467384713361 978198924149600538535021)
    ·
      refine ⟨366824596556100201950633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 978198924149600538535021 366824596556100201950633)
      ·
        refine ⟨275118447417075151462975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366824596556100201950633 275118447417075151462975)
        ·
          refine ⟨412677671125612727194463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275118447417075151462975 412677671125612727194463)
          ·
            refine ⟨619016506688419090791695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412677671125612727194463 619016506688419090791695)
            ·
              refine ⟨928524760032628636187543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619016506688419090791695 928524760032628636187543)
              ·
                refine ⟨1392787140048942954281315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928524760032628636187543 1392787140048942954281315)
                ·
                  refine ⟨2089180710073414431421973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392787140048942954281315 2089180710073414431421973)
                  ·
                    refine ⟨97930345784691301472905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2089180710073414431421973 97930345784691301472905)
                    ·
                      rfl

theorem cell22_286078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_286078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286078 prefixEnd_286078 := by exact prefixLift 286078
  have htrace : WordTrace (prefixWord ++ tailWord_286078) baseStart_286078 baseEnd_286078 := by
    simpa [prefixWord, tailWord_286078, baseEnd_286078] using wordTrace_append hprefix tailTrace_286078
  have hstable : (prefixWord ++ tailWord_286078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286078).length < 2 ^ (prefixWord ++ tailWord_286078).sum := by decide
  have hdescent : baseEnd_286078 < baseStart_286078 := by decide
  rcases family_descends (prefixWord ++ tailWord_286078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286117 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_286117 : Nat := 118140960795 + 286117 * 2 ^ 59
def prefixEnd_286117 : Nat := 4983230072969 + 3 ^ 40 * 286117 * 2
def baseEnd_286117 : Nat := 97943696281708199747785

theorem tailTrace_286117 : CollatzResearch.WordTrace tailWord_286117 prefixEnd_286117 97943696281708199747785 := by
  unfold tailWord_286117
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435544304454448738376605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6957029536302965825584403 10435544304454448738376605)
  ·
    refine ⟨3913329114170418276891227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10435544304454448738376605 3913329114170418276891227)
    ·
      refine ⟨5869993671255627415336841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3913329114170418276891227 5869993671255627415336841)
      ·
        refine ⟨4402495253441720561502631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5869993671255627415336841 4402495253441720561502631)
        ·
          refine ⟨6603742880162580842253947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402495253441720561502631 6603742880162580842253947)
          ·
            refine ⟨9905614320243871263380921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6603742880162580842253947 9905614320243871263380921)
            ·
              refine ⟨7429210740182903447535691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9905614320243871263380921 7429210740182903447535691)
              ·
                refine ⟨11143816110274355171303537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429210740182903447535691 11143816110274355171303537)
                ·
                  refine ⟨8357862082705766378477653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11143816110274355171303537 8357862082705766378477653)
                  ·
                    refine ⟨97943696281708199747785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8357862082705766378477653 97943696281708199747785)
                    ·
                      rfl

theorem cell22_286117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_286117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286117 prefixEnd_286117 := by exact prefixLift 286117
  have htrace : WordTrace (prefixWord ++ tailWord_286117) baseStart_286117 baseEnd_286117 := by
    simpa [prefixWord, tailWord_286117, baseEnd_286117] using wordTrace_append hprefix tailTrace_286117
  have hstable : (prefixWord ++ tailWord_286117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286117).length < 2 ^ (prefixWord ++ tailWord_286117).sum := by decide
  have hdescent : baseEnd_286117 < baseStart_286117 := by decide
  rcases family_descends (prefixWord ++ tailWord_286117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286119 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_286119 : Nat := 118140960795 + 286119 * 2 ^ 59
def prefixEnd_286119 : Nat := 4983230072969 + 3 ^ 40 * 286119 * 2
def baseEnd_286119 : Nat := 97944380922580861197779

theorem tailTrace_286119 : CollatzResearch.WordTrace tailWord_286119 prefixEnd_286119 97944380922580861197779 := by
  unfold tailWord_286119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435617250447203079949411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6957078166964802053299607 10435617250447203079949411)
  ·
    refine ⟨15653425875670804619924117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10435617250447203079949411 15653425875670804619924117)
    ·
      refine ⟨733754337922068966558943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15653425875670804619924117 733754337922068966558943)
      ·
        refine ⟨1100631506883103449838415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733754337922068966558943 1100631506883103449838415)
        ·
          refine ⟨1650947260324655174757623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100631506883103449838415 1650947260324655174757623)
          ·
            refine ⟨2476420890486982762136435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650947260324655174757623 2476420890486982762136435)
            ·
              refine ⟨3714631335730474143204653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476420890486982762136435 3714631335730474143204653)
              ·
                refine ⟨1392986750898927803701745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714631335730474143204653 1392986750898927803701745)
                ·
                  refine ⟨1044740063174195852776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1392986750898927803701745 1044740063174195852776309)
                  ·
                    refine ⟨97944380922580861197779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1044740063174195852776309 97944380922580861197779)
                    ·
                      rfl

theorem cell22_286119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_286119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286119 prefixEnd_286119 := by exact prefixLift 286119
  have htrace : WordTrace (prefixWord ++ tailWord_286119) baseStart_286119 baseEnd_286119 := by
    simpa [prefixWord, tailWord_286119, baseEnd_286119] using wordTrace_append hprefix tailTrace_286119
  have hstable : (prefixWord ++ tailWord_286119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286119).length < 2 ^ (prefixWord ++ tailWord_286119).sum := by decide
  have hdescent : baseEnd_286119 < baseStart_286119 := by decide
  rcases family_descends (prefixWord ++ tailWord_286119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286243 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 3, 3]
def baseStart_286243 : Nat := 118140960795 + 286243 * 2 ^ 59
def prefixEnd_286243 : Nat := 4983230072969 + 3 ^ 40 * 286243 * 2
def baseEnd_286243 : Nat := 97986828656685871097399

theorem tailTrace_286243 : CollatzResearch.WordTrace tailWord_286243 prefixEnd_286243 97986828656685871097399 := by
  unfold tailWord_286243
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440139901997972257463383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6960093267998648171642255 10440139901997972257463383)
  ·
    refine ⟨15660209852996958386195075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10440139901997972257463383 15660209852996958386195075)
    ·
      refine ⟨23490314779495437579292613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15660209852996958386195075 23490314779495437579292613)
      ·
        refine ⟨4404434021155394546117365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23490314779495437579292613 4404434021155394546117365)
        ·
          refine ⟨412915689483318238698503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4404434021155394546117365 412915689483318238698503)
          ·
            refine ⟨619373534224977358047755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412915689483318238698503 619373534224977358047755)
            ·
              refine ⟨929060301337466037071633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619373534224977358047755 929060301337466037071633)
              ·
                refine ⟨696795226003099527803725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929060301337466037071633 696795226003099527803725)
                ·
                  refine ⟨261298209751162322926397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696795226003099527803725 261298209751162322926397)
                  ·
                    refine ⟨97986828656685871097399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261298209751162322926397 97986828656685871097399)
                    ·
                      rfl

theorem cell22_286243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].length) (baseStart_286243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286243 prefixEnd_286243 := by exact prefixLift 286243
  have htrace : WordTrace (prefixWord ++ tailWord_286243) baseStart_286243 baseEnd_286243 := by
    simpa [prefixWord, tailWord_286243, baseEnd_286243] using wordTrace_append hprefix tailTrace_286243
  have hstable : (prefixWord ++ tailWord_286243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286243).length < 2 ^ (prefixWord ++ tailWord_286243).sum := by decide
  have hdescent : baseEnd_286243 < baseStart_286243 := by decide
  rcases family_descends (prefixWord ++ tailWord_286243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286331 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_286331 : Nat := 118140960795 + 286331 * 2 ^ 59
def prefixEnd_286331 : Nat := 4983230072969 + 3 ^ 40 * 286331 * 2
def baseEnd_286331 : Nat := 98016952855082974897129

theorem tailTrace_286331 : CollatzResearch.WordTrace tailWord_286331 prefixEnd_286331 98016952855082974897129 := by
  unfold tailWord_286331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443349525679163286666847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6962233017119442191111231 10443349525679163286666847)
  ·
    refine ⟨15665024288518744930000271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443349525679163286666847 15665024288518744930000271)
    ·
      refine ⟨23497536432778117395000407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665024288518744930000271 23497536432778117395000407)
      ·
        refine ⟨35246304649167176092500611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23497536432778117395000407 35246304649167176092500611)
        ·
          refine ⟨52869456973750764138750917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35246304649167176092500611 52869456973750764138750917)
          ·
            refine ⟨9913023182578268276015797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52869456973750764138750917 9913023182578268276015797)
            ·
              refine ⟨929345923366712650876481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9913023182578268276015797 929345923366712650876481)
              ·
                refine ⟨697009442525034488157361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929345923366712650876481 697009442525034488157361)
                ·
                  refine ⟨522757081893775866118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697009442525034488157361 522757081893775866118021)
                  ·
                    refine ⟨98016952855082974897129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522757081893775866118021 98016952855082974897129)
                    ·
                      rfl

theorem cell22_286331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_286331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286331 prefixEnd_286331 := by exact prefixLift 286331
  have htrace : WordTrace (prefixWord ++ tailWord_286331) baseStart_286331 baseEnd_286331 := by
    simpa [prefixWord, tailWord_286331, baseEnd_286331] using wordTrace_append hprefix tailTrace_286331
  have hstable : (prefixWord ++ tailWord_286331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286331).length < 2 ^ (prefixWord ++ tailWord_286331).sum := by decide
  have hdescent : baseEnd_286331 < baseStart_286331 := by decide
  rcases family_descends (prefixWord ++ tailWord_286331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286333 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_286333 : Nat := 118140960795 + 286333 * 2 ^ 59
def prefixEnd_286333 : Nat := 4983230072969 + 3 ^ 40 * 286333 * 2
def baseEnd_286333 : Nat := 98017637495955636347123

theorem tailTrace_286333 : CollatzResearch.WordTrace tailWord_286333 prefixEnd_286333 98017637495955636347123 := by
  unfold tailWord_286333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443422471671917628239653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6962281647781278418826435 10443422471671917628239653)
  ·
    refine ⟨1958141713438484555294935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10443422471671917628239653 1958141713438484555294935)
    ·
      refine ⟨2937212570157726832942403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958141713438484555294935 2937212570157726832942403)
      ·
        refine ⟨4405818855236590249413605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937212570157726832942403 4405818855236590249413605)
        ·
          refine ⟨826091035356860671765051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4405818855236590249413605 826091035356860671765051)
          ·
            refine ⟨1239136553035291007647577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826091035356860671765051 1239136553035291007647577)
            ·
              refine ⟨929352414776468255735683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239136553035291007647577 929352414776468255735683)
              ·
                refine ⟨1394028622164702383603525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929352414776468255735683 1394028622164702383603525)
                ·
                  refine ⟨261380366655881696925661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394028622164702383603525 261380366655881696925661)
                  ·
                    refine ⟨98017637495955636347123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261380366655881696925661 98017637495955636347123)
                    ·
                      rfl

theorem cell22_286333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_286333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286333 prefixEnd_286333 := by exact prefixLift 286333
  have htrace : WordTrace (prefixWord ++ tailWord_286333) baseStart_286333 baseEnd_286333 := by
    simpa [prefixWord, tailWord_286333, baseEnd_286333] using wordTrace_append hprefix tailTrace_286333
  have hstable : (prefixWord ++ tailWord_286333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286333).length < 2 ^ (prefixWord ++ tailWord_286333).sum := by decide
  have hdescent : baseEnd_286333 < baseStart_286333 := by decide
  rcases family_descends (prefixWord ++ tailWord_286333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286346 : List Nat := [3, 1, 2, 3, 2, 1, 1, 9]
def baseStart_286346 : Nat := 118140960795 + 286346 * 2 ^ 59
def prefixEnd_286346 : Nat := 4983230072969 + 3 ^ 40 * 286346 * 2
def baseEnd_286346 : Nat := 10891343073514215085787

theorem tailTrace_286346 : CollatzResearch.WordTrace tailWord_286346 prefixEnd_286346 10891343073514215085787 := by
  unfold tailWord_286346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610974155156205212115723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6962597747083213898975261 2610974155156205212115723)
  ·
    refine ⟨3916461232734307818173585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610974155156205212115723 3916461232734307818173585)
    ·
      refine ⟨2937345924550730863630189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3916461232734307818173585 2937345924550730863630189)
      ·
        refine ⟨1101504721706524073861321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2937345924550730863630189 1101504721706524073861321)
        ·
          refine ⟨826128541279893055395991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101504721706524073861321 826128541279893055395991)
          ·
            refine ⟨1239192811919839583093987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826128541279893055395991 1239192811919839583093987)
            ·
              refine ⟨1858789217879759374640981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239192811919839583093987 1858789217879759374640981)
              ·
                refine ⟨10891343073514215085787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1858789217879759374640981 10891343073514215085787)
                ·
                  rfl

theorem cell22_286346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_286346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286346 prefixEnd_286346 := by exact prefixLift 286346
  have htrace : WordTrace (prefixWord ++ tailWord_286346) baseStart_286346 baseEnd_286346 := by
    simpa [prefixWord, tailWord_286346, baseEnd_286346] using wordTrace_append hprefix tailTrace_286346
  have hstable : (prefixWord ++ tailWord_286346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286346).length < 2 ^ (prefixWord ++ tailWord_286346).sum := by decide
  have hdescent : baseEnd_286346 < baseStart_286346 := by decide
  rcases family_descends (prefixWord ++ tailWord_286346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286350 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_286350 : Nat := 118140960795 + 286350 * 2 ^ 59
def prefixEnd_286350 : Nat := 4983230072969 + 3 ^ 40 * 286350 * 2
def baseEnd_286350 : Nat := 98023456943373258672071

theorem tailTrace_286350 : CollatzResearch.WordTrace tailWord_286350 prefixEnd_286350 98023456943373258672071 := by
  unfold tailWord_286350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305505314076291191451063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6962695008406886354405669 1305505314076291191451063)
  ·
    refine ⟨1958257971114436787176595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305505314076291191451063 1958257971114436787176595)
    ·
      refine ⟨2937386956671655180764893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958257971114436787176595 2937386956671655180764893)
      ·
        refine ⟨1101520108751870692786835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2937386956671655180764893 1101520108751870692786835)
        ·
          refine ⟨1652280163127806039180253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101520108751870692786835 1652280163127806039180253)
          ·
            refine ⟨619605061172927264692595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1652280163127806039180253 619605061172927264692595)
            ·
              refine ⟨929407591759390897038893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619605061172927264692595 929407591759390897038893)
              ·
                refine ⟨348527846909771586389585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929407591759390897038893 348527846909771586389585)
                ·
                  refine ⟨261395885182328689792189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348527846909771586389585 261395885182328689792189)
                  ·
                    refine ⟨98023456943373258672071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261395885182328689792189 98023456943373258672071)
                    ·
                      rfl

theorem cell22_286350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_286350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286350 prefixEnd_286350 := by exact prefixLift 286350
  have htrace : WordTrace (prefixWord ++ tailWord_286350) baseStart_286350 baseEnd_286350 := by
    simpa [prefixWord, tailWord_286350, baseEnd_286350] using wordTrace_append hprefix tailTrace_286350
  have hstable : (prefixWord ++ tailWord_286350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286350).length < 2 ^ (prefixWord ++ tailWord_286350).sum := by decide
  have hdescent : baseEnd_286350 < baseStart_286350 := by decide
  rcases family_descends (prefixWord ++ tailWord_286350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286436 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_286436 : Nat := 118140960795 + 286436 * 2 ^ 59
def prefixEnd_286436 : Nat := 4983230072969 + 3 ^ 40 * 286436 * 2
def baseEnd_286436 : Nat := 32684298833632567007269

theorem tailTrace_286436 : CollatzResearch.WordTrace tailWord_286436 prefixEnd_286436 32684298833632567007269 := by
  unfold tailWord_286436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223589595149383109619581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6964786126865844146159441 5223589595149383109619581)
  ·
    refine ⟨1958846098181018666107343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5223589595149383109619581 1958846098181018666107343)
    ·
      refine ⟨2938269147271527999161015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958846098181018666107343 2938269147271527999161015)
      ·
        refine ⟨4407403720907291998741523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938269147271527999161015 4407403720907291998741523)
        ·
          refine ⟨6611105581360937998112285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407403720907291998741523 6611105581360937998112285)
          ·
            refine ⟨2479164593010351749292107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6611105581360937998112285 2479164593010351749292107)
            ·
              refine ⟨3718746889515527623938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479164593010351749292107 3718746889515527623938161)
              ·
                refine ⟨2789060167136645717953621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718746889515527623938161 2789060167136645717953621)
                ·
                  refine ⟨32684298833632567007269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2789060167136645717953621 32684298833632567007269)
                  ·
                    rfl

theorem cell22_286436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_286436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286436 prefixEnd_286436 := by exact prefixLift 286436
  have htrace : WordTrace (prefixWord ++ tailWord_286436) baseStart_286436 baseEnd_286436 := by
    simpa [prefixWord, tailWord_286436, baseEnd_286436] using wordTrace_append hprefix tailTrace_286436
  have hstable : (prefixWord ++ tailWord_286436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286436).length < 2 ^ (prefixWord ++ tailWord_286436).sum := by decide
  have hdescent : baseEnd_286436 < baseStart_286436 := by decide
  rcases family_descends (prefixWord ++ tailWord_286436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286451 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_286451 : Nat := 118140960795 + 286451 * 2 ^ 59
def prefixEnd_286451 : Nat := 4983230072969 + 3 ^ 40 * 286451 * 2
def baseEnd_286451 : Nat := 98058031307442661896761

theorem tailTrace_286451 : CollatzResearch.WordTrace tailWord_286451 prefixEnd_286451 98058031307442661896761 := by
  unfold tailWord_286451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447726285244423781035207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6965150856829615854023471 10447726285244423781035207)
  ·
    refine ⟨15671589427866635671552811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10447726285244423781035207 15671589427866635671552811)
    ·
      refine ⟨23507384141799953507329217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15671589427866635671552811 23507384141799953507329217)
      ·
        refine ⟨17630538106349965130496913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23507384141799953507329217 17630538106349965130496913)
        ·
          refine ⟨13222903579762473847872685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17630538106349965130496913 13222903579762473847872685)
          ·
            refine ⟨4958588842410927692952257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13222903579762473847872685 4958588842410927692952257)
            ·
              refine ⟨3718941631808195769714193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958588842410927692952257 3718941631808195769714193)
              ·
                refine ⟨2789206223856146827285645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718941631808195769714193 2789206223856146827285645)
                ·
                  refine ⟨1045952333946055060232117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2789206223856146827285645 1045952333946055060232117)
                  ·
                    refine ⟨98058031307442661896761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1045952333946055060232117 98058031307442661896761)
                    ·
                      rfl

theorem cell22_286451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_286451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286451 prefixEnd_286451 := by exact prefixLift 286451
  have htrace : WordTrace (prefixWord ++ tailWord_286451) baseStart_286451 baseEnd_286451 := by
    simpa [prefixWord, tailWord_286451, baseEnd_286451] using wordTrace_append hprefix tailTrace_286451
  have hstable : (prefixWord ++ tailWord_286451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286451).length < 2 ^ (prefixWord ++ tailWord_286451).sum := by decide
  have hdescent : baseEnd_286451 < baseStart_286451 := by decide
  rcases family_descends (prefixWord ++ tailWord_286451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286487 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 4]
def baseStart_286487 : Nat := 118140960795 + 286487 * 2 ^ 59
def prefixEnd_286487 : Nat := 4983230072969 + 3 ^ 40 * 286487 * 2
def baseEnd_286487 : Nat := 32690118281050189332217

theorem tailTrace_286487 : CollatzResearch.WordTrace tailWord_286487 prefixEnd_286487 32690118281050189332217 := by
  unfold tailWord_286487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449039313114001929345715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6966026208742667952897143 10449039313114001929345715)
  ·
    refine ⟨15673558969671002894018573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449039313114001929345715 15673558969671002894018573)
    ·
      refine ⟨5877584613626626085256965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15673558969671002894018573 5877584613626626085256965)
      ·
        refine ⟨1102047115054992390985681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5877584613626626085256965 1102047115054992390985681)
        ·
          refine ⟨826535336291244293239261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102047115054992390985681 826535336291244293239261)
          ·
            refine ⟨309950751109216609964723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 826535336291244293239261 309950751109216609964723)
            ·
              refine ⟨464926126663824914947085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309950751109216609964723 464926126663824914947085)
              ·
                refine ⟨174347297498934343105157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464926126663824914947085 174347297498934343105157)
                ·
                  refine ⟨32690118281050189332217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174347297498934343105157 32690118281050189332217)
                  ·
                    rfl

theorem cell22_286487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 4].length) (baseStart_286487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286487 prefixEnd_286487 := by exact prefixLift 286487
  have htrace : WordTrace (prefixWord ++ tailWord_286487) baseStart_286487 baseEnd_286487 := by
    simpa [prefixWord, tailWord_286487, baseEnd_286487] using wordTrace_append hprefix tailTrace_286487
  have hstable : (prefixWord ++ tailWord_286487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286487).length < 2 ^ (prefixWord ++ tailWord_286487).sum := by decide
  have hdescent : baseEnd_286487 < baseStart_286487 := by decide
  rcases family_descends (prefixWord ++ tailWord_286487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286500 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_286500 : Nat := 118140960795 + 286500 * 2 ^ 59
def prefixEnd_286500 : Nat := 4983230072969 + 3 ^ 40 * 286500 * 2
def baseEnd_286500 : Nat := 98074805008822867421611

theorem tailTrace_286500 : CollatzResearch.WordTrace tailWord_286500 prefixEnd_286500 98074805008822867421611 := by
  unfold tailWord_286500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224756731033452574784477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6966342308044603433045969 5224756731033452574784477)
  ·
    refine ⟨1959283774137544715544179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5224756731033452574784477 1959283774137544715544179)
    ·
      refine ⟨2938925661206317073316269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959283774137544715544179 2938925661206317073316269)
      ·
        refine ⟨1102097122952368902493601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2938925661206317073316269 1102097122952368902493601)
        ·
          refine ⟨826572842214276676870201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102097122952368902493601 826572842214276676870201)
          ·
            refine ⟨619929631660707507652651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826572842214276676870201 619929631660707507652651)
            ·
              refine ⟨929894447491061261478977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619929631660707507652651 929894447491061261478977)
              ·
                refine ⟨697420835618295946109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929894447491061261478977 697420835618295946109233)
                ·
                  refine ⟨523065626713721959581925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697420835618295946109233 523065626713721959581925)
                  ·
                    refine ⟨98074805008822867421611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523065626713721959581925 98074805008822867421611)
                    ·
                      rfl

theorem cell22_286500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_286500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286500 prefixEnd_286500 := by exact prefixLift 286500
  have htrace : WordTrace (prefixWord ++ tailWord_286500) baseStart_286500 baseEnd_286500 := by
    simpa [prefixWord, tailWord_286500, baseEnd_286500] using wordTrace_append hprefix tailTrace_286500
  have hstable : (prefixWord ++ tailWord_286500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286500).length < 2 ^ (prefixWord ++ tailWord_286500).sum := by decide
  have hdescent : baseEnd_286500 < baseStart_286500 := by decide
  rcases family_descends (prefixWord ++ tailWord_286500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286511 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_286511 : Nat := 118140960795 + 286511 * 2 ^ 59
def prefixEnd_286511 : Nat := 4983230072969 + 3 ^ 40 * 286511 * 2
def baseEnd_286511 : Nat := 98078570533622505396577

theorem tailTrace_286511 : CollatzResearch.WordTrace tailWord_286511 prefixEnd_286511 98078570533622505396577 := by
  unfold tailWord_286511
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449914665027054028219387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6966609776684702685479591 10449914665027054028219387)
  ·
    refine ⟨15674871997540581042329081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449914665027054028219387 15674871997540581042329081)
    ·
      refine ⟨11756153998155435781746811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15674871997540581042329081 11756153998155435781746811)
      ·
        refine ⟨17634230997233153672620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11756153998155435781746811 17634230997233153672620217)
        ·
          refine ⟨13225673247924865254465163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17634230997233153672620217 13225673247924865254465163)
          ·
            refine ⟨19838509871887297881697745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13225673247924865254465163 19838509871887297881697745)
            ·
              refine ⟨14878882403915473411273309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19838509871887297881697745 14878882403915473411273309)
              ·
                refine ⟨5579580901468302529227491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14878882403915473411273309 5579580901468302529227491)
                ·
                  refine ⟨8369371352202453793841237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579580901468302529227491 8369371352202453793841237)
                  ·
                    refine ⟨98078570533622505396577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8369371352202453793841237 98078570533622505396577)
                    ·
                      rfl

theorem cell22_286511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_286511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286511 prefixEnd_286511 := by exact prefixLift 286511
  have htrace : WordTrace (prefixWord ++ tailWord_286511) baseStart_286511 baseEnd_286511 := by
    simpa [prefixWord, tailWord_286511, baseEnd_286511] using wordTrace_append hprefix tailTrace_286511
  have hstable : (prefixWord ++ tailWord_286511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286511).length < 2 ^ (prefixWord ++ tailWord_286511).sum := by decide
  have hdescent : baseEnd_286511 < baseStart_286511 := by decide
  rcases family_descends (prefixWord ++ tailWord_286511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286534 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_286534 : Nat := 118140960795 + 286534 * 2 ^ 59
def prefixEnd_286534 : Nat := 4983230072969 + 3 ^ 40 * 286534 * 2
def baseEnd_286534 : Nat := 98086443903658112071507

theorem tailTrace_286534 : CollatzResearch.WordTrace tailWord_286534 prefixEnd_286534 98086443903658112071507 := by
  unfold tailWord_286534
  simp only [CollatzResearch.WordTrace]
  refine ⟨326586048248241529884583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6967169029295819304204437 326586048248241529884583)
  ·
    refine ⟨489879072372362294826875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326586048248241529884583 489879072372362294826875)
    ·
      refine ⟨734818608558543442240313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489879072372362294826875 734818608558543442240313)
      ·
        refine ⟨551113956418907581680235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734818608558543442240313 551113956418907581680235)
        ·
          refine ⟨826670934628361372520353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551113956418907581680235 826670934628361372520353)
          ·
            refine ⟨620003200971271029390265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826670934628361372520353 620003200971271029390265)
            ·
              refine ⟨465002400728453272042699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620003200971271029390265 465002400728453272042699)
              ·
                refine ⟨697503601092679908064049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465002400728453272042699 697503601092679908064049)
                ·
                  refine ⟨523127700819509931048037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697503601092679908064049 523127700819509931048037)
                  ·
                    refine ⟨98086443903658112071507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523127700819509931048037 98086443903658112071507)
                    ·
                      rfl

theorem cell22_286534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_286534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286534 prefixEnd_286534 := by exact prefixLift 286534
  have htrace : WordTrace (prefixWord ++ tailWord_286534) baseStart_286534 baseEnd_286534 := by
    simpa [prefixWord, tailWord_286534, baseEnd_286534] using wordTrace_append hprefix tailTrace_286534
  have hstable : (prefixWord ++ tailWord_286534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286534).length < 2 ^ (prefixWord ++ tailWord_286534).sum := by decide
  have hdescent : baseEnd_286534 < baseStart_286534 := by decide
  rcases family_descends (prefixWord ++ tailWord_286534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286560 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_286560 : Nat := 118140960795 + 286560 * 2 ^ 59
def prefixEnd_286560 : Nat := 4983230072969 + 3 ^ 40 * 286560 * 2
def baseEnd_286560 : Nat := 32698448078334236973809

theorem tailTrace_286560 : CollatzResearch.WordTrace tailWord_286560 prefixEnd_286560 32698448078334236973809 := by
  unfold tailWord_286560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225850920924767698376567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6967801227899690264502089 5225850920924767698376567)
  ·
    refine ⟨7838776381387151547564851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225850920924767698376567 7838776381387151547564851)
    ·
      refine ⟨11758164572080727321347277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7838776381387151547564851 11758164572080727321347277)
      ·
        refine ⟨4409311714530272745505229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11758164572080727321347277 4409311714530272745505229)
        ·
          refine ⟨1653491892948852279564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4409311714530272745505229 1653491892948852279564461)
          ·
            refine ⟨620059459855819604836673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1653491892948852279564461 620059459855819604836673)
            ·
              refine ⟨465044594891864703627505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620059459855819604836673 465044594891864703627505)
              ·
                refine ⟨348783446168898527720629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465044594891864703627505 348783446168898527720629)
                ·
                  refine ⟨32698448078334236973809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348783446168898527720629 32698448078334236973809)
                  ·
                    rfl

theorem cell22_286560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_286560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286560 prefixEnd_286560 := by exact prefixLift 286560
  have htrace : WordTrace (prefixWord ++ tailWord_286560) baseStart_286560 baseEnd_286560 := by
    simpa [prefixWord, tailWord_286560, baseEnd_286560] using wordTrace_append hprefix tailTrace_286560
  have hstable : (prefixWord ++ tailWord_286560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286560).length < 2 ^ (prefixWord ++ tailWord_286560).sum := by decide
  have hdescent : baseEnd_286560 < baseStart_286560 := by decide
  rcases family_descends (prefixWord ++ tailWord_286560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286564 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_286564 : Nat := 118140960795 + 286564 * 2 ^ 59
def prefixEnd_286564 : Nat := 4983230072969 + 3 ^ 40 * 286564 * 2
def baseEnd_286564 : Nat := 98096713516748033821415

theorem tailTrace_286564 : CollatzResearch.WordTrace tailWord_286564 prefixEnd_286564 98096713516748033821415 := by
  unfold tailWord_286564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225923866917522039949373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6967898489223362719932497 5225923866917522039949373)
  ·
    refine ⟨1959721450094070764981015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5225923866917522039949373 1959721450094070764981015)
    ·
      refine ⟨2939582175141106147471523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959721450094070764981015 2939582175141106147471523)
      ·
        refine ⟨4409373262711659221207285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939582175141106147471523 4409373262711659221207285)
        ·
          refine ⟨413378743379218051988183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4409373262711659221207285 413378743379218051988183)
          ·
            refine ⟨620068115068827077982275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413378743379218051988183 620068115068827077982275)
            ·
              refine ⟨930102172603240616973413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620068115068827077982275 930102172603240616973413)
              ·
                refine ⟨174394157363107615682515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 930102172603240616973413 174394157363107615682515)
                ·
                  refine ⟨261591236044661423523773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174394157363107615682515 261591236044661423523773)
                  ·
                    refine ⟨98096713516748033821415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261591236044661423523773 98096713516748033821415)
                    ·
                      rfl

theorem cell22_286564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_286564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286564 prefixEnd_286564 := by exact prefixLift 286564
  have htrace : WordTrace (prefixWord ++ tailWord_286564) baseStart_286564 baseEnd_286564 := by
    simpa [prefixWord, tailWord_286564, baseEnd_286564] using wordTrace_append hprefix tailTrace_286564
  have hstable : (prefixWord ++ tailWord_286564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286564).length < 2 ^ (prefixWord ++ tailWord_286564).sum := by decide
  have hdescent : baseEnd_286564 < baseStart_286564 := by decide
  rcases family_descends (prefixWord ++ tailWord_286564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286648 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_286648 : Nat := 118140960795 + 286648 * 2 ^ 59
def prefixEnd_286648 : Nat := 4983230072969 + 3 ^ 40 * 286648 * 2
def baseEnd_286648 : Nat := 98125468433399814721157

theorem tailTrace_286648 : CollatzResearch.WordTrace tailWord_286648 prefixEnd_286648 98125468433399814721157 := by
  unfold tailWord_286648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227455732765363212978299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6969940977020484283971065 5227455732765363212978299)
  ·
    refine ⟨7841183599148044819467449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227455732765363212978299 7841183599148044819467449)
    ·
      refine ⟨5880887699361033614600587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7841183599148044819467449 5880887699361033614600587)
      ·
        refine ⟨8821331549041550421900881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880887699361033614600587 8821331549041550421900881)
        ·
          refine ⟨6615998661781162816425661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8821331549041550421900881 6615998661781162816425661)
          ·
            refine ⟨2480999498167936056159623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6615998661781162816425661 2480999498167936056159623)
            ·
              refine ⟨3721499247251904084239435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480999498167936056159623 3721499247251904084239435)
              ·
                refine ⟨5582248870877856126359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721499247251904084239435 5582248870877856126359153)
                ·
                  refine ⟨4186686653158392094769365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582248870877856126359153 4186686653158392094769365)
                  ·
                    refine ⟨98125468433399814721157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4186686653158392094769365 98125468433399814721157)
                    ·
                      rfl

theorem cell22_286648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_286648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286648 prefixEnd_286648 := by exact prefixLift 286648
  have htrace : WordTrace (prefixWord ++ tailWord_286648) baseStart_286648 baseEnd_286648 := by
    simpa [prefixWord, tailWord_286648, baseEnd_286648] using wordTrace_append hprefix tailTrace_286648
  have hstable : (prefixWord ++ tailWord_286648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286648).length < 2 ^ (prefixWord ++ tailWord_286648).sum := by decide
  have hdescent : baseEnd_286648 < baseStart_286648 := by decide
  rcases family_descends (prefixWord ++ tailWord_286648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286663 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_286663 : Nat := 118140960795 + 286663 * 2 ^ 59
def prefixEnd_286663 : Nat := 4983230072969 + 3 ^ 40 * 286663 * 2
def baseEnd_286663 : Nat := 98130603239944775596111

theorem tailTrace_286663 : CollatzResearch.WordTrace tailWord_286663 prefixEnd_286663 98130603239944775596111 := by
  unfold tailWord_286663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10455458560476383987752643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6970305706984255991835095 10455458560476383987752643)
  ·
    refine ⟨15683187840714575981628965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10455458560476383987752643 15683187840714575981628965)
    ·
      refine ⟨2940597720133982996555431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15683187840714575981628965 2940597720133982996555431)
      ·
        refine ⟨4410896580200974494833147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940597720133982996555431 4410896580200974494833147)
        ·
          refine ⟨6616344870301461742249721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410896580200974494833147 6616344870301461742249721)
          ·
            refine ⟨4962258652726096306687291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6616344870301461742249721 4962258652726096306687291)
            ·
              refine ⟨7443387979089144460030937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962258652726096306687291 7443387979089144460030937)
              ·
                refine ⟨5582540984316858345023203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443387979089144460030937 5582540984316858345023203)
                ·
                  refine ⟨8373811476475287517534805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582540984316858345023203 8373811476475287517534805)
                  ·
                    refine ⟨98130603239944775596111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8373811476475287517534805 98130603239944775596111)
                    ·
                      rfl

theorem cell22_286663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_286663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286663 prefixEnd_286663 := by exact prefixLift 286663
  have htrace : WordTrace (prefixWord ++ tailWord_286663) baseStart_286663 baseEnd_286663 := by
    simpa [prefixWord, tailWord_286663, baseEnd_286663] using wordTrace_append hprefix tailTrace_286663
  have hstable : (prefixWord ++ tailWord_286663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286663).length < 2 ^ (prefixWord ++ tailWord_286663).sum := by decide
  have hdescent : baseEnd_286663 < baseStart_286663 := by decide
  rcases family_descends (prefixWord ++ tailWord_286663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286776 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_286776 : Nat := 118140960795 + 286776 * 2 ^ 59
def prefixEnd_286776 : Nat := 4983230072969 + 3 ^ 40 * 286776 * 2
def baseEnd_286776 : Nat := 98169285449250147520765

theorem tailTrace_286776 : CollatzResearch.WordTrace tailWord_286776 prefixEnd_286776 98169285449250147520765 := by
  unfold tailWord_286776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229790004533502143308091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6973053339378002857744121 5229790004533502143308091)
  ·
    refine ⟨7844685006800253214962137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229790004533502143308091 7844685006800253214962137)
    ·
      refine ⟨5883513755100189911221603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844685006800253214962137 5883513755100189911221603)
      ·
        refine ⟨8825270632650284866832405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883513755100189911221603 8825270632650284866832405)
        ·
          refine ⟨413684560905482103132769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8825270632650284866832405 413684560905482103132769)
          ·
            refine ⟨310263420679111577349577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413684560905482103132769 310263420679111577349577)
            ·
              refine ⟨232697565509333683012183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310263420679111577349577 232697565509333683012183)
              ·
                refine ⟨349046348264000524518275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232697565509333683012183 349046348264000524518275)
                ·
                  refine ⟨523569522396000786777413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349046348264000524518275 523569522396000786777413)
                  ·
                    refine ⟨98169285449250147520765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523569522396000786777413 98169285449250147520765)
                    ·
                      rfl

theorem cell22_286776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_286776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286776 prefixEnd_286776 := by exact prefixLift 286776
  have htrace : WordTrace (prefixWord ++ tailWord_286776) baseStart_286776 baseEnd_286776 := by
    simpa [prefixWord, tailWord_286776, baseEnd_286776] using wordTrace_append hprefix tailTrace_286776
  have hstable : (prefixWord ++ tailWord_286776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286776).length < 2 ^ (prefixWord ++ tailWord_286776).sum := by decide
  have hdescent : baseEnd_286776 < baseStart_286776 := by decide
  rcases family_descends (prefixWord ++ tailWord_286776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286806 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_286806 : Nat := 118140960795 + 286806 * 2 ^ 59
def prefixEnd_286806 : Nat := 4983230072969 + 3 ^ 40 * 286806 * 2
def baseEnd_286806 : Nat := 98179555062340069270673

theorem tailTrace_286806 : CollatzResearch.WordTrace tailWord_286806 prefixEnd_286806 98179555062340069270673 := by
  unfold tailWord_286806
  simp only [CollatzResearch.WordTrace]
  refine ⟨653792137434894963138017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6973782799305546273472181 653792137434894963138017)
  ·
    refine ⟨490344103076171222353513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653792137434894963138017 490344103076171222353513)
    ·
      refine ⟨367758077307128416765135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 490344103076171222353513 367758077307128416765135)
      ·
        refine ⟨551637115960692625147703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367758077307128416765135 551637115960692625147703)
        ·
          refine ⟨827455673941038937721555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551637115960692625147703 827455673941038937721555)
          ·
            refine ⟨1241183510911558406582333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827455673941038937721555 1241183510911558406582333)
            ·
              refine ⟨465443816591834402468375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241183510911558406582333 465443816591834402468375)
              ·
                refine ⟨698165724887751603702563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465443816591834402468375 698165724887751603702563)
                ·
                  refine ⟨1047248587331627405553845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698165724887751603702563 1047248587331627405553845)
                  ·
                    refine ⟨98179555062340069270673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1047248587331627405553845 98179555062340069270673)
                    ·
                      rfl

theorem cell22_286806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_286806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286806 prefixEnd_286806 := by exact prefixLift 286806
  have htrace : WordTrace (prefixWord ++ tailWord_286806) baseStart_286806 baseEnd_286806 := by
    simpa [prefixWord, tailWord_286806, baseEnd_286806] using wordTrace_append hprefix tailTrace_286806
  have hstable : (prefixWord ++ tailWord_286806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286806).length < 2 ^ (prefixWord ++ tailWord_286806).sum := by decide
  have hdescent : baseEnd_286806 < baseStart_286806 := by decide
  rcases family_descends (prefixWord ++ tailWord_286806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286860 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_286860 : Nat := 118140960795 + 286860 * 2 ^ 59
def prefixEnd_286860 : Nat := 4983230072969 + 3 ^ 40 * 286860 * 2
def baseEnd_286860 : Nat := 98198040365901928420507

theorem tailTrace_286860 : CollatzResearch.WordTrace tailWord_286860 prefixEnd_286860 98198040365901928420507 := by
  unfold tailWord_286860
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231321870381343316337017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6975095827175124421782689 5231321870381343316337017)
  ·
    refine ⟨3923491402786007487252763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5231321870381343316337017 3923491402786007487252763)
    ·
      refine ⟨5885237104179011230879145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923491402786007487252763 5885237104179011230879145)
      ·
        refine ⟨4413927828134258423159359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5885237104179011230879145 4413927828134258423159359)
        ·
          refine ⟨6620891742201387634739039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413927828134258423159359 6620891742201387634739039)
          ·
            refine ⟨9931337613302081452108559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620891742201387634739039 9931337613302081452108559)
            ·
              refine ⟨14897006419953122178162839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9931337613302081452108559 14897006419953122178162839)
              ·
                refine ⟨22345509629929683267244259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14897006419953122178162839 22345509629929683267244259)
                ·
                  refine ⟨33518264444894524900866389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22345509629929683267244259 33518264444894524900866389)
                  ·
                    refine ⟨98198040365901928420507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 33518264444894524900866389 98198040365901928420507)
                    ·
                      rfl

theorem cell22_286860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_286860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286860 prefixEnd_286860 := by exact prefixLift 286860
  have htrace : WordTrace (prefixWord ++ tailWord_286860) baseStart_286860 baseEnd_286860 := by
    simpa [prefixWord, tailWord_286860, baseEnd_286860] using wordTrace_append hprefix tailTrace_286860
  have hstable : (prefixWord ++ tailWord_286860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286860).length < 2 ^ (prefixWord ++ tailWord_286860).sum := by decide
  have hdescent : baseEnd_286860 < baseStart_286860 := by decide
  rcases family_descends (prefixWord ++ tailWord_286860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286922 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_286922 : Nat := 118140960795 + 286922 * 2 ^ 59
def prefixEnd_286922 : Nat := 4983230072969 + 3 ^ 40 * 286922 * 2
def baseEnd_286922 : Nat := 98219264232954433370317

theorem tailTrace_286922 : CollatzResearch.WordTrace tailWord_286922 prefixEnd_286922 98219264232954433370317 := by
  unfold tailWord_286922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616226266634517805357755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6976603377692047480954013 2616226266634517805357755)
  ·
    refine ⟨3924339399951776708036633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616226266634517805357755 3924339399951776708036633)
    ·
      refine ⟨2943254549963832531027475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924339399951776708036633 2943254549963832531027475)
      ·
        refine ⟨4414881824945748796541213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943254549963832531027475 4414881824945748796541213)
        ·
          refine ⟨1655580684354655798702955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4414881824945748796541213 1655580684354655798702955)
          ·
            refine ⟨2483371026531983698054433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655580684354655798702955 2483371026531983698054433)
            ·
              refine ⟨1862528269898987773540825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483371026531983698054433 1862528269898987773540825)
              ·
                refine ⟨1396896202424240830155619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862528269898987773540825 1396896202424240830155619)
                ·
                  refine ⟨2095344303636361245233429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396896202424240830155619 2095344303636361245233429)
                  ·
                    refine ⟨98219264232954433370317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2095344303636361245233429 98219264232954433370317)
                    ·
                      rfl

theorem cell22_286922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_286922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286922 prefixEnd_286922 := by exact prefixLift 286922
  have htrace : WordTrace (prefixWord ++ tailWord_286922) baseStart_286922 baseEnd_286922 := by
    simpa [prefixWord, tailWord_286922, baseEnd_286922] using wordTrace_append hprefix tailTrace_286922
  have hstable : (prefixWord ++ tailWord_286922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286922).length < 2 ^ (prefixWord ++ tailWord_286922).sum := by decide
  have hdescent : baseEnd_286922 < baseStart_286922 := by decide
  rcases family_descends (prefixWord ++ tailWord_286922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286997 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_286997 : Nat := 118140960795 + 286997 * 2 ^ 59
def prefixEnd_286997 : Nat := 4983230072969 + 3 ^ 40 * 286997 * 2
def baseEnd_286997 : Nat := 98244938265679237745087

theorem tailTrace_286997 : CollatzResearch.WordTrace tailWord_286997 prefixEnd_286997 98244938265679237745087 := by
  unfold tailWord_286997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467640541266359030411245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6978427027510906020274163 10467640541266359030411245)
  ·
    refine ⟨3925365202974884636404217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10467640541266359030411245 3925365202974884636404217)
    ·
      refine ⟨2944023902231163477303163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3925365202974884636404217 2944023902231163477303163)
      ·
        refine ⟨4416035853346745215954745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944023902231163477303163 4416035853346745215954745)
        ·
          refine ⟨3312026890010058911966059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4416035853346745215954745 3312026890010058911966059)
          ·
            refine ⟨4968040335015088367949089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312026890010058911966059 4968040335015088367949089)
            ·
              refine ⟨3726030251261316275961817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4968040335015088367949089 3726030251261316275961817)
              ·
                refine ⟨2794522688445987206971363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3726030251261316275961817 2794522688445987206971363)
                ·
                  refine ⟨4191784032668980810457045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794522688445987206971363 4191784032668980810457045)
                  ·
                    refine ⟨98244938265679237745087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4191784032668980810457045 98244938265679237745087)
                    ·
                      rfl

theorem cell22_286997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_286997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_286997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_286997 prefixEnd_286997 := by exact prefixLift 286997
  have htrace : WordTrace (prefixWord ++ tailWord_286997) baseStart_286997 baseEnd_286997 := by
    simpa [prefixWord, tailWord_286997, baseEnd_286997] using wordTrace_append hprefix tailTrace_286997
  have hstable : (prefixWord ++ tailWord_286997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286997).length < 2 ^ (prefixWord ++ tailWord_286997).sum := by decide
  have hdescent : baseEnd_286997 < baseStart_286997 := by decide
  rcases family_descends (prefixWord ++ tailWord_286997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287029 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_287029 : Nat := 118140960795 + 287029 * 2 ^ 59
def prefixEnd_287029 : Nat := 4983230072969 + 3 ^ 40 * 287029 * 2
def baseEnd_287029 : Nat := 98255892519641820944989

theorem tailTrace_287029 : CollatzResearch.WordTrace tailWord_287029 prefixEnd_287029 98255892519641820944989 := by
  unfold tailWord_287029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468807677150428495576141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6979205118100285663717427 10468807677150428495576141)
  ·
    refine ⟨3925802878931410685841053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10468807677150428495576141 3925802878931410685841053)
    ·
      refine ⟨1472176079599279007190395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3925802878931410685841053 1472176079599279007190395)
      ·
        refine ⟨2208264119398918510785593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472176079599279007190395 2208264119398918510785593)
        ·
          refine ⟨1656198089549188883089195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208264119398918510785593 1656198089549188883089195)
          ·
            refine ⟨2484297134323783324633793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656198089549188883089195 2484297134323783324633793)
            ·
              refine ⟨1863222850742837493475345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484297134323783324633793 1863222850742837493475345)
              ·
                refine ⟨1397417138057128120106509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863222850742837493475345 1397417138057128120106509)
                ·
                  refine ⟨524031426771423045039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1397417138057128120106509 524031426771423045039941)
                  ·
                    refine ⟨98255892519641820944989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524031426771423045039941 98255892519641820944989)
                    ·
                      rfl

theorem cell22_287029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_287029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287029 prefixEnd_287029 := by exact prefixLift 287029
  have htrace : WordTrace (prefixWord ++ tailWord_287029) baseStart_287029 baseEnd_287029 := by
    simpa [prefixWord, tailWord_287029, baseEnd_287029] using wordTrace_append hprefix tailTrace_287029
  have hstable : (prefixWord ++ tailWord_287029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287029).length < 2 ^ (prefixWord ++ tailWord_287029).sum := by decide
  have hdescent : baseEnd_287029 < baseStart_287029 := by decide
  rcases family_descends (prefixWord ++ tailWord_287029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287033 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 5]
def baseStart_287033 : Nat := 118140960795 + 287033 * 2 ^ 59
def prefixEnd_287033 : Nat := 4983230072969 + 3 ^ 40 * 287033 * 2
def baseEnd_287033 : Nat := 32752420600462381281659

theorem tailTrace_287033 : CollatzResearch.WordTrace tailWord_287033 prefixEnd_287033 32752420600462381281659 := by
  unfold tailWord_287033
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468953569135937178721753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6979302379423958119147835 10468953569135937178721753)
  ·
    refine ⟨7851715176851952884041315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10468953569135937178721753 7851715176851952884041315)
    ·
      refine ⟨11777572765277929326061973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851715176851952884041315 11777572765277929326061973)
      ·
        refine ⟨552073723372402937159155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11777572765277929326061973 552073723372402937159155)
        ·
          refine ⟨828110585058604405738733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552073723372402937159155 828110585058604405738733)
          ·
            refine ⟨310541469396976652152025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 828110585058604405738733 310541469396976652152025)
            ·
              refine ⟨232906102047732489114019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310541469396976652152025 232906102047732489114019)
              ·
                refine ⟨349359153071598733671029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232906102047732489114019 349359153071598733671029)
                ·
                  refine ⟨32752420600462381281659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 349359153071598733671029 32752420600462381281659)
                  ·
                    rfl

theorem cell22_287033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_287033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287033 prefixEnd_287033 := by exact prefixLift 287033
  have htrace : WordTrace (prefixWord ++ tailWord_287033) baseStart_287033 baseEnd_287033 := by
    simpa [prefixWord, tailWord_287033, baseEnd_287033] using wordTrace_append hprefix tailTrace_287033
  have hstable : (prefixWord ++ tailWord_287033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287033).length < 2 ^ (prefixWord ++ tailWord_287033).sum := by decide
  have hdescent : baseEnd_287033 < baseStart_287033 := by decide
  rcases family_descends (prefixWord ++ tailWord_287033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287059 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 4, 3]
def baseStart_287059 : Nat := 118140960795 + 287059 * 2 ^ 59
def prefixEnd_287059 : Nat := 4983230072969 + 3 ^ 40 * 287059 * 2
def baseEnd_287059 : Nat := 98266162132731742694897

theorem tailTrace_287059 : CollatzResearch.WordTrace tailWord_287059 prefixEnd_287059 98266162132731742694897 := by
  unfold tailWord_287059
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469901867041743619168231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6979934578027829079445487 10469901867041743619168231)
  ·
    refine ⟨15704852800562615428752347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10469901867041743619168231 15704852800562615428752347)
    ·
      refine ⟨23557279200843923143128521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15704852800562615428752347 23557279200843923143128521)
      ·
        refine ⟨17667959400632942357346391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23557279200843923143128521 17667959400632942357346391)
        ·
          refine ⟨26501939100949413536019587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17667959400632942357346391 26501939100949413536019587)
          ·
            refine ⟨39752908651424120304029381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26501939100949413536019587 39752908651424120304029381)
            ·
              refine ⟨7453670372142022557005509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39752908651424120304029381 7453670372142022557005509)
              ·
                refine ⟨1397563194776629229438533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7453670372142022557005509 1397563194776629229438533)
                ·
                  refine ⟨262043099020617980519725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397563194776629229438533 262043099020617980519725)
                  ·
                    refine ⟨98266162132731742694897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262043099020617980519725 98266162132731742694897)
                    ·
                      rfl

theorem cell22_287059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].length) (baseStart_287059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287059 prefixEnd_287059 := by exact prefixLift 287059
  have htrace : WordTrace (prefixWord ++ tailWord_287059) baseStart_287059 baseEnd_287059 := by
    simpa [prefixWord, tailWord_287059, baseEnd_287059] using wordTrace_append hprefix tailTrace_287059
  have hstable : (prefixWord ++ tailWord_287059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287059).length < 2 ^ (prefixWord ++ tailWord_287059).sum := by decide
  have hdescent : baseEnd_287059 < baseStart_287059 := by decide
  rcases family_descends (prefixWord ++ tailWord_287059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287072 : List Nat := [2, 1, 1, 3, 15]
def baseStart_287072 : Nat := 118140960795 + 287072 * 2 ^ 59
def prefixEnd_287072 : Nat := 4983230072969 + 3 ^ 40 * 287072 * 2
def baseEnd_287072 : Nat := 404405811927588650699

theorem tailTrace_287072 : CollatzResearch.WordTrace tailWord_287072 prefixEnd_287072 404405811927588650699 := by
  unfold tailWord_287072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235188007997323419695735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6980250677329764559594313 5235188007997323419695735)
  ·
    refine ⟨7852782011995985129543603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235188007997323419695735 7852782011995985129543603)
    ·
      refine ⟨11779173017993977694315405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7852782011995985129543603 11779173017993977694315405)
      ·
        refine ⟨4417189881747741635368277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11779173017993977694315405 4417189881747741635368277)
        ·
          refine ⟨404405811927588650699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 4417189881747741635368277 404405811927588650699)
          ·
            rfl

theorem cell22_287072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 15].length) (baseStart_287072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287072 prefixEnd_287072 := by exact prefixLift 287072
  have htrace : WordTrace (prefixWord ++ tailWord_287072) baseStart_287072 baseEnd_287072 := by
    simpa [prefixWord, tailWord_287072, baseEnd_287072] using wordTrace_append hprefix tailTrace_287072
  have hstable : (prefixWord ++ tailWord_287072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287072).length < 2 ^ (prefixWord ++ tailWord_287072).sum := by decide
  have hdescent : baseEnd_287072 < baseStart_287072 := by decide
  rcases family_descends (prefixWord ++ tailWord_287072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287093 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_287093 : Nat := 118140960795 + 287093 * 2 ^ 59
def prefixEnd_287093 : Nat := 4983230072969 + 3 ^ 40 * 287093 * 2
def baseEnd_287093 : Nat := 98277801027566987344793

theorem tailTrace_287093 : CollatzResearch.WordTrace tailWord_287093 prefixEnd_287093 98277801027566987344793 := by
  unfold tailWord_287093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471141948918567425905933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6980761299279044950603955 10471141948918567425905933)
  ·
    refine ⟨3926678230844462784714725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10471141948918567425905933 3926678230844462784714725)
    ·
      refine ⟨736252168283336772134011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3926678230844462784714725 736252168283336772134011)
      ·
        refine ⟨1104378252425005158201017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736252168283336772134011 1104378252425005158201017)
        ·
          refine ⟨828283689318753868650763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104378252425005158201017 828283689318753868650763)
          ·
            refine ⟨1242425533978130802976145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828283689318753868650763 1242425533978130802976145)
            ·
              refine ⟨931819150483598102232109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242425533978130802976145 931819150483598102232109)
              ·
                refine ⟨349432181431349288337041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931819150483598102232109 349432181431349288337041)
                ·
                  refine ⟨262074136073511966252781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349432181431349288337041 262074136073511966252781)
                  ·
                    refine ⟨98277801027566987344793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262074136073511966252781 98277801027566987344793)
                    ·
                      rfl

theorem cell22_287093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_287093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287093 prefixEnd_287093 := by exact prefixLift 287093
  have htrace : WordTrace (prefixWord ++ tailWord_287093) baseStart_287093 baseEnd_287093 := by
    simpa [prefixWord, tailWord_287093, baseEnd_287093] using wordTrace_append hprefix tailTrace_287093
  have hstable : (prefixWord ++ tailWord_287093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287093).length < 2 ^ (prefixWord ++ tailWord_287093).sum := by decide
  have hdescent : baseEnd_287093 < baseStart_287093 := by decide
  rcases family_descends (prefixWord ++ tailWord_287093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287138 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_287138 : Nat := 118140960795 + 287138 * 2 ^ 59
def prefixEnd_287138 : Nat := 4983230072969 + 3 ^ 40 * 287138 * 2
def baseEnd_287138 : Nat := 98293205447201869969655

theorem tailTrace_287138 : CollatzResearch.WordTrace tailWord_287138 prefixEnd_287138 98293205447201869969655 := by
  unfold tailWord_287138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618195808438885027823517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6981855489170360074196045 2618195808438885027823517)
  ·
    refine ⟨981823428164581885433819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2618195808438885027823517 981823428164581885433819)
    ·
      refine ⟨1472735142246872828150729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981823428164581885433819 1472735142246872828150729)
      ·
        refine ⟨1104551356685154621113047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1472735142246872828150729 1104551356685154621113047)
        ·
          refine ⟨1656827035027731931669571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104551356685154621113047 1656827035027731931669571)
          ·
            refine ⟨2485240552541597897504357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656827035027731931669571 2485240552541597897504357)
            ·
              refine ⟨465982603601549605782067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2485240552541597897504357 465982603601549605782067)
              ·
                refine ⟨698973905402324408673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465982603601549605782067 698973905402324408673101)
                ·
                  refine ⟨262115214525871653252413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698973905402324408673101 262115214525871653252413)
                  ·
                    refine ⟨98293205447201869969655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262115214525871653252413 98293205447201869969655)
                    ·
                      rfl

theorem cell22_287138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_287138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287138 prefixEnd_287138 := by exact prefixLift 287138
  have htrace : WordTrace (prefixWord ++ tailWord_287138) baseStart_287138 baseEnd_287138 := by
    simpa [prefixWord, tailWord_287138, baseEnd_287138] using wordTrace_append hprefix tailTrace_287138
  have hstable : (prefixWord ++ tailWord_287138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287138).length < 2 ^ (prefixWord ++ tailWord_287138).sum := by decide
  have hdescent : baseEnd_287138 < baseStart_287138 := by decide
  rcases family_descends (prefixWord ++ tailWord_287138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287209 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_287209 : Nat := 118140960795 + 287209 * 2 ^ 59
def prefixEnd_287209 : Nat := 4983230072969 + 3 ^ 40 * 287209 * 2
def baseEnd_287209 : Nat := 98317510198181351444437

theorem tailTrace_287209 : CollatzResearch.WordTrace tailWord_287209 prefixEnd_287209 98317510198181351444437 := by
  unfold tailWord_287209
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475372816498319237128681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6983581877665546158085787 10475372816498319237128681)
  ·
    refine ⟨7856529612373739427846511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10475372816498319237128681 7856529612373739427846511)
    ·
      refine ⟨11784794418560609141769767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856529612373739427846511 11784794418560609141769767)
      ·
        refine ⟨17677191627840913712654651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784794418560609141769767 17677191627840913712654651)
        ·
          refine ⟨26515787441761370568981977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17677191627840913712654651 26515787441761370568981977)
          ·
            refine ⟨19886840581321027926736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26515787441761370568981977 19886840581321027926736483)
            ·
              refine ⟨29830260871981541890104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19886840581321027926736483 29830260871981541890104725)
              ·
                refine ⟨1398293478374134776098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29830260871981541890104725 1398293478374134776098659)
                ·
                  refine ⟨2097440217561202164147989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398293478374134776098659 2097440217561202164147989)
                  ·
                    refine ⟨98317510198181351444437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2097440217561202164147989 98317510198181351444437)
                    ·
                      rfl

theorem cell22_287209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_287209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287209 prefixEnd_287209 := by exact prefixLift 287209
  have htrace : WordTrace (prefixWord ++ tailWord_287209) baseStart_287209 baseEnd_287209 := by
    simpa [prefixWord, tailWord_287209, baseEnd_287209] using wordTrace_append hprefix tailTrace_287209
  have hstable : (prefixWord ++ tailWord_287209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287209).length < 2 ^ (prefixWord ++ tailWord_287209).sum := by decide
  have hdescent : baseEnd_287209 < baseStart_287209 := by decide
  rcases family_descends (prefixWord ++ tailWord_287209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287224 : List Nat := [2, 1, 2, 1, 1, 4, 1, 10]
def baseStart_287224 : Nat := 118140960795 + 287224 * 2 ^ 59
def prefixEnd_287224 : Nat := 4983230072969 + 3 ^ 40 * 287224 * 2
def baseEnd_287224 : Nat := 10924738333858479146599

theorem tailTrace_287224 : CollatzResearch.WordTrace tailWord_287224 prefixEnd_287224 10924738333858479146599 := by
  unfold tailWord_287224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237959955721988399462363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6983946607629317865949817 5237959955721988399462363)
  ·
    refine ⟨7856939933582982599193545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237959955721988399462363 7856939933582982599193545)
    ·
      refine ⟨5892704950187236949395159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7856939933582982599193545 5892704950187236949395159)
      ·
        refine ⟨8839057425280855424092739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5892704950187236949395159 8839057425280855424092739)
        ·
          refine ⟨13258586137921283136139109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8839057425280855424092739 13258586137921283136139109)
          ·
            refine ⟨2485984900860240588026083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13258586137921283136139109 2485984900860240588026083)
            ·
              refine ⟨3728977351290360882039125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485984900860240588026083 3728977351290360882039125)
              ·
                refine ⟨10924738333858479146599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3728977351290360882039125 10924738333858479146599)
                ·
                  rfl

theorem cell22_287224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_287224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287224 prefixEnd_287224 := by exact prefixLift 287224
  have htrace : WordTrace (prefixWord ++ tailWord_287224) baseStart_287224 baseEnd_287224 := by
    simpa [prefixWord, tailWord_287224, baseEnd_287224] using wordTrace_append hprefix tailTrace_287224
  have hstable : (prefixWord ++ tailWord_287224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287224).length < 2 ^ (prefixWord ++ tailWord_287224).sum := by decide
  have hdescent : baseEnd_287224 < baseStart_287224 := by decide
  rcases family_descends (prefixWord ++ tailWord_287224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287277 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_287277 : Nat := 118140960795 + 287277 * 2 ^ 59
def prefixEnd_287277 : Nat := 4983230072969 + 3 ^ 40 * 287277 * 2
def baseEnd_287277 : Nat := 98340787987851840744229

theorem tailTrace_287277 : CollatzResearch.WordTrace tailWord_287277 prefixEnd_287277 98340787987851840744229 := by
  unfold tailWord_287277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477852980251966850604085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6985235320167977900402723 10477852980251966850604085)
  ·
    refine ⟨982298716898621892244133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10477852980251966850604085 982298716898621892244133)
    ·
      refine ⟨184181009418491604795775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 982298716898621892244133 184181009418491604795775)
      ·
        refine ⟨276271514127737407193663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184181009418491604795775 276271514127737407193663)
        ·
          refine ⟨414407271191606110790495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276271514127737407193663 414407271191606110790495)
          ·
            refine ⟨621610906787409166185743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414407271191606110790495 621610906787409166185743)
            ·
              refine ⟨932416360181113749278615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621610906787409166185743 932416360181113749278615)
              ·
                refine ⟨1398624540271670623917923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932416360181113749278615 1398624540271670623917923)
                ·
                  refine ⟨2097936810407505935876885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398624540271670623917923 2097936810407505935876885)
                  ·
                    refine ⟨98340787987851840744229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2097936810407505935876885 98340787987851840744229)
                    ·
                      rfl

theorem cell22_287277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_287277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287277 prefixEnd_287277 := by exact prefixLift 287277
  have htrace : WordTrace (prefixWord ++ tailWord_287277) baseStart_287277 baseEnd_287277 := by
    simpa [prefixWord, tailWord_287277, baseEnd_287277] using wordTrace_append hprefix tailTrace_287277
  have hstable : (prefixWord ++ tailWord_287277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287277).length < 2 ^ (prefixWord ++ tailWord_287277).sum := by decide
  have hdescent : baseEnd_287277 < baseStart_287277 := by decide
  rcases family_descends (prefixWord ++ tailWord_287277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287290 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_287290 : Nat := 118140960795 + 287290 * 2 ^ 59
def prefixEnd_287290 : Nat := 4983230072969 + 3 ^ 40 * 287290 * 2
def baseEnd_287290 : Nat := 98345238153524140169189

theorem tailTrace_287290 : CollatzResearch.WordTrace tailWord_287290 prefixEnd_287290 98345238153524140169189 := by
  unfold tailWord_287290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619581782301217517706831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6985551419469913380551549 2619581782301217517706831)
  ·
    refine ⟨3929372673451826276560247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2619581782301217517706831 3929372673451826276560247)
    ·
      refine ⟨5894059010177739414840371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929372673451826276560247 5894059010177739414840371)
      ·
        refine ⟨8841088515266609122260557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894059010177739414840371 8841088515266609122260557)
        ·
          refine ⟨3315408193224978420847709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8841088515266609122260557 3315408193224978420847709)
          ·
            refine ⟨1243278072459366907817891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3315408193224978420847709 1243278072459366907817891)
            ·
              refine ⟨1864917108689050361726837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243278072459366907817891 1864917108689050361726837)
              ·
                refine ⟨174835978939598471411891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1864917108689050361726837 174835978939598471411891)
                ·
                  refine ⟨262253968409397707117837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174835978939598471411891 262253968409397707117837)
                  ·
                    refine ⟨98345238153524140169189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262253968409397707117837 98345238153524140169189)
                    ·
                      rfl

theorem cell22_287290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_287290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287290 prefixEnd_287290 := by exact prefixLift 287290
  have htrace : WordTrace (prefixWord ++ tailWord_287290) baseStart_287290 baseEnd_287290 := by
    simpa [prefixWord, tailWord_287290, baseEnd_287290] using wordTrace_append hprefix tailTrace_287290
  have hstable : (prefixWord ++ tailWord_287290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287290).length < 2 ^ (prefixWord ++ tailWord_287290).sum := by decide
  have hdescent : baseEnd_287290 < baseStart_287290 := by decide
  rcases family_descends (prefixWord ++ tailWord_287290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287301 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_287301 : Nat := 118140960795 + 287301 * 2 ^ 59
def prefixEnd_287301 : Nat := 4983230072969 + 3 ^ 40 * 287301 * 2
def baseEnd_287301 : Nat := 98349003678323778144155

theorem tailTrace_287301 : CollatzResearch.WordTrace tailWord_287301 prefixEnd_287301 98349003678323778144155 := by
  unfold tailWord_287301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478728332165018949477757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6985818888110012632985171 10478728332165018949477757)
  ·
    refine ⟨3929523124561882106054159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10478728332165018949477757 3929523124561882106054159)
    ·
      refine ⟨5894284686842823159081239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929523124561882106054159 5894284686842823159081239)
      ·
        refine ⟨8841427030264234738621859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894284686842823159081239 8841427030264234738621859)
        ·
          refine ⟨13262140545396352107932789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8841427030264234738621859 13262140545396352107932789)
          ·
            refine ⟨1243325676130908010118699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13262140545396352107932789 1243325676130908010118699)
            ·
              refine ⟨1864988514196362015178049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243325676130908010118699 1864988514196362015178049)
              ·
                refine ⟨1398741385647271511383537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864988514196362015178049 1398741385647271511383537)
                ·
                  refine ⟨1049056039235453633537653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1398741385647271511383537 1049056039235453633537653)
                  ·
                    refine ⟨98349003678323778144155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1049056039235453633537653 98349003678323778144155)
                    ·
                      rfl

theorem cell22_287301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_287301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287301 prefixEnd_287301 := by exact prefixLift 287301
  have htrace : WordTrace (prefixWord ++ tailWord_287301) baseStart_287301 baseEnd_287301 := by
    simpa [prefixWord, tailWord_287301, baseEnd_287301] using wordTrace_append hprefix tailTrace_287301
  have hstable : (prefixWord ++ tailWord_287301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287301).length < 2 ^ (prefixWord ++ tailWord_287301).sum := by decide
  have hdescent : baseEnd_287301 < baseStart_287301 := by decide
  rcases family_descends (prefixWord ++ tailWord_287301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287303 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 5]
def baseStart_287303 : Nat := 118140960795 + 287303 * 2 ^ 59
def prefixEnd_287303 : Nat := 4983230072969 + 3 ^ 40 * 287303 * 2
def baseEnd_287303 : Nat := 32783229439732146531383

theorem tailTrace_287303 : CollatzResearch.WordTrace tailWord_287303 prefixEnd_287303 32783229439732146531383 := by
  unfold tailWord_287303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478801278157773291050563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6985867518771848860700375 10478801278157773291050563)
  ·
    refine ⟨15718201917236659936575845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478801278157773291050563 15718201917236659936575845)
    ·
      refine ⟨2947162859481873738107971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15718201917236659936575845 2947162859481873738107971)
      ·
        refine ⟨4420744289222810607161957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947162859481873738107971 4420744289222810607161957)
        ·
          refine ⟨828889554229276988842867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4420744289222810607161957 828889554229276988842867)
          ·
            refine ⟨1243334331343915483264301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828889554229276988842867 1243334331343915483264301)
            ·
              refine ⟨466250374253968306224113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243334331343915483264301 466250374253968306224113)
              ·
                refine ⟨349687780690476229668085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466250374253968306224113 349687780690476229668085)
                ·
                  refine ⟨32783229439732146531383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 349687780690476229668085 32783229439732146531383)
                  ·
                    rfl

theorem cell22_287303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].length) (baseStart_287303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287303 prefixEnd_287303 := by exact prefixLift 287303
  have htrace : WordTrace (prefixWord ++ tailWord_287303) baseStart_287303 baseEnd_287303 := by
    simpa [prefixWord, tailWord_287303, baseEnd_287303] using wordTrace_append hprefix tailTrace_287303
  have hstable : (prefixWord ++ tailWord_287303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287303).length < 2 ^ (prefixWord ++ tailWord_287303).sum := by decide
  have hdescent : baseEnd_287303 < baseStart_287303 := by decide
  rcases family_descends (prefixWord ++ tailWord_287303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287326 : List Nat := [4, 4, 1, 2, 2, 1, 2, 6]
def baseStart_287326 : Nat := 118140960795 + 287326 * 2 ^ 59
def prefixEnd_287326 : Nat := 4983230072969 + 3 ^ 40 * 287326 * 2
def baseEnd_287326 : Nat := 10928617965470227363231

theorem tailTrace_287326 : CollatzResearch.WordTrace tailWord_287326 prefixEnd_287326 10928617965470227363231 := by
  unfold tailWord_287326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309955019634306027392229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6986426771382965479425221 1309955019634306027392229)
  ·
    refine ⟨245616566181432380136043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1309955019634306027392229 245616566181432380136043)
    ·
      refine ⟨368424849272148570204065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245616566181432380136043 368424849272148570204065)
      ·
        refine ⟨276318636954111427653049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368424849272148570204065 276318636954111427653049)
        ·
          refine ⟨207238977715583570739787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276318636954111427653049 207238977715583570739787)
          ·
            refine ⟨310858466573375356109681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207238977715583570739787 310858466573375356109681)
            ·
              refine ⟨233143849930031517082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310858466573375356109681 233143849930031517082261)
              ·
                refine ⟨10928617965470227363231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233143849930031517082261 10928617965470227363231)
                ·
                  rfl

theorem cell22_287326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_287326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287326 prefixEnd_287326 := by exact prefixLift 287326
  have htrace : WordTrace (prefixWord ++ tailWord_287326) baseStart_287326 baseEnd_287326 := by
    simpa [prefixWord, tailWord_287326, baseEnd_287326] using wordTrace_append hprefix tailTrace_287326
  have hstable : (prefixWord ++ tailWord_287326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287326).length < 2 ^ (prefixWord ++ tailWord_287326).sum := by decide
  have hdescent : baseEnd_287326 < baseStart_287326 := by decide
  rcases family_descends (prefixWord ++ tailWord_287326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287331 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 6]
def baseStart_287331 : Nat := 118140960795 + 287331 * 2 ^ 59
def prefixEnd_287331 : Nat := 4983230072969 + 3 ^ 40 * 287331 * 2
def baseEnd_287331 : Nat := 32786424430471233298021

theorem tailTrace_287331 : CollatzResearch.WordTrace tailWord_287331 prefixEnd_287331 32786424430471233298021 := by
  unfold tailWord_287331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479822522056334073069847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6986548348037556048713231 10479822522056334073069847)
  ·
    refine ⟨15719733783084501109604771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10479822522056334073069847 15719733783084501109604771)
    ·
      refine ⟨23579600674626751664407157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719733783084501109604771 23579600674626751664407157)
      ·
        refine ⟨2210587563246257968538171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23579600674626751664407157 2210587563246257968538171)
        ·
          refine ⟨3315881344869386952807257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210587563246257968538171 3315881344869386952807257)
          ·
            refine ⟨2486911008652040214605443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315881344869386952807257 2486911008652040214605443)
            ·
              refine ⟨3730366512978060321908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486911008652040214605443 3730366512978060321908165)
              ·
                refine ⟨699443721183386310357781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3730366512978060321908165 699443721183386310357781)
                ·
                  refine ⟨32786424430471233298021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 699443721183386310357781 32786424430471233298021)
                  ·
                    rfl

theorem cell22_287331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_287331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287331 prefixEnd_287331 := by exact prefixLift 287331
  have htrace : WordTrace (prefixWord ++ tailWord_287331) baseStart_287331 baseEnd_287331 := by
    simpa [prefixWord, tailWord_287331, baseEnd_287331] using wordTrace_append hprefix tailTrace_287331
  have hstable : (prefixWord ++ tailWord_287331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287331).length < 2 ^ (prefixWord ++ tailWord_287331).sum := by decide
  have hdescent : baseEnd_287331 < baseStart_287331 := by decide
  rcases family_descends (prefixWord ++ tailWord_287331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287363 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 4, 3]
def baseStart_287363 : Nat := 118140960795 + 287363 * 2 ^ 59
def prefixEnd_287363 : Nat := 4983230072969 + 3 ^ 40 * 287363 * 2
def baseEnd_287363 : Nat := 98370227545376283093965

theorem tailTrace_287363 : CollatzResearch.WordTrace tailWord_287363 prefixEnd_287363 98370227545376283093965 := by
  unfold tailWord_287363
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480989657940403538234743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6987326438626935692156495 10480989657940403538234743)
  ·
    refine ⟨15721484486910605307352115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10480989657940403538234743 15721484486910605307352115)
    ·
      refine ⟨23582226730365907961028173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15721484486910605307352115 23582226730365907961028173)
      ·
        refine ⟨8843335023887215485385565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23582226730365907961028173 8843335023887215485385565)
        ·
          refine ⟨3316250633957705807019587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8843335023887215485385565 3316250633957705807019587)
          ·
            refine ⟨4974375950936558710529381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316250633957705807019587 4974375950936558710529381)
            ·
              refine ⟨932695490800604758224259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4974375950936558710529381 932695490800604758224259)
              ·
                refine ⟨1399043236200907137336389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932695490800604758224259 1399043236200907137336389)
                ·
                  refine ⟨262320606787670088250573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399043236200907137336389 262320606787670088250573)
                  ·
                    refine ⟨98370227545376283093965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262320606787670088250573 98370227545376283093965)
                    ·
                      rfl

theorem cell22_287363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].length) (baseStart_287363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287363 prefixEnd_287363 := by exact prefixLift 287363
  have htrace : WordTrace (prefixWord ++ tailWord_287363) baseStart_287363 baseEnd_287363 := by
    simpa [prefixWord, tailWord_287363, baseEnd_287363] using wordTrace_append hprefix tailTrace_287363
  have hstable : (prefixWord ++ tailWord_287363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287363).length < 2 ^ (prefixWord ++ tailWord_287363).sum := by decide
  have hdescent : baseEnd_287363 < baseStart_287363 := by decide
  rcases family_descends (prefixWord ++ tailWord_287363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287442 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_287442 : Nat := 118140960795 + 287442 * 2 ^ 59
def prefixEnd_287442 : Nat := 4983230072969 + 3 ^ 40 * 287442 * 2
def baseEnd_287442 : Nat := 98397270859846410368723

theorem tailTrace_287442 : CollatzResearch.WordTrace tailWord_287442 prefixEnd_287442 98397270859846410368723 := by
  unfold tailWord_287442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620967756163550007590145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6989247349769466686907053 2620967756163550007590145)
  ·
    refine ⟨1965725817122662505692609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2620967756163550007590145 1965725817122662505692609)
    ·
      refine ⟨1474294362841996879269457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1965725817122662505692609 1474294362841996879269457)
      ·
        refine ⟨1105720772131497659452093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474294362841996879269457 1105720772131497659452093)
        ·
          refine ⟨414645289549311622294535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1105720772131497659452093 414645289549311622294535)
          ·
            refine ⟨621967934323967433441803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414645289549311622294535 621967934323967433441803)
            ·
              refine ⟨932951901485951150162705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621967934323967433441803 932951901485951150162705)
              ·
                refine ⟨699713926114463362622029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932951901485951150162705 699713926114463362622029)
                ·
                  refine ⟨262392722292923760983261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699713926114463362622029 262392722292923760983261)
                  ·
                    refine ⟨98397270859846410368723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262392722292923760983261 98397270859846410368723)
                    ·
                      rfl

theorem cell22_287442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_287442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287442 prefixEnd_287442 := by exact prefixLift 287442
  have htrace : WordTrace (prefixWord ++ tailWord_287442) baseStart_287442 baseEnd_287442 := by
    simpa [prefixWord, tailWord_287442, baseEnd_287442] using wordTrace_append hprefix tailTrace_287442
  have hstable : (prefixWord ++ tailWord_287442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287442).length < 2 ^ (prefixWord ++ tailWord_287442).sum := by decide
  have hdescent : baseEnd_287442 < baseStart_287442 := by decide
  rcases family_descends (prefixWord ++ tailWord_287442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_287451 : Nat := 118140960795 + 287451 * 2 ^ 59
def prefixEnd_287451 : Nat := 4983230072969 + 3 ^ 40 * 287451 * 2
def baseEnd_287451 : Nat := 98400351743773386893695

theorem tailTrace_287451 : CollatzResearch.WordTrace tailWord_287451 prefixEnd_287451 98400351743773386893695 := by
  unfold tailWord_287451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484199281621594567438207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6989466187747729711625471 10484199281621594567438207)
  ·
    refine ⟨15726298922432391851157311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10484199281621594567438207 15726298922432391851157311)
    ·
      refine ⟨23589448383648587776735967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15726298922432391851157311 23589448383648587776735967)
      ·
        refine ⟨35384172575472881665103951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23589448383648587776735967 35384172575472881665103951)
        ·
          refine ⟨53076258863209322497655927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35384172575472881665103951 53076258863209322497655927)
          ·
            refine ⟨79614388294813983746483891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53076258863209322497655927 79614388294813983746483891)
            ·
              refine ⟨119421582442220975619725837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79614388294813983746483891 119421582442220975619725837)
              ·
                refine ⟨44783093415832865857397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119421582442220975619725837 44783093415832865857397189)
                ·
                  refine ⟨8396830015468662348261973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44783093415832865857397189 8396830015468662348261973)
                  ·
                    refine ⟨98400351743773386893695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8396830015468662348261973 98400351743773386893695)
                    ·
                      rfl

theorem cell22_287451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_287451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287451 prefixEnd_287451 := by exact prefixLift 287451
  have htrace : WordTrace (prefixWord ++ tailWord_287451) baseStart_287451 baseEnd_287451 := by
    simpa [prefixWord, tailWord_287451, baseEnd_287451] using wordTrace_append hprefix tailTrace_287451
  have hstable : (prefixWord ++ tailWord_287451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287451).length < 2 ^ (prefixWord ++ tailWord_287451).sum := by decide
  have hdescent : baseEnd_287451 < baseStart_287451 := by decide
  rcases family_descends (prefixWord ++ tailWord_287451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287459 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 1, 3]
def baseStart_287459 : Nat := 118140960795 + 287459 * 2 ^ 59
def prefixEnd_287459 : Nat := 4983230072969 + 3 ^ 40 * 287459 * 2
def baseEnd_287459 : Nat := 98403090307264032693671

theorem tailTrace_287459 : CollatzResearch.WordTrace tailWord_287459 prefixEnd_287459 98403090307264032693671 := by
  unfold tailWord_287459
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484491065592611933729431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6989660710395074622486287 10484491065592611933729431)
  ·
    refine ⟨15726736598388917900594147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10484491065592611933729431 15726736598388917900594147)
    ·
      refine ⟨23590104897583376850891221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15726736598388917900594147 23590104897583376850891221)
      ·
        refine ⟨552893083537110394942763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23590104897583376850891221 552893083537110394942763)
        ·
          refine ⟨829339625305665592414145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552893083537110394942763 829339625305665592414145)
          ·
            refine ⟨622004718979249194310609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829339625305665592414145 622004718979249194310609)
            ·
              refine ⟨466503539234436895732957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622004718979249194310609 466503539234436895732957)
              ·
                refine ⟨174938827212913835899859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466503539234436895732957 174938827212913835899859)
                ·
                  refine ⟨262408240819370753849789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174938827212913835899859 262408240819370753849789)
                  ·
                    refine ⟨98403090307264032693671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262408240819370753849789 98403090307264032693671)
                    ·
                      rfl

theorem cell22_287459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 3].length) (baseStart_287459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287459 prefixEnd_287459 := by exact prefixLift 287459
  have htrace : WordTrace (prefixWord ++ tailWord_287459) baseStart_287459 baseEnd_287459 := by
    simpa [prefixWord, tailWord_287459, baseEnd_287459] using wordTrace_append hprefix tailTrace_287459
  have hstable : (prefixWord ++ tailWord_287459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287459).length < 2 ^ (prefixWord ++ tailWord_287459).sum := by decide
  have hdescent : baseEnd_287459 < baseStart_287459 := by decide
  rcases family_descends (prefixWord ++ tailWord_287459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287476 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_287476 : Nat := 118140960795 + 287476 * 2 ^ 59
def prefixEnd_287476 : Nat := 4983230072969 + 3 ^ 40 * 287476 * 2
def baseEnd_287476 : Nat := 98408909754681655018619

theorem tailTrace_287476 : CollatzResearch.WordTrace tailWord_287476 prefixEnd_287476 98408909754681655018619 := by
  unfold tailWord_287476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242555553265511918549141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6990074071020682558065521 5242555553265511918549141)
  ·
    refine ⟨245744791559320871181991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5242555553265511918549141 245744791559320871181991)
    ·
      refine ⟨368617187338981306772987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245744791559320871181991 368617187338981306772987)
      ·
        refine ⟨552925781008471960159481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368617187338981306772987 552925781008471960159481)
        ·
          refine ⟨414694335756353970119611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552925781008471960159481 414694335756353970119611)
          ·
            refine ⟨622041503634530955179417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414694335756353970119611 622041503634530955179417)
            ·
              refine ⟨466531127725898216384563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622041503634530955179417 466531127725898216384563)
              ·
                refine ⟨699796691588847324576845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466531127725898216384563 699796691588847324576845)
                ·
                  refine ⟨262423759345817746716317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699796691588847324576845 262423759345817746716317)
                  ·
                    refine ⟨98408909754681655018619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262423759345817746716317 98408909754681655018619)
                    ·
                      rfl

theorem cell22_287476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_287476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287476 prefixEnd_287476 := by exact prefixLift 287476
  have htrace : WordTrace (prefixWord ++ tailWord_287476) baseStart_287476 baseEnd_287476 := by
    simpa [prefixWord, tailWord_287476, baseEnd_287476] using wordTrace_append hprefix tailTrace_287476
  have hstable : (prefixWord ++ tailWord_287476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287476).length < 2 ^ (prefixWord ++ tailWord_287476).sum := by decide
  have hdescent : baseEnd_287476 < baseStart_287476 := by decide
  rcases family_descends (prefixWord ++ tailWord_287476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287549 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_287549 : Nat := 118140960795 + 287549 * 2 ^ 59
def prefixEnd_287549 : Nat := 4983230072969 + 3 ^ 40 * 287549 * 2
def baseEnd_287549 : Nat := 98433899146533797943395

theorem tailTrace_287549 : CollatzResearch.WordTrace tailWord_287549 prefixEnd_287549 98433899146533797943395 := by
  unfold tailWord_287549
  simp only [CollatzResearch.WordTrace]
  refine ⟨10487773635266557304505701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6991849090177704869670467 10487773635266557304505701)
  ·
    refine ⟨1966457556612479494594819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10487773635266557304505701 1966457556612479494594819)
    ·
      refine ⟨2949686334918719241892229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966457556612479494594819 2949686334918719241892229)
      ·
        refine ⟨553066187797259857854793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2949686334918719241892229 553066187797259857854793)
        ·
          refine ⟨414799640847944893391095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553066187797259857854793 414799640847944893391095)
          ·
            refine ⟨622199461271917340086643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414799640847944893391095 622199461271917340086643)
            ·
              refine ⟨933299191907876010129965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622199461271917340086643 933299191907876010129965)
              ·
                refine ⟨349987196965453503798737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933299191907876010129965 349987196965453503798737)
                ·
                  refine ⟨262490397724090127849053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349987196965453503798737 262490397724090127849053)
                  ·
                    refine ⟨98433899146533797943395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262490397724090127849053 98433899146533797943395)
                    ·
                      rfl

theorem cell22_287549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_287549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_287549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_287549 prefixEnd_287549 := by exact prefixLift 287549
  have htrace : WordTrace (prefixWord ++ tailWord_287549) baseStart_287549 baseEnd_287549 := by
    simpa [prefixWord, tailWord_287549, baseEnd_287549] using wordTrace_append hprefix tailTrace_287549
  have hstable : (prefixWord ++ tailWord_287549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287549).length < 2 ^ (prefixWord ++ tailWord_287549).sum := by decide
  have hdescent : baseEnd_287549 < baseStart_287549 := by decide
  rcases family_descends (prefixWord ++ tailWord_287549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
